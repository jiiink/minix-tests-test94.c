/* Tests for BPF devices (LWIP) - by D.C. van Moolenbroek */
/* This test needs to be run as root: opening BPF devices is root-only. */
/*
 * We do not attempt to test the BPF filter code here.  Such a test is better
 * done through standardized tests and with direct use of the filter code.
 * The current BPF filter implementation has been run through the FreeBSD
 * BPF filter regression tests (from their tools/regression/bpf/bpf_filter), of
 * which only the last test (0084 - "Check very long BPF program") failed due
 * to our lower and strictly enforced BPF_MAXINSNS value.  Future modifications
 * of the BPF filter code should be tested against at least that test set.
 */
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/sysctl.h>
#include <sys/wait.h>
#include <net/bpf.h>
#include <net/bpfdesc.h>
#include <net/if.h>
#include <net/if_types.h>
#include <net/if_ether.h>
#include <net/if_dl.h>
#include <netinet/in.h>
#include <netinet/ip.h>
#include <netinet/ip6.h>
#include <netinet/udp.h>
#include <ifaddrs.h>
#include <unistd.h>
#include <fcntl.h>
#include <limits.h>
#include <paths.h>
#include <pwd.h>

#include "common.h"

#define ITERATIONS	2

#define LOOPBACK_IFNAME	"lo0"

#define TEST_PORT_A	12345
#define TEST_PORT_B	12346

#define SLEEP_TIME	250000	/* (us) - increases may require code changes */

#define NONROOT_USER	"bin"	/* name of any unprivileged user */

#ifdef NO_INET6
const struct in6_addr in6addr_loopback = IN6ADDR_LOOPBACK_INIT;
#endif /* NO_INET6 */

static unsigned int got_signal;

/*
 * Signal handler.
 */
static void
test94_signal(int sig)
{
    if (sig != SIGUSR1) {
        e(0);
    }
    
    got_signal++;
}

/*
 * Send UDP packets on the given socket 'fd' so as to fill up a BPF store
 * buffer of size 'size' exactly.  The provided buffer 'buf' may be used for
 * packet generation and is at least of 'size' bytes.  Return the number of
 * packets sent.
 */
static uint32_t
test94_fill_exact(int fd, uint8_t * buf, size_t size, uint32_t seq)
{
	size_t hdrlen, len;

	if (buf == NULL || fd < 0) {
		return seq;
	}

	hdrlen = BPF_WORDALIGN(sizeof(struct bpf_hdr)) + sizeof(struct ip) +
	    sizeof(struct udphdr) + sizeof(seq);

	for (len = 16; len <= hdrlen; len <<= 1) {
		if (len > SIZE_MAX / 2) {
			return seq;
		}
	}
	
	if (len > size) {
		return seq;
	}

	hdrlen = BPF_WORDALIGN(hdrlen - sizeof(seq));

	while (size > 0) {
		size_t write_len = len - hdrlen;
		
		if (write_len > size) {
			write_len = size;
		}
		
		memset(buf, 'Y', write_len);
		
		if (write_len > sizeof(seq)) {
			buf[sizeof(seq)] = 'X';
		}
		
		if (write_len > 0) {
			buf[write_len - 1] = 'Z';
		}
		
		memcpy(buf, &seq, (write_len < sizeof(seq)) ? write_len : sizeof(seq));

		ssize_t written = write(fd, buf, write_len);
		if (written != (ssize_t)write_len || written < 0) {
			return seq;
		}

		size -= write_len;
		seq++;
	}

	return seq;
}

/*
 * Send UDP packets on the given socket 'fd' so as to fill up at least a BPF
 * store buffer of size 'size', with at least one more packet being sent.  The
 * provided buffer 'buf' may be used for packet generation and is at least of
 * 'size' bytes.
 */
static void
test94_fill_random(int fd, uint8_t * buf, size_t size)
{
	size_t hdrlen, len, data_len;
	ssize_t left;
	uint32_t seq;
	ssize_t write_result;

	hdrlen = BPF_WORDALIGN(BPF_WORDALIGN(sizeof(struct bpf_hdr)) +
	    sizeof(struct ip) + sizeof(struct udphdr));

	for (left = (ssize_t)size, seq = 1; left >= 0; seq++) {
		len = hdrlen + sizeof(seq) + lrand48() % (size / 10);
		data_len = len - hdrlen;

		if (data_len > 0) {
			memset(buf, 'Y', data_len);
			if (data_len > sizeof(seq))
				buf[sizeof(seq)] = 'X';
			buf[data_len - 1] = 'Z';
		}
		memcpy(buf, &seq, sizeof(seq));

		write_result = write(fd, buf, data_len);
		if (write_result != (ssize_t)data_len) e(0);

		left -= BPF_WORDALIGN(len);
	}
}

/*
 * Send a UDP packet with a specific size of 'size' bytes and sequence number
 * 'seq' on socket 'fd', using 'buf' as scratch buffer.
 */
static void
test94_add_specific(int fd, uint8_t * buf, size_t size, uint32_t seq)
{
    if (buf == NULL || fd < 0) {
        e(0);
        return;
    }

    size_t total_size = size + sizeof(seq);
    if (total_size < size) {
        e(0);
        return;
    }

    memset(buf, 'Y', total_size);
    if (total_size > sizeof(seq))
        buf[sizeof(seq)] = 'X';
    buf[total_size - 1] = 'Z';
    memcpy(buf, &seq, sizeof(seq));

    ssize_t bytes_written = write(fd, buf, total_size);
    if (bytes_written != (ssize_t)total_size) {
        e(0);
        return;
    }
}

/*
 * Send a randomly sized, relatively small UDP packet on the given socket 'fd',
 * using sequence number 'seq'.  The buffer 'buf' may be used as scratch buffer
 * which is at most 'size' bytes--the same size as the total BPF buffer.
 */
static void
test94_add_random(int fd, uint8_t * buf, size_t size, uint32_t seq)
{
    if (size < 10) {
        return;
    }
    
    size_t random_size = (size_t)(lrand48() % (size / 10));
    test94_add_specific(fd, buf, random_size, seq);
}

/*
 * Check whether the packet in 'buf' of 'caplen' captured bytes out of
 * 'datalen' data bytes is one we sent.  If so, return an offset to the packet
 * data.  If not, return a negative value.
 */
static ssize_t
test94_check_pkt(uint8_t * buf, ssize_t caplen, ssize_t datalen)
{
	struct ip ip;
	struct udphdr uh;
	ssize_t ip_size = sizeof(ip);
	ssize_t udp_size = sizeof(uh);
	ssize_t total_header_size = ip_size + udp_size;

	if (caplen < ip_size)
		return -1;

	memcpy(&ip, buf, ip_size);

	if (ip.ip_v != IPVERSION)
		return -1;
	if (ip.ip_hl != (ip_size >> 2))
		return -1;
	if (ip.ip_p != IPPROTO_UDP)
		return -1;

	if (caplen < total_header_size)
		return -1;

	memcpy(&uh, buf + ip_size, udp_size);

	if (uh.uh_sport != htons(TEST_PORT_A))
		return -1;
	if (uh.uh_dport != htons(TEST_PORT_B))
		return -1;

	if (datalen - ip_size != ntohs(uh.uh_ulen))
		e(0);

	return total_header_size;
}

/*
 * Check whether the capture in 'buf' of 'len' bytes looks like a valid set of
 * captured packets.  The valid packets start from sequence number 'seq'; the
 * next expected sequence number is returned.  If 'filtered' is set, there
 * should be no other packets in the capture; otherwise, other packets are
 * ignored.
 */
static uint32_t
test94_check(uint8_t * buf, ssize_t len, uint32_t seq, int filtered,
	uint32_t * caplen, uint32_t * datalen)
{
	struct bpf_hdr bh;
	ssize_t off;
	uint32_t nseq;
	ssize_t aligned_hdr_size;
	ssize_t aligned_cap_size;

	if (buf == NULL || len < 0) {
		e(0);
		return seq;
	}

	while (len > 0) {
		if (len < BPF_WORDALIGN(sizeof(bh))) {
			e(0);
			break;
		}

		memcpy(&bh, buf, sizeof(bh));

		if (bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) {
			e(0);
			break;
		}

		if (caplen != NULL) {
			if (bh.bh_caplen != *caplen || bh.bh_datalen != *datalen) {
				e(0);
				break;
			}
			caplen++;
			datalen++;
		} else {
			if (bh.bh_datalen != bh.bh_caplen) {
				e(0);
				break;
			}
		}

		if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh))) {
			e(0);
			break;
		}

		aligned_hdr_size = bh.bh_hdrlen;
		aligned_cap_size = BPF_WORDALIGN(bh.bh_caplen);

		if (aligned_hdr_size + aligned_cap_size > len) {
			e(0);
			break;
		}

		buf += aligned_hdr_size;
		len -= aligned_hdr_size;

		off = test94_check_pkt(buf, bh.bh_caplen, bh.bh_datalen);
		if (off < 0) {
			if (filtered) {
				e(0);
				break;
			}
			buf += aligned_cap_size;
			len -= aligned_cap_size;
			continue;
		}

		if (bh.bh_caplen < off + sizeof(seq)) {
			e(0);
			break;
		}

		memcpy(&nseq, &buf[off], sizeof(nseq));

		if (nseq != seq) {
			e(0);
			break;
		}
		seq++;

		off += sizeof(seq);

		if (off < bh.bh_caplen && off < bh.bh_datalen - 1 && buf[off] == 'X') {
			for (off++; off < bh.bh_caplen && off < bh.bh_datalen - 1; off++) {
				if (buf[off] != 'Y') {
					e(0);
					break;
				}
			}
		}

		if (off < bh.bh_caplen && off == bh.bh_datalen - 1 && buf[off] != 'Z') {
			e(0);
			break;
		}

		buf += aligned_cap_size;
		len -= aligned_cap_size;
	}

	return seq;
}

/*
 * Filter program to ensure that the given (datalink-headerless) packet is an
 * IPv4 UDP packet from port 12345 to port 12346.  Important: the 'k' value of
 * the last instruction must be the accepted packet size, and is modified by
 * some of the tests further down!
 */
static struct bpf_insn test94_filter[] = {
	{ BPF_LD+BPF_B+BPF_ABS, 0, 0, 0 },	/* is this an IPv4 header? */
	{ BPF_ALU+BPF_RSH+BPF_K, 0, 0, 4 },
	{ BPF_JMP+BPF_JEQ+BPF_K, 0, 7, 4 },
	{ BPF_LD+BPF_B+BPF_ABS, 0, 0, 9 },	/* is this a UDP packet? */
	{ BPF_JMP+BPF_JEQ+BPF_K, 0, 5, IPPROTO_UDP },
	{ BPF_LDX+BPF_B+BPF_MSH, 0, 0, 0 },
	{ BPF_LD+BPF_H+BPF_IND, 0, 0, 0 },	/* source port 12345? */
	{ BPF_JMP+BPF_JEQ+BPF_K, 0, 2, TEST_PORT_A },
	{ BPF_LD+BPF_H+BPF_IND, 0, 0, 2 },	/* destination port 12346? */
	{ BPF_JMP+BPF_JEQ+BPF_K, 1, 0, TEST_PORT_B },
	{ BPF_RET+BPF_K, 0, 0, 0 },		/* reject the packet */
	{ BPF_RET+BPF_K, 0, 0, (uint32_t)-1 },	/* accept the (whole) packet */
};

/*
 * Set up a BPF device, a pair of sockets of which traffic will be captured on
 * the BPF device, a buffer for capturing packets, and optionally a filter.
 * If the given size is non-zero, use that as buffer size.  Return the BPF
 * device's actual buffer size, which is also the size of 'buf'.
 */
static size_t
test94_setup(int * fd, int * fd2, int * fd3, uint8_t ** buf, unsigned int size,
	int set_filter)
{
	struct sockaddr_in sinA, sinB;
	struct ifreq ifr;
	struct bpf_program bf;
	unsigned int dlt;

	*fd = open(_PATH_BPF, O_RDWR);
	if (*fd < 0) e(0);

	if (size != 0) {
		if (ioctl(*fd, BIOCSBLEN, &size) != 0) e(0);
	}

	if (ioctl(*fd, BIOCGBLEN, &size) != 0) e(0);
	if (size < 1024 || size > BPF_MAXBUFSIZE) e(0);

	*buf = malloc(size);
	if (*buf == NULL) e(0);

	if (set_filter) {
		memset(&bf, 0, sizeof(bf));
		bf.bf_len = __arraycount(test94_filter);
		bf.bf_insns = test94_filter;
		if (ioctl(*fd, BIOCSETF, &bf) != 0) e(0);
	}

	memset(&ifr, 0, sizeof(ifr));
	strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
	if (ioctl(*fd, BIOCSETIF, &ifr) != 0) e(0);

	if (ioctl(*fd, BIOCGDLT, &dlt) != 0) e(0);
	if (dlt != DLT_RAW) e(0);

	*fd2 = socket(AF_INET, SOCK_DGRAM, 0);
	if (*fd2 < 0) e(0);

	memset(&sinA, 0, sizeof(sinA));
	sinA.sin_family = AF_INET;
	sinA.sin_port = htons(TEST_PORT_A);
	sinA.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	if (bind(*fd2, (struct sockaddr *)&sinA, sizeof(sinA)) != 0) e(0);

	memcpy(&sinB, &sinA, sizeof(sinB));
	sinB.sin_port = htons(TEST_PORT_B);
	if (connect(*fd2, (struct sockaddr *)&sinB, sizeof(sinB)) != 0) e(0);

	*fd3 = socket(AF_INET, SOCK_DGRAM, 0);
	if (*fd3 < 0) e(0);

	if (bind(*fd3, (struct sockaddr *)&sinB, sizeof(sinB)) != 0) e(0);

	if (connect(*fd3, (struct sockaddr *)&sinA, sizeof(sinA)) != 0) e(0);

	return size;
}

/*
 * Clean up resources allocated by test94_setup().
 */
static void
test94_cleanup(int fd, int fd2, int fd3, uint8_t * buf)
{
    if (fd3 >= 0 && close(fd3) != 0) e(0);
    if (fd2 >= 0 && close(fd2) != 0) e(0);
    if (fd >= 0 && close(fd) != 0) e(0);
    free(buf);
}

/*
 * Test reading packets from a BPF device, using regular mode.
 */
static void
test94a(void)
{
	struct bpf_program bf;
	struct timeval tv;
	fd_set fds;
	uint8_t *buf;
	pid_t pid;
	size_t size;
	ssize_t len;
	uint32_t seq;
	int fd, fd2, fd3, status, bytes, fl;

	subtest = 1;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 0);

	pid = fork();
	if (pid == -1) {
		e(0);
		return;
	}
	
	if (pid == 0) {
		errct = 0;
		usleep(SLEEP_TIME);
		test94_fill_random(fd2, buf, size);
		exit(errct);
	}

	len = read(fd, buf, size);

	if (len < size * 3/4) e(0);
	if (len > size) e(0);
	test94_check(buf, len, 1, 0, NULL, NULL);

	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	if (read(fd, buf, size - 1) != -1) e(0);
	if (errno != EINVAL) e(0);
	if (read(fd, buf, size + 1) != -1) e(0);
	if (errno != EINVAL) e(0);
	if (read(fd, buf, sizeof(struct bpf_hdr)) != -1) e(0);
	if (errno != EINVAL) e(0);

	memset(&bf, 0, sizeof(bf));
	bf.bf_len = __arraycount(test94_filter);
	bf.bf_insns = test94_filter;
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = 0;
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv) != 0) e(0);
	if (FD_ISSET(fd, &fds)) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);
	if (bytes != 0) e(0);

	pid = fork();
	if (pid == -1) {
		e(0);
		return;
	}
	
	if (pid == 0) {
		errct = 0;
		usleep(SLEEP_TIME);
		test94_fill_random(fd2, buf, size);
		exit(errct);
	}

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);

	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);

	len = read(fd, buf, size);

	if (len < size * 3/4) e(0);
	if (len > size) e(0);
	seq = test94_check(buf, len, 1, 1, NULL, NULL);

	if (len != bytes) e(0);

	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = 0;
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv) != 0) e(0);
	if (FD_ISSET(fd, &fds)) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);
	if (bytes != 0) e(0);

	got_signal = 0;

	pid = fork();
	if (pid == -1) {
		e(0);
		return;
	}
	
	if (pid == 0) {
		errct = 0;
		signal(SIGUSR1, test94_signal);
		usleep(SLEEP_TIME);
		test94_add_random(fd2, buf, size, seq + 1);
		usleep(SLEEP_TIME);
		if (got_signal != 0) e(0);
		pause();
		if (got_signal != 1) e(0);
		exit(errct);
	}

	tv.tv_sec = 0;
	tv.tv_usec = SLEEP_TIME * 3;
	if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= size * 3/4) e(0);
	if (test94_check(buf, len, seq, 1, NULL, NULL) != seq + 2) e(0);

	if (kill(pid, SIGUSR1) != 0) e(0);

	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = SLEEP_TIME;
	if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	if (read(fd, buf, size) != -1) e(0);
	if (errno != EAGAIN) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = 0;
	if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	pid = fork();
	if (pid == -1) {
		e(0);
		return;
	}
	
	if (pid == 0) {
		errct = 0;
		signal(SIGUSR1, test94_signal);
		if (read(fd, buf, size) != -1) e(0);
		if (errno != EINTR) e(0);
		if (got_signal != 1) e(0);
		exit(errct);
	}

	usleep(SLEEP_TIME * 2);

	if (kill(pid, SIGUSR1) != 0) e(0);

	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	pid = fork();
	if (pid == -1) {
		e(0);
		return;
	}
	
	if (pid == 0) {
		errct = 0;
		signal(SIGUSR1, test94_signal);
		if (read(fd, buf, size) != -1) e(0);
		if (errno != EINTR) e(0);
		if (got_signal != 1) e(0);
		exit(errct);
	}

	usleep(SLEEP_TIME);

	test94_add_random(fd2, buf, size, 2);

	usleep(SLEEP_TIME);

	if (kill(pid, SIGUSR1) != 0) e(0);

	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	if ((fl = fcntl(fd, F_GETFL)) == -1) e(0);
	if (fcntl(fd, F_SETFL, fl | O_NONBLOCK) != 0) e(0);

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= size * 3/4) e(0);
	seq = test94_check(buf, len, 2, 1, NULL, NULL);

	if (read(fd, buf, size) != -1) e(0);
	if (errno != EAGAIN) e(0);

	test94_fill_random(fd2, buf, size);

	len = read(fd, buf, size);
	if (len < size * 3/4) e(0);
	if (len > size) e(0);
	seq = test94_check(buf, len, 1, 1, NULL, NULL);

	len = read(fd, buf, size);

	if (len <= 0) e(0);
	if (len >= size * 3/4) e(0);
	if (test94_check(buf, len, seq, 1, NULL, NULL) != seq + 1) e(0);

	if (fcntl(fd, F_SETFL, fl) != 0) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = SLEEP_TIME * 2;
	if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	pid = fork();
	if (pid == -1) {
		e(0);
		return;
	}
	
	if (pid == 0) {
		errct = 0;
		usleep(SLEEP_TIME);
		test94_add_random(fd2, buf, size, 1);
		exit(errct);
	}

	tv.tv_sec = 1;
	tv.tv_usec = 0;
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv) != 0) e(0);

	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test reading packets from a BPF device, using immediate mode.
 */
static void
test94b(void)
{
	struct timeval tv;
	fd_set fds;
	uint8_t *buf;
	unsigned int val;
	size_t size;
	ssize_t len;
	uint32_t seq;
	pid_t pid;
	int fd, fd2, fd3, bytes, status, fl;

	subtest = 2;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);
	if (size == 0) {
		return;
	}

	val = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &val) != 0) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = 0;
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv) != 0) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);
	if (bytes != 0) e(0);

	test94_fill_random(fd2, buf, size);

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);

	len = read(fd, buf, size);
	if (len < (ssize_t)(size * 3 / 4)) e(0);
	if (len > (ssize_t)size) e(0);
	seq = test94_check(buf, len, 1, 1, NULL, NULL);

	if (len != bytes) e(0);

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)(size * 3 / 4)) e(0);
	if (test94_check(buf, len, seq, 1, NULL, NULL) != seq + 1) e(0);

	if (len != bytes) e(0);

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv) != 0) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);
	if (bytes != 0) e(0);

	test94_add_random(fd2, buf, size, seq + 1);
	test94_add_random(fd2, buf, size, seq + 2);

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)(size * 3 / 4)) e(0);
	if (test94_check(buf, len, seq + 1, 1, NULL, NULL) != seq + 3) e(0);

	if (len != bytes) e(0);

	pid = fork();
	if (pid == 0) {
		errct = 0;
		usleep(SLEEP_TIME);
		test94_add_random(fd2, buf, size, seq + 3);
		exit(errct);
	} else if (pid == -1) {
		e(0);
	}

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)(size * 3 / 4)) e(0);
	if (test94_check(buf, len, seq + 3, 1, NULL, NULL) != seq + 4) e(0);

	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	pid = fork();
	if (pid == 0) {
		errct = 0;
		usleep(SLEEP_TIME);
		test94_add_random(fd2, buf, size, seq + 4);
		exit(errct);
	} else if (pid == -1) {
		e(0);
	}

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);

	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)(size * 3 / 4)) e(0);
	if (test94_check(buf, len, seq + 4, 1, NULL, NULL) != seq + 5) e(0);

	if (len != bytes) e(0);

	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	fl = fcntl(fd, F_GETFL);
	if (fl == -1) e(0);
	if (fcntl(fd, F_SETFL, fl | O_NONBLOCK) != 0) e(0);

	if (read(fd, buf, size) != -1) e(0);
	if (errno != EAGAIN) e(0);

	test94_fill_random(fd2, buf, size);

	len = read(fd, buf, size);
	if (len < (ssize_t)(size * 3 / 4)) e(0);
	if (len > (ssize_t)size) e(0);
	seq = test94_check(buf, len, 1, 1, NULL, NULL);

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)(size * 3 / 4)) e(0);
	if (test94_check(buf, len, seq, 1, NULL, NULL) != seq + 1) e(0);

	if (fcntl(fd, F_SETFL, fl) != 0) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = SLEEP_TIME;
	if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	if (read(fd, buf, size) != -1) e(0);
	if (errno != EAGAIN) e(0);

	test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test reading packets from a BPF device, with an exactly filled buffer.  The
 * idea is that normally the store buffer is considered "full" if the next
 * packet does not fit in it, but if no more bytes are left in it, it can be
 * rotated immediately.  This is a practically useless edge case, but we
 * support it, so we might as well test it.  Also, some of the code for this
 * case is shared with other rare cases that we cannot test here (interfaces
 * disappearing, to be specific), and exactly filling up the buffers does test
 * some other bounds checks so all that might make this worth it anyway.  While
 * we are exercising full control over our buffers, also check statistics.
 */
static void
test94c(void)
{
	struct bpf_stat bs;
	fd_set fds;
	uint8_t *buf;
	size_t size;
	pid_t pid;
	uint32_t count, seq;
	int fd, fd2, fd3, bytes, status, fl;

	subtest = 3;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != 0) e(0);
	if (bs.bs_drop != 0) e(0);

	count = test94_fill_exact(fd2, buf, size, 0);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != count) e(0);
	if (bs.bs_recv < bs.bs_capt) e(0);
	if (bs.bs_drop != 0) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);
	if (bytes != size) e(0);

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);

	if (read(fd, buf, size) != size) e(0);
	test94_check(buf, size, 0, 1, NULL, NULL);

	seq = test94_fill_exact(fd2, buf, size, 1);
	test94_fill_exact(fd2, buf, size, seq);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != count * 3) e(0);
	if (bs.bs_recv < bs.bs_capt) e(0);
	if (bs.bs_drop != 0) e(0);

	test94_add_random(fd2, buf, size, 0);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != count * 3 + 1) e(0);
	if (bs.bs_recv < bs.bs_capt) e(0);
	if (bs.bs_drop != 1) e(0);

	test94_add_random(fd2, buf, size, 0);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != count * 3 + 2) e(0);
	if (bs.bs_recv < bs.bs_capt) e(0);
	if (bs.bs_drop != 2) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);
	if (bytes != size) e(0);

	if (read(fd, buf, size) != size) e(0);
	if (test94_check(buf, size, 1, 1, NULL, NULL) != seq) e(0);

	if (read(fd, buf, size) != size) e(0);
	if (test94_check(buf, size, seq, 1, NULL, NULL) != count * 2 + 1) e(0);

	pid = fork();
	if (pid == 0) {
		errct = 0;
		usleep(SLEEP_TIME);
		test94_fill_exact(fd2, buf, size, 1);
		exit(errct);
	} else if (pid == -1) {
		e(0);
	}

	if (read(fd, buf, size) != size) e(0);
	test94_check(buf, size, 1, 1, NULL, NULL);

	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	pid = fork();
	if (pid == 0) {
		errct = 0;
		usleep(SLEEP_TIME);
		test94_fill_exact(fd2, buf, size, seq);
		exit(errct);
	} else if (pid == -1) {
		e(0);
	}

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);

	if ((fl = fcntl(fd, F_GETFL)) == -1) e(0);
	if (fcntl(fd, F_SETFL, fl | O_NONBLOCK) != 0) e(0);

	if (read(fd, buf, size) != size) e(0);
	test94_check(buf, size, seq, 1, NULL, NULL);

	if (read(fd, buf, size) != -1) e(0);
	if (errno != EAGAIN) e(0);

	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != count * 5 + 2) e(0);
	if (bs.bs_recv < bs.bs_capt) e(0);
	if (bs.bs_drop != 2) e(0);

	test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test receipt of large packets on BPF devices.  Large packets should be
 * truncated to the size of the buffer, but unless the filter specifies a
 * smaller capture size, no more than that.
 */
static void
test94d(void)
{
    struct bpf_hdr bh;
    uint8_t *buf, *buf2;
    size_t size;
    ssize_t len;
    int fd, fd2, fd3, datalen;
    const size_t BUFFER_SIZE = 32768;
    const int LARGE_PACKET_SIZE = 65000;

    subtest = 4;

    size = test94_setup(&fd, &fd2, &fd3, &buf, BUFFER_SIZE, 1);
    if (size != BUFFER_SIZE) e(0);

    datalen = LARGE_PACKET_SIZE;
    if (setsockopt(fd2, SOL_SOCKET, SO_SNDBUF, &datalen, sizeof(datalen)) != 0) 
        e(0);

    buf2 = malloc(datalen);
    if (buf2 == NULL) e(0);

    memset(buf2, 'Y', datalen);
    buf2[0] = 'X';
    buf2[size - sizeof(struct udphdr) - sizeof(struct ip) - 
         BPF_WORDALIGN(sizeof(bh)) - 1] = 'Z';

    if (write(fd2, buf2, datalen) != datalen) {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }

    if (read(fd, buf, size) != (ssize_t)size) {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }

    memcpy(&bh, buf, sizeof(bh));

    if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh))) {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }
    
    if (bh.bh_caplen != size - BPF_WORDALIGN(sizeof(bh))) {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }
    
    if (bh.bh_datalen != sizeof(struct ip) + sizeof(struct udphdr) + datalen) {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }

    size_t packet_start = BPF_WORDALIGN(sizeof(bh)) + sizeof(struct ip) + sizeof(struct udphdr);
    
    if (buf[packet_start] != 'X') {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }
    
    if (buf[size - 2] != 'Y') {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }
    
    if (buf[size - 1] != 'Z') {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }

    test94_add_random(fd2, buf, size, 1);

    if (write(fd2, buf2, datalen) != datalen) {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }

    len = read(fd, buf, size);
    if (len <= 0) {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }
    
    if (len >= (ssize_t)(size * 3 / 4)) {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }
    
    if (test94_check(buf, len, 1, 1, NULL, NULL) != 2) {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }

    if (read(fd, buf, size) != (ssize_t)size) {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }

    memcpy(&bh, buf, sizeof(bh));

    if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh))) {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }
    
    if (bh.bh_caplen != size - BPF_WORDALIGN(sizeof(bh))) {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }
    
    if (bh.bh_datalen != sizeof(struct ip) + sizeof(struct udphdr) + datalen) {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }

    if (buf[packet_start] != 'X') {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }
    
    if (buf[size - 2] != 'Y') {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }
    
    if (buf[size - 1] != 'Z') {
        free(buf2);
        test94_cleanup(fd, fd2, fd3, buf);
        e(0);
    }

    free(buf2);
    test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test whether our filter is active through two-way communication and a
 * subsequent check on the BPF statistics.  We do not actually look through the
 * captured packets, because who knows what else is active on the loopback
 * device (e.g., X11) and the extra code specifically to extract our packets in
 * the other direction is simply not worth it.
 */
static void
test94_comm(int fd, int fd2, int fd3, int filtered)
{
	struct bpf_stat bs;
	char c;
	ssize_t result;

	result = write(fd2, "A", 1);
	if (result != 1) e(0);

	result = read(fd3, &c, 1);
	if (result != 1) e(0);
	if (c != 'A') e(0);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_recv == 0) e(0);
	if (bs.bs_capt == 0) e(0);

	if (ioctl(fd, BIOCFLUSH) != 0) e(0);

	result = write(fd3, "B", 1);
	if (result != 1) e(0);

	result = read(fd2, &c, 1);
	if (result != 1) e(0);
	if (c != 'B') e(0);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_recv == 0) e(0);

	if (filtered) {
		if (bs.bs_capt != 0) e(0);
		if (bs.bs_drop != 0) e(0);
	} else {
		if (bs.bs_capt == 0) e(0);
	}

	if (ioctl(fd, BIOCFLUSH) != 0) e(0);
}

/*
 * Test filter installation and mechanics.
 */
static void
test94e(void)
{
	struct bpf_program bf;
	struct bpf_stat bs;
	struct bpf_hdr bh;
	uint8_t *buf;
	size_t size, len, plen, alen, off;
	uint32_t seq, caplen[4], datalen[4];
	int i, fd, fd2, fd3, val;

	subtest = 5;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 0);

	val = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &val) != 0) e(0);

	memset(&bf, 0, sizeof(bf));
	bf.bf_len = BPF_MAXINSNS + 1;
	bf.bf_insns = NULL;
	if (ioctl(fd, BIOCSETF, &bf) != -1) e(0);
	if (errno != EINVAL) e(0);

	memset(&bf, 0, sizeof(bf));
	bf.bf_len = __arraycount(test94_filter) - 1;
	bf.bf_insns = test94_filter;
	if (ioctl(fd, BIOCSETF, &bf) != -1) e(0);
	if (errno != EINVAL) e(0);

	test94_comm(fd, fd2, fd3, 0);

	bf.bf_len++;
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);

	test94_comm(fd, fd2, fd3, 1);

	memset(&bf, 0, sizeof(bf));
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);

	test94_comm(fd, fd2, fd3, 0);

	memset(&bf, 0, sizeof(bf));
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);

	test94_comm(fd, fd2, fd3, 0);

	plen = sizeof(struct ip) + sizeof(struct udphdr) + sizeof(seq);
	if (BPF_WORDALIGN(plen) != plen) e(0);
	alen = BPF_WORDALIGN(plen + 1);
	if (alen - 2 <= plen + 1) e(0);

	test94_filter[__arraycount(test94_filter) - 1].k = alen;

	memset(&bf, 0, sizeof(bf));
	bf.bf_len = __arraycount(test94_filter);
	bf.bf_insns = test94_filter;
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);

	test94_comm(fd, fd2, fd3, 1);

	test94_add_specific(fd2, buf, alen + 1 - plen, 1);
	caplen[0] = alen;
	datalen[0] = alen + 1;

	test94_add_specific(fd2, buf, alen - plen, 2);
	caplen[1] = alen;
	datalen[1] = alen;

	test94_add_specific(fd2, buf, alen + 3 - plen, 3);
	caplen[2] = alen;
	datalen[2] = alen + 3;

	test94_add_specific(fd2, buf, alen - 1 - plen, 4);
	caplen[3] = alen - 1;
	datalen[3] = alen - 1;

	memset(buf, 0, size);

	len = read(fd, buf, size);

	if (test94_check(buf, len, 1, 1, caplen, datalen) != 5) e(0);

	test94_filter[__arraycount(test94_filter) - 1].k = alen + 1;
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);

	test94_add_specific(fd2, buf, alen + 2 - plen, 5);
	caplen[0] = alen + 1;
	datalen[0] = alen + 2;

	test94_add_specific(fd2, buf, alen + 1 - plen, 6);
	caplen[1] = alen + 1;
	datalen[1] = alen + 1;

	test94_add_specific(fd2, buf, alen + 9 - plen, 7);
	caplen[2] = alen + 1;
	datalen[2] = alen + 9;

	test94_add_specific(fd2, buf, alen - plen, 8);
	caplen[3] = alen;
	datalen[3] = alen;

	memset(buf, 0, size);

	len = read(fd, buf, size);

	if (test94_check(buf, len, 5, 1, caplen, datalen) != 9) e(0);

	test94_filter[__arraycount(test94_filter) - 1].k = 1;
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);

	test94_add_random(fd2, buf, size, 9);
	test94_add_random(fd2, buf, size, 10);
	test94_add_random(fd2, buf, size, 11);

	memset(buf, 0, size);

	len = read(fd, buf, size);
	if (len <= 0) e(0);

	off = 0;
	for (i = 0; i < 3; i++) {
		if (len - off < sizeof(bh)) e(0);
		memcpy(&bh, &buf[off], sizeof(bh));

		if (bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0)
			e(0);
		if (bh.bh_caplen != 1) e(0);
		if (bh.bh_datalen < plen) e(0);
		if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh))) e(0);

		off += bh.bh_hdrlen;

		if (buf[off] != 0x45) e(0);

		off += BPF_WORDALIGN(bh.bh_caplen);
	}
	if (off != len) e(0);

	test94_filter[__arraycount(test94_filter) - 1].k = 0;
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);

	test94_add_random(fd2, buf, size, 12);
	test94_add_random(fd2, buf, size, 13);
	test94_add_random(fd2, buf, size, 14);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_recv < 3) e(0);
	if (bs.bs_capt != 0) e(0);
	if (bs.bs_drop != 0) e(0);

	test94_filter[__arraycount(test94_filter) - 1].k = (uint32_t)-1;

	test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Compute an IP checksum.
 */
static uint16_t
test94_cksum(uint8_t * buf, size_t len)
{
	uint32_t sum = 0;
	uint16_t word;

	if (buf == NULL) {
		return 0;
	}

	while (len > 1) {
		word = ((uint16_t)buf[0] << 8) | buf[1];
		sum += word;
		buf += 2;
		len -= 2;
	}

	if (len == 1) {
		word = (uint16_t)buf[0] << 8;
		sum += word;
	}

	while (sum >> 16) {
		sum = (sum & 0xFFFF) + (sum >> 16);
	}

	return (uint16_t)~sum;
}

/*
 * Set up UDP headers for a packet.  The packet uses IPv4 unless 'v6' is set,
 * in which case IPv6 is used.  The given buffer must be large enough to
 * contain the headers and the (to be appended) data.  The function returns the
 * offset into the buffer to the data portion of the packet.
 */
static size_t
test94_make_pkt(uint8_t *buf, size_t len, int v6)
{
    struct ip ip;
    struct ip6_hdr ip6;
    struct udphdr uh;
    size_t off;

    if (!v6) {
        memset(&ip, 0, sizeof(ip));
        ip.ip_v = IPVERSION;
        ip.ip_hl = sizeof(ip) >> 2;
        ip.ip_len = htons((uint16_t)(sizeof(ip) + sizeof(uh) + len));
        ip.ip_ttl = 255;
        ip.ip_p = IPPROTO_UDP;
        ip.ip_sum = 0;
        ip.ip_src.s_addr = htonl(INADDR_LOOPBACK);
        ip.ip_dst.s_addr = htonl(INADDR_LOOPBACK);

        memcpy(buf, &ip, sizeof(ip));
        ip.ip_sum = htons(test94_cksum(buf, sizeof(ip)));
        memcpy(buf, &ip, sizeof(ip));
        if (test94_cksum(buf, sizeof(ip)) != 0) {
            e(0);
        }

        off = sizeof(ip);
    } else {
        memset(&ip6, 0, sizeof(ip6));
        ip6.ip6_vfc = IPV6_VERSION;
        ip6.ip6_plen = htons((uint16_t)(sizeof(uh) + len));
        ip6.ip6_nxt = IPPROTO_UDP;
        ip6.ip6_hlim = 255;
        memcpy(&ip6.ip6_src, &in6addr_loopback, sizeof(ip6.ip6_src));
        memcpy(&ip6.ip6_dst, &in6addr_loopback, sizeof(ip6.ip6_dst));

        memcpy(buf, &ip6, sizeof(ip6));

        off = sizeof(ip6);
    }

    memset(&uh, 0, sizeof(uh));
    uh.uh_sport = htons(TEST_PORT_A);
    uh.uh_dport = htons(TEST_PORT_B);
    uh.uh_ulen = htons((uint16_t)(sizeof(uh) + len));
    uh.uh_sum = 0;

    memcpy(buf + off, &uh, sizeof(uh));

    return off + sizeof(uh);
}

/*
 * Test sending packets by writing to a BPF device.
 */
static void
test94f(void)
{
	struct bpf_stat bs;
	struct ifreq ifr;
	fd_set fds;
	uint8_t *buf = NULL;
	size_t off;
	unsigned int i, uval, mtu;
	int fd = -1, fd2 = -1, fd3 = -1;

	subtest = 6;

	if (test94_setup(&fd, &fd2, &fd3, &buf, 0, 1) != 0) {
		e(0);
		return;
	}

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, NULL, &fds, NULL, NULL) != 1) {
		e(0);
		goto cleanup;
	}
	if (!FD_ISSET(fd, &fds)) {
		e(0);
		goto cleanup;
	}

	memset(&ifr, 0, sizeof(ifr));
	strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));

	if (ioctl(fd2, SIOCGIFMTU, &ifr) != 0) {
		e(0);
		goto cleanup;
	}
	mtu = ifr.ifr_mtu;

	uint8_t *new_buf = realloc(buf, UINT16_MAX + 1);
	if (new_buf == NULL) {
		e(0);
		goto cleanup;
	}
	buf = new_buf;

	memset(buf, 0, UINT16_MAX + 1);

	for (i = UINT16_MAX + 1; i > mtu; i--) {
		if (write(fd, buf, i) != -1) {
			e(0);
			goto cleanup;
		}
		if (errno != EMSGSIZE) {
			e(0);
			goto cleanup;
		}
	}

	if (write(fd, buf, mtu) != (ssize_t)mtu) {
		e(0);
		goto cleanup;
	}

	if (write(fd, buf, 0) != 0) {
		e(0);
		goto cleanup;
	}

	off = test94_make_pkt(buf, 6, 0);
	memcpy(buf + off, "Hello!", 6);

	if (write(fd, buf, off + 6) != (ssize_t)(off + 6)) {
		e(0);
		goto cleanup;
	}

	memset(buf, 0, mtu);
	if (read(fd3, buf, mtu) != 6) {
		e(0);
		goto cleanup;
	}
	if (memcmp(buf, "Hello!", 6) != 0) {
		e(0);
		goto cleanup;
	}

	uval = 1;
	if (ioctl(fd, BIOCSFEEDBACK, &uval) != 0) {
		e(0);
		goto cleanup;
	}

	off = test94_make_pkt(buf, 12345, 0);
	for (i = 0; i < 12345; i++)
		buf[off + i] = 1 + (i % 251);

	if (write(fd, buf, off + 12345) != (ssize_t)(off + 12345)) {
		e(0);
		goto cleanup;
	}

	memset(buf, 0, UINT16_MAX);
	if (recv(fd3, buf, UINT16_MAX, 0) != 12345) {
		e(0);
		goto cleanup;
	}
	for (i = 0; i < 12345; i++) {
		if (buf[i] != 1 + (i % 251)) {
			e(0);
			goto cleanup;
		}
	}

	memset(buf, 0, UINT16_MAX);
	if (recv(fd3, buf, UINT16_MAX, MSG_DONTWAIT) != 12345) {
		e(0);
		goto cleanup;
	}
	for (i = 0; i < 12345; i++) {
		if (buf[i] != 1 + (i % 251)) {
			e(0);
			goto cleanup;
		}
	}

	if (recv(fd3, buf, UINT16_MAX, MSG_DONTWAIT) != -1) {
		e(0);
		goto cleanup;
	}
	if (errno != EWOULDBLOCK) {
		e(0);
		goto cleanup;
	}

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) {
		e(0);
		goto cleanup;
	}
	if (bs.bs_capt != 2) {
		e(0);
		goto cleanup;
	}

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, NULL, &fds, NULL, NULL) != 1) {
		e(0);
		goto cleanup;
	}
	if (!FD_ISSET(fd, &fds)) {
		e(0);
		goto cleanup;
	}

cleanup:
	test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test read, write, and select operations on unconfigured devices.
 */
static void
test94g(void)
{
	fd_set rfds, wfds;
	uint8_t *buf = NULL;
	unsigned int size;
	int fd = -1;

	subtest = 7;

	fd = open(_PATH_BPF, O_RDWR);
	if (fd < 0) {
		e(0);
		return;
	}

	if (ioctl(fd, BIOCGBLEN, &size) != 0) {
		e(0);
		goto cleanup;
	}
	
	if (size < 1024 || size > BPF_MAXBUFSIZE) {
		e(0);
		goto cleanup;
	}

	buf = malloc(size);
	if (buf == NULL) {
		e(0);
		goto cleanup;
	}

	if (read(fd, buf, size) != -1) {
		e(0);
		goto cleanup;
	}
	if (errno != EINVAL) {
		e(0);
		goto cleanup;
	}

	if (write(fd, buf, size) != -1) {
		e(0);
		goto cleanup;
	}
	if (errno != EINVAL) {
		e(0);
		goto cleanup;
	}

	FD_ZERO(&rfds);
	FD_SET(fd, &rfds);
	FD_ZERO(&wfds);
	FD_SET(fd, &wfds);

	if (select(fd + 1, &rfds, &wfds, NULL, NULL) != 2) {
		e(0);
		goto cleanup;
	}

	if (!FD_ISSET(fd, &rfds)) {
		e(0);
		goto cleanup;
	}
	if (!FD_ISSET(fd, &wfds)) {
		e(0);
		goto cleanup;
	}

cleanup:
	if (buf != NULL) {
		free(buf);
	}
	if (fd >= 0) {
		close(fd);
	}
}

/*
 * Test various IOCTL calls.  Several of these tests are rather superficial,
 * because we would need a real interface, rather than the loopback device, to
 * test their functionality properly.  Also note that we skip various checks
 * performed as part of the earlier subtests.
 */
static void
test94h(void)
{
	struct bpf_stat bs;
	struct bpf_version bv;
	struct bpf_dltlist bfl;
	struct ifreq ifr;
	struct timeval tv;
	uint8_t *buf;
	size_t size;
	unsigned int uval, list[2];
	int cfd, ufd, fd2, fd3, val;

	subtest = 8;

	size = test94_setup(&cfd, &fd2, &fd3, &buf, 0, 1);

	ufd = open(_PATH_BPF, O_RDWR);
	if (ufd < 0) e(0);

	test_buffer_length_operations(ufd, cfd, size);
	test_flush_operations(cfd, fd2, buf, size, ufd);
	test_device_operations(ufd, cfd);
	test_interface_operations(ufd, cfd);
	test_immediate_mode(cfd, fd2, buf, size, ufd);
	test_version_operation(ufd);
	test_header_complete_operations(ufd);
	test_data_link_operations(ufd, cfd);
	test_data_link_list_operations(ufd, cfd, list);
	test_see_sent_operations(ufd, cfd, fd2, buf, size);
	test_timeout_operations(ufd);
	test_feedback_operations(ufd);

	if (close(ufd) != 0) e(0);
	test94_cleanup(cfd, fd2, fd3, buf);
}

static void test_buffer_length_operations(int ufd, int cfd, size_t expected_size)
{
	unsigned int uval;

	uval = 1;
	if (ioctl(ufd, BIOCSBLEN, &uval) != 0) e(0);
	if (ioctl(ufd, BIOCGBLEN, &uval) != 0) e(0);
	if (uval < sizeof(struct bpf_hdr) || uval > BPF_MAXBUFSIZE) e(0);

	uval = (unsigned int)-1;
	if (ioctl(ufd, BIOCSBLEN, &uval) != 0) e(0);
	if (ioctl(ufd, BIOCGBLEN, &uval) != 0) e(0);
	if (uval < sizeof(struct bpf_hdr) || uval > BPF_MAXBUFSIZE) e(0);

	uval = 0;
	if (ioctl(ufd, BIOCSBLEN, &uval) != 0) e(0);
	if (ioctl(ufd, BIOCGBLEN, &uval) != 0) e(0);
	if (uval < sizeof(struct bpf_hdr) || uval > BPF_MAXBUFSIZE) e(0);

	uval = 1024;
	if (ioctl(ufd, BIOCSBLEN, &uval) != 0) e(0);
	if (ioctl(ufd, BIOCGBLEN, &uval) != 0) e(0);
	if (uval != 1024) e(0);

	if (ioctl(cfd, BIOCSBLEN, &uval) != -1) e(0);
	if (errno != EINVAL) e(0);

	if (ioctl(cfd, BIOCGBLEN, &uval) != 0) e(0);
	if (uval != expected_size) e(0);
}

static void test_flush_operations(int cfd, int fd2, uint8_t *buf, size_t size, int ufd)
{
	struct bpf_stat bs;
	unsigned int uval;
	int val;

	uval = 1;
	if (ioctl(cfd, BIOCIMMEDIATE, &uval) != 0) e(0);

	test94_fill_exact(fd2, buf, size, 1);
	test94_fill_exact(fd2, buf, size, 1);
	test94_fill_exact(fd2, buf, size, 1);

	if (ioctl(cfd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_recv == 0) e(0);
	if (bs.bs_drop == 0) e(0);
	if (bs.bs_capt == 0) e(0);

	if (ioctl(cfd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_recv == 0) e(0);
	if (bs.bs_drop == 0) e(0);
	if (bs.bs_capt == 0) e(0);

	if (ioctl(cfd, FIONREAD, &val) != 0) e(0);
	if (val == 0) e(0);

	if (ioctl(cfd, BIOCFLUSH) != 0) e(0);

	if (ioctl(cfd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_drop != 0) e(0);
	if (bs.bs_capt != 0) e(0);

	if (ioctl(cfd, FIONREAD, &val) != 0) e(0);
	if (val != 0) e(0);

	if (ioctl(ufd, BIOCFLUSH) != 0) e(0);

	if (ioctl(ufd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_recv != 0) e(0);
	if (bs.bs_drop != 0) e(0);
	if (bs.bs_capt != 0) e(0);
}

static void test_device_operations(int ufd, int cfd)
{
	unsigned int uval;

	if (ioctl(ufd, BIOCPROMISC) != -1) e(0);
	if (errno != EINVAL) e(0);

	if (ioctl(cfd, BIOCPROMISC) != 0) e(0);

	if (ioctl(ufd, BIOCGDLT, &uval) != -1) e(0);
	if (errno != EINVAL) e(0);
}

static void test_interface_operations(int ufd, int cfd)
{
	struct ifreq ifr;

	if (ioctl(ufd, BIOCGETIF, &ifr) != -1) e(0);
	if (errno != EINVAL) e(0);

	memset(&ifr, 'X', sizeof(ifr));
	if (ioctl(cfd, BIOCGETIF, &ifr) != 0) e(0);
	if (strcmp(ifr.ifr_name, LOOPBACK_IFNAME) != 0) e(0);

	memset(&ifr, 0, sizeof(ifr));
	strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
	if (ioctl(cfd, BIOCSETIF, &ifr) != -1) e(0);
	if (errno != EINVAL) e(0);

	memset(&ifr, 0, sizeof(ifr));
	memset(ifr.ifr_name, 'x', sizeof(ifr.ifr_name));
	if (ioctl(ufd, BIOCSETIF, &ifr) != -1) e(0);
	if (errno != ENXIO) e(0);

	memset(&ifr, 0, sizeof(ifr));
	strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
	ifr.ifr_name[strlen(ifr.ifr_name) - 1] += 9;
	if (ioctl(ufd, BIOCSETIF, &ifr) != -1) e(0);
	if (errno != ENXIO) e(0);
}

static void test_immediate_mode(int cfd, int fd2, uint8_t *buf, size_t size, int ufd)
{
	unsigned int uval;
	int val;

	test94_add_random(fd2, buf, size, 1);

	if (ioctl(cfd, FIONREAD, &val) != 0) e(0);
	if (val == 0) e(0);

	uval = 0;
	if (ioctl(cfd, BIOCIMMEDIATE, &uval) != 0) e(0);

	if (ioctl(cfd, FIONREAD, &val) != 0) e(0);
	if (val != 0) e(0);

	uval = 1;
	if (ioctl(cfd, BIOCIMMEDIATE, &uval) != 0) e(0);

	if (ioctl(cfd, FIONREAD, &val) != 0) e(0);
	if (val == 0) e(0);

	if (ioctl(cfd, BIOCFLUSH) != 0) e(0);

	uval = 1;
	if (ioctl(ufd, BIOCIMMEDIATE, &uval) != 0) e(0);

	uval = 0;
	if (ioctl(ufd, BIOCIMMEDIATE, &uval) != 0) e(0);
}

static void test_version_operation(int ufd)
{
	struct bpf_version bv;

	if (ioctl(ufd, BIOCVERSION, &bv) != 0) e(0);
	if (bv.bv_major != BPF_MAJOR_VERSION) e(0);
	if (bv.bv_minor != BPF_MINOR_VERSION) e(0);
}

static void test_header_complete_operations(int ufd)
{
	unsigned int uval;

	uval = 1;
	if (ioctl(ufd, BIOCGHDRCMPLT, &uval) != 0) e(0);
	if (uval != 0) e(0);

	uval = 2;
	if (ioctl(ufd, BIOCSHDRCMPLT, &uval) != 0) e(0);

	if (ioctl(ufd, BIOCGHDRCMPLT, &uval) != 0) e(0);
	if (uval != 1) e(0);

	uval = 0;
	if (ioctl(ufd, BIOCSHDRCMPLT, &uval) != 0) e(0);

	uval = 1;
	if (ioctl(ufd, BIOCGHDRCMPLT, &uval) != 0) e(0);
	if (uval != 0) e(0);
}

static void test_data_link_operations(int ufd, int cfd)
{
	unsigned int uval;

	uval = DLT_RAW;
	if (ioctl(ufd, BIOCSDLT, &uval) != -1) e(0);
	if (errno != EINVAL) e(0);

	uval = DLT_RAW;
	if (ioctl(cfd, BIOCSDLT, &uval) != 0) e(0);

	uval = DLT_NULL;
	if (ioctl(cfd, BIOCSDLT, &uval) != -1) e(0);
	if (errno != EINVAL) e(0);

	if (ioctl(cfd, BIOCGDLT, &uval) != 0) e(0);
	if (uval != DLT_RAW) e(0);
}

static void test_data_link_list_operations(int ufd, int cfd, unsigned int *list)
{
	struct bpf_dltlist bfl;

	memset(&bfl, 0, sizeof(bfl));
	if (ioctl(ufd, BIOCGDLTLIST, &bfl) != -1) e(0);
	if (errno != EINVAL) e(0);

	memset(&bfl, 0, sizeof(bfl));
	if (ioctl(cfd, BIOCGDLTLIST, &bfl) != 0) e(0);
	if (bfl.bfl_len != 1) e(0);
	if (bfl.bfl_list != NULL) e(0);

	memset(&bfl, 0, sizeof(bfl));
	bfl.bfl_len = 2;
	if (ioctl(cfd, BIOCGDLTLIST, &bfl) != 0) e(0);
	if (bfl.bfl_len != 1) e(0);
	if (bfl.bfl_list != NULL) e(0);

	memset(&bfl, 0, sizeof(bfl));
	memset(list, 0, 2 * sizeof(unsigned int));
	bfl.bfl_list = list;
	if (ioctl(cfd, BIOCGDLTLIST, &bfl) != -1) e(0);
	if (errno != ENOMEM) e(0);
	if (list[0] != 0) e(0);

	memset(&bfl, 0, sizeof(bfl));
	bfl.bfl_len = 1;
	bfl.bfl_list = list;
	if (ioctl(cfd, BIOCGDLTLIST, &bfl) != 0) e(0);
	if (bfl.bfl_len != 1) e(0);
	if (bfl.bfl_list != list) e(0);
	if (list[0] != DLT_RAW) e(0);
	if (list[1] != 0) e(0);

	memset(&bfl, 0, sizeof(bfl));
	memset(list, 0, 2 * sizeof(unsigned int));
	bfl.bfl_len = 2;
	bfl.bfl_list = list;
	if (ioctl(cfd, BIOCGDLTLIST, &bfl) != 0) e(0);
	if (bfl.bfl_len != 1) e(0);
	if (bfl.bfl_list != list) e(0);
	if (list[0] != DLT_RAW) e(0);
	if (list[1] != 0) e(0);
}

static void test_see_sent_operations(int ufd, int cfd, int fd2, uint8_t *buf, size_t size)
{
	struct bpf_stat bs;
	unsigned int uval;

	uval = 0;
	if (ioctl(ufd, BIOCGSEESENT, &uval) != 0) e(0);
	if (uval != 1) e(0);

	uval = 0;
	if (ioctl(ufd, BIOCSSEESENT, &uval) != 0) e(0);

	uval = 1;
	if (ioctl(ufd, BIOCGSEESENT, &uval) != 0) e(0);
	if (uval != 0) e(0);

	uval = 2;
	if (ioctl(ufd, BIOCSSEESENT, &uval) != 0) e(0);

	if (ioctl(ufd, BIOCGSEESENT, &uval) != 0) e(0);
	if (uval != 1) e(0);

	if (ioctl(cfd, BIOCGSEESENT, &uval) != 0) e(0);
	if (uval != 1) e(0);

	uval = 0;
	if (ioctl(cfd, BIOCSSEESENT, &uval) != 0) e(0);

	if (ioctl(cfd, BIOCFLUSH) != 0) e(0);

	test94_add_random(fd2, buf, size, 1);

	if (ioctl(cfd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_recv != 0) e(0);

	uval = 1;
	if (ioctl(cfd, BIOCSSEESENT, &uval) != 0) e(0);

	if (ioctl(cfd, BIOCFLUSH) != 0) e(0);

	test94_add_random(fd2, buf, size, 1);

	if (ioctl(cfd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_recv == 0) e(0);
}

static void test_timeout_operations(int ufd)
{
	struct timeval tv;

	tv.tv_sec = 99;
	if (ioctl(ufd, BIOCGRTIMEOUT, &tv) != 0) e(0);
	if (tv.tv_sec != 0) e(0);
	if (tv.tv_usec != 0) e(0);

	tv.tv_usec = 1000000;
	if (ioctl(ufd, BIOCSRTIMEOUT, &tv) != -1) e(0);
	if (errno != EINVAL) e(0);

	tv.tv_usec = -1;
	if (ioctl(ufd, BIOCSRTIMEOUT, &tv) != -1) e(0);
	if (errno != EINVAL) e(0);

	tv.tv_sec = -1;
	tv.tv_usec = 0;
	if (ioctl(ufd, BIOCSRTIMEOUT, &tv) != -1) e(0);
	if (errno != EINVAL) e(0);

	tv.tv_sec = INT_MAX;
	if (ioctl(ufd, BIOCSRTIMEOUT, &tv) != -1) e(0);
	if (errno != EDOM) e(0);

	if (ioctl(ufd, BIOCGRTIMEOUT, &tv) != 0) e(0);
	if (tv.tv_sec != 0) e(0);
	if (tv.tv_usec != 0) e(0);

	tv.tv_sec = 123;
	tv.tv_usec = 1;
	if (ioctl(ufd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	if (ioctl(ufd, BIOCGRTIMEOUT, &tv) != 0) e(0);
	if (tv.tv_sec != 123) e(0);
	if (tv.tv_usec == 0) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = 0;
	if (ioctl(ufd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	if (ioctl(ufd, BIOCGRTIMEOUT, &tv) != 0) e(0);
	if (tv.tv_sec != 0) e(0);
	if (tv.tv_usec != 0) e(0);
}

static void test_feedback_operations(int ufd)
{
	unsigned int uval;

	uval = 1;
	if (ioctl(ufd, BIOCGFEEDBACK, &uval) != 0) e(0);
	if (uval != 0) e(0);

	uval = 2;
	if (ioctl(ufd, BIOCSFEEDBACK, &uval) != 0) e(0);

	if (ioctl(ufd, BIOCGFEEDBACK, &uval) != 0) e(0);
	if (uval != 1) e(0);

	uval = 0;
	if (ioctl(ufd, BIOCSFEEDBACK, &uval) != 0) e(0);

	uval = 1;
	if (ioctl(ufd, BIOCGFEEDBACK, &uval) != 0) e(0);
	if (uval != 0) e(0);
}

/* IPv6 version of our filter. */
static struct bpf_insn test94_filter6[] = {
	{ BPF_LD+BPF_B+BPF_ABS, 0, 0, 0 },	/* is this an IPv6 header? */
	{ BPF_ALU+BPF_RSH+BPF_K, 0, 0, 4 },
	{ BPF_JMP+BPF_JEQ+BPF_K, 0, 6, 6 },
	{ BPF_LD+BPF_B+BPF_ABS, 0, 0, 6 },	/* is this a UDP packet? */
	{ BPF_JMP+BPF_JEQ+BPF_K, 0, 4, IPPROTO_UDP },
	{ BPF_LD+BPF_H+BPF_ABS, 0, 0, 40 },	/* source port 12345? */
	{ BPF_JMP+BPF_JEQ+BPF_K, 0, 2, TEST_PORT_A },
	{ BPF_LD+BPF_H+BPF_ABS, 0, 0, 42 },	/* destination port 12346? */
	{ BPF_JMP+BPF_JEQ+BPF_K, 1, 0, TEST_PORT_B },
	{ BPF_RET+BPF_K, 0, 0, 0 },		/* reject the packet */
	{ BPF_RET+BPF_K, 0, 0, (uint32_t)-1 },	/* accept the (whole) packet */
};

/*
 * Test receipt of IPv6 packets, because it was getting a bit messy to
 * integrate that into the previous subtests.  We just want to make sure that
 * IPv6 packets are properly filtered and captured at all.  The rest of the
 * code is entirely version agnostic anyway.
 */
static void
test94i(void)
{
    struct sockaddr_in6 sin6A, sin6B;
    struct bpf_program bf;
    struct bpf_stat bs;
    struct bpf_hdr bh;
    struct ifreq ifr;
    struct ip6_hdr ip6;
    struct udphdr uh;
    uint8_t *buf = NULL;
    uint8_t c;
    socklen_t socklen;
    ssize_t len;
    size_t off;
    unsigned int uval, size, dlt;
    int fd = -1, fd2 = -1, fd3 = -1;

    subtest = 9;

    fd = open(_PATH_BPF, O_RDWR);
    if (fd < 0) e(0);

    if (ioctl(fd, BIOCGBLEN, &size) != 0) e(0);
    if (size < 1024 || size > BPF_MAXBUFSIZE) e(0);

    buf = malloc(size);
    if (buf == NULL) e(0);

    memset(&bf, 0, sizeof(bf));
    bf.bf_len = __arraycount(test94_filter6);
    bf.bf_insns = test94_filter6;
    if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);

    uval = 1;
    if (ioctl(fd, BIOCIMMEDIATE, &uval) != 0) e(0);

    memset(&ifr, 0, sizeof(ifr));
    strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
    if (ioctl(fd, BIOCSETIF, &ifr) != 0) e(0);

    if (ioctl(fd, BIOCGDLT, &dlt) != 0) e(0);
    if (dlt != DLT_RAW) e(0);

    fd2 = socket(AF_INET6, SOCK_DGRAM, 0);
    if (fd2 < 0) e(0);

    memset(&sin6A, 0, sizeof(sin6A));
    sin6A.sin6_family = AF_INET6;
    sin6A.sin6_port = htons(TEST_PORT_A);
    memcpy(&sin6A.sin6_addr, &in6addr_loopback, sizeof(sin6A.sin6_addr));
    if (bind(fd2, (struct sockaddr *)&sin6A, sizeof(sin6A)) != 0) e(0);

    memcpy(&sin6B, &sin6A, sizeof(sin6B));
    sin6B.sin6_port = htons(TEST_PORT_B);
    if (connect(fd2, (struct sockaddr *)&sin6B, sizeof(sin6B)) != 0) e(0);

    fd3 = socket(AF_INET6, SOCK_DGRAM, 0);
    if (fd3 < 0) e(0);

    if (bind(fd3, (struct sockaddr *)&sin6B, sizeof(sin6B)) != 0) e(0);
    if (connect(fd3, (struct sockaddr *)&sin6A, sizeof(sin6A)) != 0) e(0);

    if (write(fd2, "A", 1) != 1) e(0);
    if (read(fd3, &c, 1) != 1) e(0);
    if (c != 'A') e(0);

    if (write(fd3, "B", 1) != 1) e(0);
    if (read(fd2, &c, 1) != 1) e(0);
    if (c != 'B') e(0);

    if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
    if (bs.bs_recv < 2) e(0);
    if (bs.bs_capt != 1) e(0);
    if (bs.bs_drop != 0) e(0);

    memset(buf, 0, size);
    len = read(fd, buf, size);

    if (len != BPF_WORDALIGN(sizeof(bh)) + BPF_WORDALIGN(sizeof(ip6) + sizeof(uh) + 1)) e(0);

    memcpy(&bh, buf, sizeof(bh));

    if (bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) e(0);
    if (bh.bh_caplen != sizeof(ip6) + sizeof(uh) + 1) e(0);
    if (bh.bh_datalen != bh.bh_caplen) e(0);
    if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh))) e(0);

    if (buf[bh.bh_hdrlen + sizeof(ip6) + sizeof(uh)] != 'A') e(0);

    off = test94_make_pkt(buf, 6, 1);
    memcpy(buf + off, "Hello!", 6);

    if (write(fd, buf, off + 6) != off + 6) e(0);

    socklen = sizeof(sin6A);
    if (recvfrom(fd3, buf, size, 0, (struct sockaddr *)&sin6A, &socklen) != 6) e(0);

    if (memcmp(buf, "Hello!", 6) != 0) e(0);
    if (socklen != sizeof(sin6A)) e(0);
    if (sin6A.sin6_family != AF_INET6) e(0);
    if (sin6A.sin6_port != htons(TEST_PORT_A)) e(0);
    if (memcmp(&sin6A.sin6_addr, &in6addr_loopback, sizeof(sin6A.sin6_addr)) != 0) e(0);

    free(buf);

    if (fd3 >= 0 && close(fd3) != 0) e(0);
    if (fd2 >= 0 && close(fd2) != 0) e(0);
    if (fd >= 0 && close(fd) != 0) e(0);
}

/*
 * Test the BPF sysctl(7) interface at a basic level.
 */
static void
test94j(void)
{
	struct bpf_stat bs1, bs2;
	struct bpf_d_ext *bde = NULL;
	uint8_t *buf = NULL;
	unsigned int slot, count, uval;
	size_t len, oldlen, size, bdesize;
	int fd = -1, fd2 = -1, fd3 = -1, val, mib[5], smib[3], found;

	subtest = 10;

	memset(mib, 0, sizeof(mib));
	len = __arraycount(mib);
	if (sysctlnametomib("net.bpf.maxbufsize", mib, &len) != 0) e(0);
	if (len != 3) e(0);

	oldlen = sizeof(val);
	if (sysctl(mib, len, &val, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen != sizeof(val)) e(0);

	if (val < 1024 || val > INT_MAX / 2) e(0);

	if (sysctl(mib, len, NULL, NULL, &val, sizeof(val)) != -1) e(0);
	if (errno != EPERM) e(0);

	memset(smib, 0, sizeof(smib));
	len = __arraycount(smib);
	if (sysctlnametomib("net.bpf.stats", smib, &len) != 0) e(0);
	if (len != 3) e(0);

	oldlen = sizeof(bs1);
	if (sysctl(smib, len, &bs1, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen != sizeof(bs1)) e(0);

	memset(mib, 0, sizeof(mib));
	len = __arraycount(mib);
	if (sysctlnametomib("net.bpf.peers", mib, &len) != 0) e(0);
	if (len != 3) e(0);
	mib[len++] = sizeof(*bde);
	mib[len++] = INT_MAX;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);
	if (fd < 0 || fd2 < 0 || fd3 < 0 || buf == NULL) e(0);

	count = test94_fill_exact(fd2, buf, size, 0);
	test94_fill_exact(fd2, buf, size, 0);
	test94_fill_exact(fd2, buf, size, 0);

	if (write(fd3, "X", 1) != 1) e(0);

	if (sysctl(mib, len, NULL, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen == 0) e(0);

	bdesize = oldlen + sizeof(*bde) * 8;
	bde = malloc(bdesize);
	if (bde == NULL) e(0);

	oldlen = bdesize;
	if (sysctl(mib, len, bde, &oldlen, NULL, 0) != 0) {
		free(bde);
		e(0);
	}
	if (oldlen % sizeof(*bde)) {
		free(bde);
		e(0);
	}

	found = 0;
	for (slot = 0; slot < oldlen / sizeof(*bde); slot++) {
		if (bde[slot].bde_pid != getpid())
			continue;

		if (bde[slot].bde_bufsize != size) e(0);
		if (bde[slot].bde_promisc != 0) e(0);
		if (bde[slot].bde_state != BPF_IDLE) e(0);
		if (bde[slot].bde_immediate != 0) e(0);
		if (bde[slot].bde_hdrcmplt != 0) e(0);
		if (bde[slot].bde_seesent != 1) e(0);
		if (bde[slot].bde_rcount < count * 3 + 1) e(0);
		if (bde[slot].bde_dcount != count) e(0);
		if (bde[slot].bde_ccount != count * 3) e(0);
		if (strcmp(bde[slot].bde_ifname, LOOPBACK_IFNAME) != 0) e(0);

		found++;
	}
	if (found != 1) e(0);

	if (ioctl(fd, BIOCFLUSH) != 0) e(0);

	test94_cleanup(fd, fd2, fd3, buf);
	fd = fd2 = fd3 = -1;
	buf = NULL;

	oldlen = sizeof(bs2);
	if (sysctl(smib, __arraycount(smib), &bs2, &oldlen, NULL, 0) != 0)
		e(0);
	if (oldlen != sizeof(bs2)) e(0);

	if (bs2.bs_recv < bs1.bs_recv + count * 3 + 1) e(0);
	if (bs2.bs_drop != bs1.bs_drop + count) e(0);
	if (bs2.bs_capt != bs1.bs_capt + count * 3) e(0);

	fd = open(_PATH_BPF, O_RDWR);
	if (fd < 0) e(0);

	uval = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &uval) != 0) e(0);
	if (ioctl(fd, BIOCSHDRCMPLT, &uval) != 0) e(0);

	uval = 0;
	if (ioctl(fd, BIOCSSEESENT, &uval) != 0) e(0);

	oldlen = bdesize;
	if (sysctl(mib, len, bde, &oldlen, NULL, 0) != 0) {
		free(bde);
		close(fd);
		e(0);
	}
	if (oldlen % sizeof(*bde)) {
		free(bde);
		close(fd);
		e(0);
	}

	found = 0;
	for (slot = 0; slot < oldlen / sizeof(*bde); slot++) {
		if (bde[slot].bde_pid != getpid())
			continue;

		if (bde[slot].bde_bufsize != size) e(0);
		if (bde[slot].bde_promisc != 0) e(0);
		if (bde[slot].bde_state != BPF_IDLE) e(0);
		if (bde[slot].bde_immediate != 1) e(0);
		if (bde[slot].bde_hdrcmplt != 1) e(0);
		if (bde[slot].bde_seesent != 0) e(0);
		if (bde[slot].bde_rcount != 0) e(0);
		if (bde[slot].bde_dcount != 0) e(0);
		if (bde[slot].bde_ccount != 0) e(0);
		if (bde[slot].bde_ifname[0] != '\0') e(0);

		found++;
	}
	if (found != 1) e(0);

	close(fd);

	oldlen = bdesize;
	if (sysctl(mib, len, bde, &oldlen, NULL, 0) != 0) {
		free(bde);
		e(0);
	}
	if (oldlen % sizeof(*bde)) {
		free(bde);
		e(0);
	}

	for (slot = 0; slot < oldlen / sizeof(*bde); slot++) {
		if (bde[slot].bde_pid == getpid()) {
			free(bde);
			e(0);
		}
	}

	free(bde);
}

/*
 * Test privileged operations as an unprivileged caller.
 */
static void
test94k(void)
{
	struct passwd *pw;
	pid_t pid;
	size_t len, oldlen;
	int mib[5], status;

	subtest = 11;

	pid = fork();
	if (pid == -1) {
		e(0);
		return;
	}

	if (pid == 0) {
		errct = 0;

		pw = getpwnam(NONROOT_USER);
		if (pw == NULL) e(0);

		if (setuid(pw->pw_uid) != 0) e(0);

		if (open(_PATH_BPF, O_RDWR) != -1) e(0);
		if (errno != EACCES) e(0);

		memset(mib, 0, sizeof(mib));
		len = __arraycount(mib);
		if (sysctlnametomib("net.bpf.peers", mib, &len) != 0) e(0);
		if (len != 3) e(0);
		mib[len++] = sizeof(struct bpf_d_ext);
		mib[len++] = INT_MAX;

		if (sysctl(mib, len, NULL, &oldlen, NULL, 0) != -1) e(0);
		if (errno != EPERM) e(0);

		exit(errct);
	}

	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);
}

/*
 * Test that traffic directed to loopback addresses be dropped on non-loopback
 * interfaces.  In particular, inbound traffic to 127.0.0.1 and ::1 should not
 * be accepted on any interface that does not own those addresses.  This test
 * is here because BPF feedback mode is (currently) the only way in which we
 * can generate inbound traffic the ethernet level, and even then only as a
 * side effect of sending outbound traffic.  That is: this test sends the same
 * test packets to the local network!  As such it must be performed only when
 * USENETWORK=yes and therefore at the user's risk.
 */
static void
test94l(void)
{
	struct sockaddr_in sin;
	struct sockaddr_in6 sin6;
	struct sockaddr_dl sdl;
	struct ifreq ifr;
	struct ifaddrs *ifa, *ifp;
	struct if_data *ifdata;
	uint8_t buf[sizeof(struct ether_header) + MAX(sizeof(struct ip),
	    sizeof(struct ip6_hdr)) + sizeof(struct udphdr) + 6];
	struct ether_header ether;
	const uint8_t ether_src[ETHER_ADDR_LEN] =
	    { 0x02, 0x00, 0x01, 0x12, 0x34, 0x56 };
	unsigned int val;
	size_t off;
	int bfd, sfd;

	subtest = 12;

	if (!get_setting_use_network())
		return;

	memset(&ifr, 0, sizeof(ifr));
	memset(&ether, 0, sizeof(ether));

	if (getifaddrs(&ifa) != 0) e(0);

	ifp = NULL;
	for (struct ifaddrs *current = ifa; current != NULL; current = current->ifa_next) {
		if (!(current->ifa_flags & IFF_UP) || current->ifa_addr == NULL ||
		    current->ifa_addr->sa_family != AF_LINK)
			continue;

		ifdata = (struct if_data *)current->ifa_data;
		if (ifdata != NULL && ifdata->ifi_type == IFT_ETHER &&
		    ifdata->ifi_link_state != LINK_STATE_DOWN) {
			strlcpy(ifr.ifr_name, current->ifa_name,
			    sizeof(ifr.ifr_name));

			memcpy(&sdl, (struct sockaddr_dl *)current->ifa_addr,
			    offsetof(struct sockaddr_dl, sdl_data));
			if (sdl.sdl_alen != sizeof(ether.ether_dhost)) e(0);
			memcpy(ether.ether_dhost,
			    ((struct sockaddr_dl *)current->ifa_addr)->sdl_data +
			    sdl.sdl_nlen, sdl.sdl_alen);
			ifp = current;
			break;
		}
	}

	freeifaddrs(ifa);

	if (ifp == NULL)
		return;

	bfd = open(_PATH_BPF, O_RDWR);
	if (bfd < 0) e(0);

	if (ioctl(bfd, BIOCSETIF, &ifr) != 0) e(0);

	if (ioctl(bfd, BIOCGDLT, &val) != 0) e(0);
	if (val != DLT_EN10MB) e(0);

	val = 1;
	if (ioctl(bfd, BIOCSFEEDBACK, &val) != 0) e(0);

	sfd = socket(AF_INET, SOCK_DGRAM, 0);
	if (sfd < 0) e(0);

	memset(&sin, 0, sizeof(sin));
	sin.sin_family = AF_INET;
	sin.sin_port = htons(TEST_PORT_B);
	sin.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	if (bind(sfd, (struct sockaddr *)&sin, sizeof(sin)) != 0) e(0);

	memcpy(ether.ether_shost, ether_src, sizeof(ether.ether_shost));
	ether.ether_type = htons(ETHERTYPE_IP);

	memcpy(buf, &ether, sizeof(ether));
	off = sizeof(ether);
	off += test94_make_pkt(buf + off, 6, 0);
	if (off + 6 > sizeof(buf)) e(0);
	memcpy(buf + off, "Hello!", 6);

	if (write(bfd, buf, off + 6) != off + 6) e(0);

	if (recv(sfd, buf, sizeof(buf), MSG_DONTWAIT) != -1) e(0);
	if (errno != EWOULDBLOCK) e(0);

	if (close(sfd) != 0) e(0);

	sfd = socket(AF_INET6, SOCK_DGRAM, 0);
	if (sfd < 0) e(0);

	memset(&sin6, 0, sizeof(sin6));
	sin6.sin6_family = AF_INET6;
	sin6.sin6_port = htons(TEST_PORT_B);
	memcpy(&sin6.sin6_addr, &in6addr_loopback, sizeof(sin6.sin6_addr));
	if (bind(sfd, (struct sockaddr *)&sin6, sizeof(sin6)) != 0) e(0);

	ether.ether_type = htons(ETHERTYPE_IPV6);

	memcpy(buf, &ether, sizeof(ether));
	off = sizeof(ether);
	off += test94_make_pkt(buf + off, 6, 1);
	if (off + 6 > sizeof(buf)) e(0);
	memcpy(buf + off, "Hello!", 6);

	if (write(bfd, buf, off + 6) != off + 6) e(0);

	if (recv(sfd, buf, sizeof(buf), MSG_DONTWAIT) != -1) e(0);
	if (errno != EWOULDBLOCK) e(0);

	if (close(sfd) != 0) e(0);
	if (close(bfd) != 0) e(0);
}

/*
 * Test program for LWIP BPF.
 */
int
main(int argc, char ** argv)
{
	int i, m;
	typedef void (*test_func_t)(void);
	test_func_t test_functions[] = {
		test94a, test94b, test94c, test94d,
		test94e, test94f, test94g, test94h,
		test94i, test94j, test94k, test94l
	};
	const int num_tests = sizeof(test_functions) / sizeof(test_functions[0]);

	start(94);

	srand48(time(NULL));

	if (argc == 2) {
		char *endptr;
		long value = strtol(argv[1], &endptr, 0);
		if (*endptr != '\0' || value < 0 || value > INT_MAX) {
			return 1;
		}
		m = (int)value;
	} else {
		m = 0xFFF;
	}

	for (i = 0; i < ITERATIONS; i++) {
		int bit;
		for (bit = 0; bit < num_tests; bit++) {
			if (m & (1 << bit)) {
				test_functions[bit]();
			}
		}
	}

	quit();
	return 0;
}
