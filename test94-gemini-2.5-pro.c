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
	if (sig != SIGUSR1)
	{
		return;
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
	const size_t MIN_PACKET_SIZE = 16;
	const char FILL_CHAR = 'Y';
	const char MARKER_CHAR = 'X';
	const char END_CHAR = 'Z';

	const size_t required_len =
	    BPF_WORDALIGN(sizeof(struct bpf_hdr)) + sizeof(struct ip) +
	    sizeof(struct udphdr) + sizeof(seq);

	size_t packet_size = MIN_PACKET_SIZE;
	while (packet_size <= required_len) {
		packet_size <<= 1;
	}

	if (packet_size > size) {
		e(0);
	}

	const size_t aligned_hdr_len =
	    BPF_WORDALIGN(required_len - sizeof(seq));
	const size_t write_size = packet_size - aligned_hdr_len;

	ssize_t remaining_size = (ssize_t)size;
	while (remaining_size > 0) {
		memset(buf, FILL_CHAR, write_size);
		if (write_size > sizeof(seq)) {
			buf[sizeof(seq)] = MARKER_CHAR;
		}
		buf[write_size - 1] = END_CHAR;

		memcpy(buf, &seq, sizeof(seq));

		if (write(fd, buf, write_size) != (ssize_t)write_size) {
			e(0);
		}

		remaining_size -= packet_size;
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
	const size_t hdrlen = BPF_WORDALIGN(BPF_WORDALIGN(sizeof(struct bpf_hdr)) +
	    sizeof(struct ip) + sizeof(struct udphdr));

	size_t sent_len = 0;
	uint32_t seq = 1;

	do {
		size_t rand_payload_add = 0;
		if (size >= 10) {
			rand_payload_add = lrand48() % (size / 10);
		}

		const size_t payload_len = sizeof(seq) + rand_payload_add;

		memset(buf, 'Y', payload_len);
		if (payload_len > sizeof(seq)) {
			buf[sizeof(seq)] = 'X';
		}
		buf[payload_len - 1] = 'Z';
		memcpy(buf, &seq, sizeof(seq));

		const ssize_t bytes_written = write(fd, buf, payload_len);
		if (bytes_written < 0 || (size_t)bytes_written != payload_len) {
			e(0);
		}

		const size_t total_len = hdrlen + payload_len;
		sent_len += BPF_WORDALIGN(total_len);
		seq++;
	} while (sent_len <= size);
}

/*
 * Send a UDP packet with a specific size of 'size' bytes and sequence number
 * 'seq' on socket 'fd', using 'buf' as scratch buffer.
 */
static void
test94_add_specific(int fd, uint8_t * buf, size_t size, uint32_t seq)
{
	const size_t total_size = size + sizeof(seq);
	const char fill_char = 'Y';
	const char marker_char = 'X';
	const char end_char = 'Z';

	memset(buf, fill_char, total_size);

	if (size > 0) {
		buf[sizeof(seq)] = marker_char;
	}
	buf[total_size - 1] = end_char;

	memcpy(buf, &seq, sizeof(seq));

	const ssize_t bytes_written = write(fd, buf, total_size);
	if (bytes_written != (ssize_t)total_size) {
		e(0);
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
    const size_t max_len = size / 10;

    if (max_len == 0) {
        test94_add_specific(fd, buf, 0, seq);
        return;
    }

    const size_t random_len = (size_t)(lrand48() % max_len);
    test94_add_specific(fd, buf, random_len, seq);
}

/*
 * Check whether the packet in 'buf' of 'caplen' captured bytes out of
 * 'datalen' data bytes is one we sent.  If so, return an offset to the packet
 * data.  If not, return a negative value.
 */
static ssize_t
test94_check_pkt(uint8_t * buf, ssize_t caplen, ssize_t datalen)
{
    const size_t ip_header_size = sizeof(struct ip);
    const size_t udp_header_size = sizeof(struct udphdr);

    if (caplen < ip_header_size + udp_header_size) {
        return -1;
    }

    struct ip ip_header;
    memcpy(&ip_header, buf, ip_header_size);

    if (ip_header.ip_v != IPVERSION) {
        return -1;
    }
    if (ip_header.ip_hl != ip_header_size / 4) {
        return -1;
    }
    if (ip_header.ip_p != IPPROTO_UDP) {
        return -1;
    }

    struct udphdr udp_header;
    memcpy(&udp_header, buf + ip_header_size, udp_header_size);

    if (udp_header.uh_sport != htons(TEST_PORT_A)) {
        return -1;
    }
    if (udp_header.uh_dport != htons(TEST_PORT_B)) {
        return -1;
    }

    if ((ssize_t)ntohs(udp_header.uh_ulen) != datalen - (ssize_t)ip_header_size) {
        return -1;
    }

    return (ssize_t)(ip_header_size + udp_header_size);
}

/*
 * Check whether the capture in 'buf' of 'len' bytes looks like a valid set of
 * captured packets.  The valid packets start from sequence number 'seq'; the
 * next expected sequence number is returned.  If 'filtered' is set, there
 * should be no other packets in the capture; otherwise, other packets are
 * ignored.
 */
static bool
check_packet_payload(const uint8_t *pkt_data, ssize_t offset, uint32_t caplen,
                     uint32_t datalen)
{
	ssize_t current_offset = offset;
	const ssize_t s_caplen = (ssize_t)caplen;
	const ssize_t s_datalen = (ssize_t)datalen;

	if (current_offset < s_datalen - 1) {
		if (current_offset < s_caplen && pkt_data[current_offset] != 'X') {
			return false;
		}
		current_offset++;

		while (current_offset < s_caplen && current_offset < s_datalen - 1) {
			if (pkt_data[current_offset] != 'Y') {
				return false;
			}
			current_offset++;
		}
	}

	if (current_offset < s_caplen && current_offset == s_datalen - 1) {
		if (pkt_data[current_offset] != 'Z') {
			return false;
		}
	}

	return true;
}

static uint32_t
test94_check(uint8_t * buf, ssize_t len, uint32_t seq, int filtered,
	uint32_t * caplen, uint32_t * datalen)
{
	uint8_t *current_buf = buf;
	ssize_t remaining_len = len;

	while (remaining_len > 0) {
		struct bpf_hdr bh;
		const size_t bpf_hdr_len_aligned = BPF_WORDALIGN(sizeof(bh));

		if (remaining_len < (ssize_t)bpf_hdr_len_aligned) {
			return seq;
		}

		memcpy(&bh, current_buf, sizeof(bh));

		if ((bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) ||
		    bh.bh_hdrlen != bpf_hdr_len_aligned) {
			return seq;
		}

		if (caplen != NULL) {
			if (bh.bh_caplen != *caplen || bh.bh_datalen != *datalen) {
				return seq;
			}
			caplen++;
			datalen++;
		} else {
			if (bh.bh_datalen != bh.bh_caplen) {
				return seq;
			}
		}

		const size_t packet_len_aligned = BPF_WORDALIGN(bh.bh_caplen);
		if ((size_t)bh.bh_hdrlen + packet_len_aligned > (size_t)remaining_len) {
			return seq;
		}

		current_buf += bh.bh_hdrlen;
		remaining_len -= bh.bh_hdrlen;

		const uint8_t *const pkt_data = current_buf;
		const ssize_t off =
		    test94_check_pkt(pkt_data, bh.bh_caplen, bh.bh_datalen);

		if (off >= 0) {
			if ((ssize_t)bh.bh_caplen < off + (ssize_t)sizeof(uint32_t)) {
				return seq;
			}

			uint32_t nseq;
			memcpy(&nseq, &pkt_data[off], sizeof(nseq));
			if (nseq != seq) {
				return seq;
			}

			if (!check_packet_payload(pkt_data, off + sizeof(uint32_t),
			                        bh.bh_caplen, bh.bh_datalen)) {
				return seq;
			}
			seq++;
		} else {
			if (filtered) {
				return seq;
			}
		}

		current_buf += packet_len_aligned;
		remaining_len -= packet_len_aligned;
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
test94_setup(int *fd, int *fd2, int *fd3, uint8_t **buf,
    unsigned int requested_size, int set_filter)
{
	struct sockaddr_in sinA, sinB;
	struct ifreq ifr;
	struct bpf_program bf;
	unsigned int dlt;
	unsigned int buffer_size = requested_size;
	size_t result_size = 0;

	*fd = -1;
	*fd2 = -1;
	*fd3 = -1;
	*buf = NULL;

	*fd = open(_PATH_BPF, O_RDWR);
	if (*fd < 0) {
		goto fail;
	}

	if (buffer_size != 0) {
		if (ioctl(*fd, BIOCSBLEN, &buffer_size) != 0) {
			goto fail;
		}
	}

	if (ioctl(*fd, BIOCGBLEN, &buffer_size) != 0) {
		goto fail;
	}

	const unsigned int MIN_BPF_BUFSIZE = 1024;
	if (buffer_size < MIN_BPF_BUFSIZE || buffer_size > BPF_MAXBUFSIZE) {
		goto fail;
	}

	*buf = malloc(buffer_size);
	if (*buf == NULL) {
		goto fail;
	}

	if (set_filter) {
		memset(&bf, 0, sizeof(bf));
		bf.bf_len = __arraycount(test94_filter);
		bf.bf_insns = test94_filter;
		if (ioctl(*fd, BIOCSETF, &bf) != 0) {
			goto fail;
		}
	}

	memset(&ifr, 0, sizeof(ifr));
	if (strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name)) >=
	    sizeof(ifr.ifr_name)) {
		goto fail;
	}
	if (ioctl(*fd, BIOCSETIF, &ifr) != 0) {
		goto fail;
	}

	if (ioctl(*fd, BIOCGDLT, &dlt) != 0) {
		goto fail;
	}
	if (dlt != DLT_RAW) {
		goto fail;
	}

	*fd2 = socket(AF_INET, SOCK_DGRAM, 0);
	if (*fd2 < 0) {
		goto fail;
	}

	memset(&sinA, 0, sizeof(sinA));
	sinA.sin_family = AF_INET;
	sinA.sin_port = htons(TEST_PORT_A);
	sinA.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	if (bind(*fd2, (struct sockaddr *)&sinA, sizeof(sinA)) != 0) {
		goto fail;
	}

	memcpy(&sinB, &sinA, sizeof(sinB));
	sinB.sin_port = htons(TEST_PORT_B);
	if (connect(*fd2, (struct sockaddr *)&sinB, sizeof(sinB)) != 0) {
		goto fail;
	}

	*fd3 = socket(AF_INET, SOCK_DGRAM, 0);
	if (*fd3 < 0) {
		goto fail;
	}

	if (bind(*fd3, (struct sockaddr *)&sinB, sizeof(sinB)) != 0) {
		goto fail;
	}

	if (connect(*fd3, (struct sockaddr *)&sinA, sizeof(sinA)) != 0) {
		goto fail;
	}

	result_size = buffer_size;
	return result_size;

fail:
	if (*fd3 != -1) {
		close(*fd3);
	}
	if (*fd2 != -1) {
		close(*fd2);
	}
	free(*buf);
	if (*fd != -1) {
		close(*fd);
	}

	*fd = -1;
	*fd2 = -1;
	*fd3 = -1;
	*buf = NULL;
	return 0;
}

/*
 * Clean up resources allocated by test94_setup().
 */
static void
test94_cleanup(int fd, int fd2, int fd3, uint8_t *buf)
{
	int close_result = 0;

	close_result |= close(fd3);
	close_result |= close(fd2);

	free(buf);

	close_result |= close(fd);

	if (close_result != 0) {
		e(0);
	}
}

/*
 * Test reading packets from a BPF device, using regular mode.
 */
static void
wait_for_child(pid_t pid)
{
	int status;
	if (waitpid(pid, &status, 0) != pid) {
		e(0);
	}
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
		e(0);
	}
}

struct child_args {
	int fd;
	int fd2;
	uint8_t *buf;
	size_t size;
	uint32_t seq;
};

static void
child_task_fill_buffer(void *arg)
{
	struct child_args *args = arg;
	usleep(SLEEP_TIME);
	test94_fill_random(args->fd2, args->buf, args->size);
}

static void
child_task_add_packet_and_pause(void *arg)
{
	struct child_args *args = arg;

	signal(SIGUSR1, test94_signal);
	usleep(SLEEP_TIME);
	test94_add_random(args->fd2, args->buf, args->size, args->seq);
	usleep(SLEEP_TIME);

	if (got_signal != 0) e(0);
	pause();
	if (got_signal != 1) e(0);
}

static void
child_task_read_expect_intr(void *arg)
{
	struct child_args *args = arg;
	signal(SIGUSR1, test94_signal);

	if (read(args->fd, args->buf, args->size) != -1) e(0);
	if (errno != EINTR) e(0);
	if (got_signal != 1) e(0);
}

static void
child_task_add_one_packet(void *arg)
{
	struct child_args *args = arg;
	usleep(SLEEP_TIME);
	test94_add_random(args->fd2, args->buf, args->size, args->seq);
}

static pid_t
run_in_child(void (*task)(void *), void *arg)
{
	pid_t pid = fork();
	switch (pid) {
	case -1:
		e(0);
		return -1;
	case 0:
		errct = 0;
		task(arg);
		exit(errct);
	default:
		return pid;
	}
}

static void
test_initial_read_no_filter(int fd, int fd2, uint8_t *buf, size_t size)
{
	struct child_args args = { .fd2 = fd2, .buf = buf, .size = size };
	pid_t pid = run_in_child(child_task_fill_buffer, &args);

	ssize_t len = read(fd, buf, size);
	if (len < (ssize_t)size * 3 / 4 || len > (ssize_t)size) e(0);

	test94_check(buf, len, 1, 0, NULL, NULL);
	wait_for_child(pid);
}

static void
test_invalid_read_sizes(int fd, uint8_t *buf, size_t size)
{
	if (read(fd, buf, size - 1) != -1 || errno != EINVAL) e(0);
	if (read(fd, buf, size + 1) != -1 || errno != EINVAL) e(0);
	if (read(fd, buf, sizeof(struct bpf_hdr)) != -1 || errno != EINVAL) e(0);
}

static void
install_filter(int fd)
{
	struct bpf_program bf;
	memset(&bf, 0, sizeof(bf));
	bf.bf_len = __arraycount(test94_filter);
	bf.bf_insns = test94_filter;
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);
}

static uint32_t
test_select_on_full_buffer(int fd, int fd2, uint8_t *buf, size_t size)
{
	struct timeval tv = { 0, 0 };
	fd_set fds;
	int bytes;

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv) != 0 || FD_ISSET(fd, &fds)) e(0);
	if (ioctl(fd, FIONREAD, &bytes) != 0 || bytes != 0) e(0);

	struct child_args args = { .fd2 = fd2, .buf = buf, .size = size };
	pid_t pid = run_in_child(child_task_fill_buffer, &args);

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1 || !FD_ISSET(fd, &fds)) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1 || !FD_ISSET(fd, &fds)) e(0);

	ssize_t len = read(fd, buf, size);
	if (len != bytes) e(0);
	if (len < (ssize_t)size * 3 / 4 || len > (ssize_t)size) e(0);

	uint32_t seq = test94_check(buf, len, 1, 1, NULL, NULL);
	wait_for_child(pid);
	return seq;
}

static void
check_read_buffer_empty(int fd)
{
	struct timeval tv = { 0, 0 };
	fd_set fds;
	int bytes;

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv) != 0 || FD_ISSET(fd, &fds)) e(0);
	if (ioctl(fd, FIONREAD, &bytes) != 0 || bytes != 0) e(0);
}

static uint32_t
test_read_timeout_partial_buffer(int fd, int fd2, uint8_t *buf, size_t size, uint32_t seq)
{
	struct timeval tv = { 0, SLEEP_TIME * 3 };
	if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	got_signal = 0;
	struct child_args args = { .fd2 = fd2, .buf = buf, .size = size, .seq = seq + 1 };
	pid_t pid = run_in_child(child_task_add_packet_and_pause, &args);

	ssize_t len = read(fd, buf, size);
	if (len <= 0 || len >= (ssize_t)size * 3 / 4) e(0);

	uint32_t next_seq = test94_check(buf, len, seq, 1, NULL, NULL);
	if (next_seq != seq + 2) e(0);

	if (kill(pid, SIGUSR1) != 0) e(0);
	wait_for_child(pid);

	return next_seq;
}

static void
test_read_timeout_empty_buffer(int fd, uint8_t *buf, size_t size)
{
	struct timeval tv = { 0, SLEEP_TIME };
	if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	if (read(fd, buf, size) != -1 || errno != EAGAIN) e(0);
}

static void
test_interrupted_read_empty_buffer(int fd, uint8_t *buf, size_t size)
{
	struct timeval tv = { 0, 0 };
	if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	got_signal = 0;
	struct child_args args = { .fd = fd, .buf = buf, .size = size };
	pid_t pid = run_in_child(child_task_read_expect_intr, &args);

	usleep(SLEEP_TIME * 2);

	if (kill(pid, SIGUSR1) != 0) e(0);
	wait_for_child(pid);
}

static void
test_interrupted_read_partial_buffer(int fd, int fd2, uint8_t *buf, size_t size)
{
	got_signal = 0;
	struct child_args args = { .fd = fd, .buf = buf, .size = size };
	pid_t pid = run_in_child(child_task_read_expect_intr, &args);

	usleep(SLEEP_TIME);
	test94_add_random(fd2, buf, size, 2);
	usleep(SLEEP_TIME);

	if (kill(pid, SIGUSR1) != 0) e(0);
	wait_for_child(pid);
}

static void
test_non_blocking_reads(int fd, int fd2, uint8_t *buf, size_t size)
{
	int fl = fcntl(fd, F_GETFL);
	if (fl == -1) e(0);
	if (fcntl(fd, F_SETFL, fl | O_NONBLOCK) != 0) e(0);

	ssize_t len = read(fd, buf, size);
	if (len <= 0 || len >= (ssize_t)size * 3 / 4) e(0);
	uint32_t seq = test94_check(buf, len, 2, 1, NULL, NULL);

	if (read(fd, buf, size) != -1 || errno != EAGAIN) e(0);

	test94_fill_random(fd2, buf, size);
	len = read(fd, buf, size);
	if (len < (ssize_t)size * 3 / 4 || len > (ssize_t)size) e(0);
	seq = test94_check(buf, len, 1, 1, NULL, NULL);

	len = read(fd, buf, size);
	if (len <= 0 || len >= (ssize_t)size * 3 / 4) e(0);
	if (test94_check(buf, len, seq, 1, NULL, NULL) != seq + 1) e(0);

	if (fcntl(fd, F_SETFL, fl) != 0) e(0);
}

static void
test_select_behavior_on_single_packet(int fd, int fd2, uint8_t *buf, size_t size)
{
	struct timeval tv_timeout = { 0, SLEEP_TIME * 2 };
	if (ioctl(fd, BIOCSRTIMEOUT, &tv_timeout) != 0) e(0);

	struct child_args args = { .fd2 = fd2, .buf = buf, .size = size, .seq = 1 };
	pid_t pid = run_in_child(child_task_add_one_packet, &args);

	struct timeval tv_select = { 1, 0 };
	fd_set fds;
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv_select) != 0) e(0);

	wait_for_child(pid);
}

static void
test94a(void)
{
	uint8_t *buf;
	size_t size;
	uint32_t seq;
	int fd, fd2, fd3;

	subtest = 1;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 0);

	test_initial_read_no_filter(fd, fd2, buf, size);
	test_invalid_read_sizes(fd, buf, size);
	install_filter(fd);

	seq = test_select_on_full_buffer(fd, fd2, buf, size);
	check_read_buffer_empty(fd);

	(void)test_read_timeout_partial_buffer(fd, fd2, buf, size, seq);
	test_read_timeout_empty_buffer(fd, buf, size);
	test_interrupted_read_empty_buffer(fd, buf, size);
	test_interrupted_read_partial_buffer(fd, fd2, buf, size);
	test_non_blocking_reads(fd, fd2, buf, size);
	test_select_behavior_on_single_packet(fd, fd2, buf, size);

	test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test reading packets from a BPF device, using immediate mode.
 */
#include <sys/time.h>
#include <sys/types.h>
#include <sys/ioctl.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdint.h>
#include <errno.h>

#define NO_SIZE_LIMIT 0
#define SET_FILTER 1
#define IS_FILTERED 1
#define IMMEDIATE_MODE_ON 1
#define INITIAL_SEQ 1

// Forward declarations for functions used but not defined in the snippet
extern int errct;
extern int subtest;
extern void e(int code);
extern size_t test94_setup(int *fd, int *fd2, int *fd3, uint8_t **buf, size_t size, int set_filter);
extern void test94_fill_random(int fd, uint8_t *buf, size_t size);
extern void test94_add_random(int fd, uint8_t *buf, size_t size, uint32_t seq);
extern uint32_t test94_check(uint8_t *buf, size_t len, uint32_t seq, int filtered, size_t *caplen, size_t *datalen);
extern void test94_cleanup(int fd, int fd2, int fd3, uint8_t *buf);

// Assuming SLEEP_TIME is defined elsewhere, e.g., in a header
#ifndef SLEEP_TIME
#define SLEEP_TIME 100000 // 100ms
#endif


static void
check_select_status(int fd, int expected_result)
{
	fd_set fds;
	struct timeval tv = { .tv_sec = 0, .tv_usec = 0 };

	FD_ZERO(&fds);
	FD_SET(fd, &fds);

	int result = select(fd + 1, &fds, NULL, NULL, &tv);
	if (result != expected_result)
		e(0);
	if (result > 0 && !FD_ISSET(fd, &fds))
		e(0);
}

static void
verify_buffer_empty(int fd)
{
	check_select_status(fd, 0);
	int bytes;
	if (ioctl(fd, FIONREAD, &bytes) != 0 || bytes != 0)
		e(0);
}

static uint32_t
read_and_check_data(int fd, uint8_t *buf, size_t size, uint32_t seq,
    uint32_t packets_expected, int check_full)
{
	int bytes;
	if (ioctl(fd, FIONREAD, &bytes) != 0)
		e(0);

	ssize_t len = read(fd, buf, size);
	if (len <= 0 || len != bytes)
		e(0);

	if (check_full) {
		if (len < (ssize_t)(size * 3 / 4) || len > (ssize_t)size)
			e(0);
	} else {
		if (len >= (ssize_t)(size * 3 / 4))
			e(0);
	}

	uint32_t next_seq = test94_check(buf, len, seq, IS_FILTERED, NULL, NULL);
	if (next_seq != seq + packets_expected)
		e(0);

	return next_seq;
}

static uint32_t
test_read_from_full_buffer(int fd, int fd2, uint8_t *buf, size_t size)
{
	test94_fill_random(fd2, buf, size);
	check_select_status(fd, 1);
	return read_and_check_data(fd, buf, size, INITIAL_SEQ, 0, 1);
}

static uint32_t
test_read_remaining_packet(int fd, uint8_t *buf, size_t size, uint32_t seq)
{
	check_select_status(fd, 1);
	return read_and_check_data(fd, buf, size, seq, 1, 0);
}

static uint32_t
test_read_multiple_packets(int fd, int fd2, uint8_t *buf, size_t size, uint32_t seq)
{
	test94_add_random(fd2, buf, size, seq);
	test94_add_random(fd2, buf, size, seq + 1);
	check_select_status(fd, 1);
	return read_and_check_data(fd, buf, size, seq, 2, 0);
}

static pid_t
fork_child_writer(int fd2, uint8_t *buf, size_t size, uint32_t seq)
{
	pid_t pid = fork();
	if (pid == -1) {
		e(0);
	} else if (pid == 0) {
		errct = 0;
		usleep(SLEEP_TIME);
		test94_add_random(fd2, buf, size, seq);
		_exit(errct);
	}
	return pid;
}

static void
wait_for_child(pid_t pid)
{
	int status;
	if (waitpid(pid, &status, 0) != pid)
		e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0)
		e(0);
}

static uint32_t
test_blocking_read_wakeup(int fd, int fd2, uint8_t *buf, size_t size, uint32_t seq)
{
	pid_t pid = fork_child_writer(fd2, buf, size, seq);
	uint32_t next_seq = read_and_check_data(fd, buf, size, seq, 1, 0);
	wait_for_child(pid);
	return next_seq;
}

static uint32_t
test_select_wakeup(int fd, int fd2, uint8_t *buf, size_t size, uint32_t seq)
{
	pid_t pid = fork_child_writer(fd2, buf, size, seq);

	fd_set fds;
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1 || !FD_ISSET(fd, &fds))
		e(0);

	// Test that select() remains ready
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1 || !FD_ISSET(fd, &fds))
		e(0);

	uint32_t next_seq = read_and_check_data(fd, buf, size, seq, 1, 0);
	wait_for_child(pid);
	return next_seq;
}

static void
test_non_blocking_read(int fd, int fd2, uint8_t *buf, size_t size)
{
	int fl_orig;
	if ((fl_orig = fcntl(fd, F_GETFL)) == -1)
		e(0);
	if (fcntl(fd, F_SETFL, fl_orig | O_NONBLOCK) != 0)
		e(0);

	if (read(fd, buf, size) != -1 || errno != EAGAIN)
		e(0);

	uint32_t seq = test_read_from_full_buffer(fd, fd2, buf, size);
	(void)test_read_remaining_packet(fd, buf, size, seq);

	if (fcntl(fd, F_SETFL, fl_orig) != 0)
		e(0);
}

static void
test_read_timeout(int fd, uint8_t *buf, size_t size)
{
	struct timeval tv = { .tv_sec = 0, .tv_usec = SLEEP_TIME };
	if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0)
		e(0);

	if (read(fd, buf, size) != -1 || errno != EAGAIN)
		e(0);
}

static void
test94b(void)
{
	subtest = 2;

	int fd, fd2, fd3;
	uint8_t *buf;
	size_t size = test94_setup(&fd, &fd2, &fd3, &buf, NO_SIZE_LIMIT, SET_FILTER);

	unsigned int val = IMMEDIATE_MODE_ON;
	if (ioctl(fd, BIOCIMMEDIATE, &val) != 0)
		e(0);

	verify_buffer_empty(fd);

	uint32_t seq = test_read_from_full_buffer(fd, fd2, buf, size);
	seq = test_read_remaining_packet(fd, buf, size, seq);

	verify_buffer_empty(fd);

	seq = test_read_multiple_packets(fd, fd2, buf, size, seq);
	seq = test_blocking_read_wakeup(fd, fd2, buf, size, seq);
	seq = test_select_wakeup(fd, fd2, buf, size, seq);

	test_non_blocking_read(fd, fd2, buf, size);
	test_read_timeout(fd, buf, size);

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
check_bpf_stats(int fd, uint32_t expected_capt, uint32_t expected_drop)
{
	struct bpf_stat bs;
	if (ioctl(fd, BIOCGSTATS, &bs) != 0) {
		e(0);
	}
	if (bs.bs_capt != expected_capt) {
		e(0);
	}
	if (bs.bs_recv < bs.bs_capt) {
		e(0);
	}
	if (bs.bs_drop != expected_drop) {
		e(0);
	}
}

static void
check_fionread(int fd, size_t expected_bytes)
{
	int bytes;
	if (ioctl(fd, FIONREAD, &bytes) != 0) {
		e(0);
	}
	if ((size_t)bytes != expected_bytes) {
		e(0);
	}
}

static void
check_select(int fd)
{
	fd_set fds;
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) {
		e(0);
	}
	if (!FD_ISSET(fd, &fds)) {
		e(0);
	}
}

static uint32_t
read_and_check(int fd, void *buf, size_t size, uint32_t seq)
{
	if (read(fd, buf, size) != (ssize_t)size) {
		e(0);
	}
	return test94_check(buf, size, seq, 1, NULL, NULL);
}

static void
child_proc_main(int fd2, uint8_t *buf, size_t size, uint32_t seq)
{
	errct = 0;
	usleep(SLEEP_TIME);
	test94_fill_exact(fd2, buf, size, seq);
	exit(errct);
}

static pid_t
start_child(int fd2, uint8_t *buf, size_t size, uint32_t seq)
{
	pid_t pid = fork();
	if (pid == -1) {
		e(0);
	} else if (pid == 0) {
		child_proc_main(fd2, buf, size, seq);
	}
	return pid;
}

static void
wait_for_child(pid_t pid)
{
	int status;
	if (waitpid(pid, &status, 0) != pid) {
		e(0);
	}
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
		e(0);
	}
}

static void
test94c(void)
{
	subtest = 3;

	int fd, fd2, fd3;
	uint8_t *buf;
	size_t size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);

	check_bpf_stats(fd, 0, 0);

	/*
	 * Test read, select, and ioctl(FIONREAD) on an exactly filled buffer.
	 */
	const uint32_t count = test94_fill_exact(fd2, buf, size, 0);
	check_bpf_stats(fd, count, 0);
	check_fionread(fd, size);
	check_select(fd);
	read_and_check(fd, buf, size, 0);

	/*
	 * If the store buffer is full, the buffers should be swapped after
	 * emptying the hold buffer, and subsequent packets dropped.
	 */
	const uint32_t seq = test94_fill_exact(fd2, buf, size, 1);
	test94_fill_exact(fd2, buf, size, seq);
	check_bpf_stats(fd, count * 3, 0);

	test94_add_random(fd2, buf, size, 0);
	check_bpf_stats(fd, count * 3 + 1, 1);

	test94_add_random(fd2, buf, size, 0);
	check_bpf_stats(fd, count * 3 + 2, 2);

	check_fionread(fd, size);

	if (read_and_check(fd, buf, size, 1) != seq) e(0);
	if (read_and_check(fd, buf, size, seq) != (count * 2 + 1)) e(0);

	/*
	 * See if an exactly filled buffer resumes reads...
	 */
	pid_t pid = start_child(fd2, buf, size, 1);
	read_and_check(fd, buf, size, 1);
	wait_for_child(pid);

	/*
	 * ...and selects, including non-blocking reads.
	 */
	pid = start_child(fd2, buf, size, seq);
	check_select(fd);

	int fl;
	if ((fl = fcntl(fd, F_GETFL)) == -1) e(0);
	if (fcntl(fd, F_SETFL, fl | O_NONBLOCK) != 0) e(0);

	read_and_check(fd, buf, size, seq);
	if (read(fd, buf, size) != -1) e(0);
	if (errno != EAGAIN) e(0);

	wait_for_child(pid);

	check_bpf_stats(fd, count * 5 + 2, 2);

	test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test receipt of large packets on BPF devices.  Large packets should be
 * truncated to the size of the buffer, but unless the filter specifies a
 * smaller capture size, no more than that.
 */
static void
verify_large_packet(int fd, uint8_t *bpf_buf, size_t bpf_buf_size,
    int expected_payload_len)
{
	const char START_CHAR = 'X';
	const char FILL_CHAR = 'Y';
	const char END_CHAR = 'Z';

	struct bpf_hdr bh;
	const size_t bpf_hdr_len_aligned = BPF_WORDALIGN(sizeof(struct bpf_hdr));
	const size_t ip_udp_hdr_len = sizeof(struct ip) + sizeof(struct udphdr);
	const size_t payload_offset = bpf_hdr_len_aligned + ip_udp_hdr_len;
	const size_t expected_caplen = bpf_buf_size - bpf_hdr_len_aligned;
	const size_t expected_bpf_datalen = ip_udp_hdr_len + expected_payload_len;

	if (read(fd, bpf_buf, bpf_buf_size) != (ssize_t)bpf_buf_size)
		e(0);

	memcpy(&bh, bpf_buf, sizeof(bh));

	if (bh.bh_hdrlen != bpf_hdr_len_aligned)
		e(0);
	if (bh.bh_caplen != expected_caplen)
		e(0);
	if (bh.bh_datalen != expected_bpf_datalen)
		e(0);

	if (bpf_buf[payload_offset] != START_CHAR)
		e(0);
	if (bpf_buf[bpf_buf_size - 2] != FILL_CHAR)
		e(0);
	if (bpf_buf[bpf_buf_size - 1] != END_CHAR)
		e(0);
}

static void
test94d(void)
{
	const size_t BPF_BUFFER_SIZE = 32768;
	const int UDP_PAYLOAD_LEN = 65000;
	const int SET_FILTER = 1;
	const int SEQUENCE_NUMBER = 1;
	const char FILL_CHAR = 'Y';
	const char START_CHAR = 'X';
	const char END_CHAR = 'Z';

	int fd, fd2, fd3;
	uint8_t *buf;
	subtest = 4;

	size_t size = test94_setup(&fd, &fd2, &fd3, &buf, BPF_BUFFER_SIZE,
	    SET_FILTER);
	if (size != BPF_BUFFER_SIZE)
		e(0);

	int sndbuf_len = UDP_PAYLOAD_LEN;
	if (setsockopt(fd2, SOL_SOCKET, SO_SNDBUF, &sndbuf_len,
	    sizeof(sndbuf_len)) != 0)
		e(0);

	uint8_t *udp_payload = malloc(UDP_PAYLOAD_LEN);
	if (udp_payload == NULL)
		e(0);

	memset(udp_payload, FILL_CHAR, UDP_PAYLOAD_LEN);
	udp_payload[0] = START_CHAR;

	const size_t bpf_hdr_len_aligned = BPF_WORDALIGN(sizeof(struct bpf_hdr));
	const size_t ip_udp_hdr_len = sizeof(struct ip) + sizeof(struct udphdr);
	const size_t caplen = size - bpf_hdr_len_aligned;
	const size_t last_captured_payload_index = caplen - ip_udp_hdr_len - 1;
	udp_payload[last_captured_payload_index] = END_CHAR;

	if (write(fd2, udp_payload, UDP_PAYLOAD_LEN) != UDP_PAYLOAD_LEN)
		e(0);

	verify_large_packet(fd, buf, size, UDP_PAYLOAD_LEN);

	test94_add_random(fd2, buf, size, SEQUENCE_NUMBER);

	if (write(fd2, udp_payload, UDP_PAYLOAD_LEN) != UDP_PAYLOAD_LEN)
		e(0);

	ssize_t len = read(fd, buf, size);
	if (len <= 0 || len >= (ssize_t)size * 3 / 4)
		e(0);
	if (test94_check(buf, len, SEQUENCE_NUMBER, SET_FILTER, NULL,
	    NULL) != 2)
		e(0);

	verify_large_packet(fd, buf, size, UDP_PAYLOAD_LEN);

	free(udp_payload);
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
check(int condition)
{
	if (!condition) {
		e(0);
	}
}

static void
get_bpf_stats(int fd, struct bpf_stat *bs)
{
	check(ioctl(fd, BIOCGSTATS, bs) == 0);
}

static void
flush_bpf(int fd)
{
	check(ioctl(fd, BIOCFLUSH) == 0);
}

static void
exchange_char(int write_fd, int read_fd, char ch)
{
	char c;
	check(write(write_fd, &ch, 1) == 1);
	check(read(read_fd, &c, 1) == 1);
	check(c == ch);
}

static void
test94_comm(int fd, int fd2, int fd3, int filtered)
{
	struct bpf_stat bs;

	exchange_char(fd2, fd3, 'A');

	get_bpf_stats(fd, &bs);
	check(bs.bs_recv != 0);
	check(bs.bs_capt != 0);

	flush_bpf(fd);

	exchange_char(fd3, fd2, 'B');

	get_bpf_stats(fd, &bs);
	check(bs.bs_recv != 0);

	if (filtered) {
		check(bs.bs_capt == 0);
		check(bs.bs_drop == 0);
	} else {
		check(bs.bs_capt != 0);
	}

	flush_bpf(fd);
}

/*
 * Test filter installation and mechanics.
 */
static void
set_bpf_filter(int fd, struct bpf_insn *insns, size_t len)
{
	struct bpf_program bf;

	memset(&bf, 0, sizeof(bf));
	bf.bf_len = len;
	bf.bf_insns = insns;
	if (ioctl(fd, BIOCSETF, &bf) != 0)
		e(0);
}

static void
test_invalid_filters(int fd)
{
	struct bpf_program bf;

	memset(&bf, 0, sizeof(bf));
	bf.bf_len = BPF_MAXINSNS + 1;
	bf.bf_insns = NULL;
	if (ioctl(fd, BIOCSETF, &bf) != -1)
		e(0);
	if (errno != EINVAL)
		e(0);

	memset(&bf, 0, sizeof(bf));
	bf.bf_len = __arraycount(test94_filter) - 1;
	bf.bf_insns = test94_filter;
	if (ioctl(fd, BIOCSETF, &bf) != -1)
		e(0);
	if (errno != EINVAL)
		e(0);
}

static void
test_filter_installation(int fd, int fd2, int fd3)
{
	const size_t filter_len = __arraycount(test94_filter);

	test94_comm(fd, fd2, fd3, 0 /*filtered*/);

	set_bpf_filter(fd, test94_filter, filter_len);
	test94_comm(fd, fd2, fd3, 1 /*filtered*/);

	set_bpf_filter(fd, NULL, 0);
	test94_comm(fd, fd2, fd3, 0 /*filtered*/);

	set_bpf_filter(fd, NULL, 0);
	test94_comm(fd, fd2, fd3, 0 /*filtered*/);
}

struct capture_test_params {
	uint32_t cap_len;
	uint32_t data_len;
};

static void
run_capture_test_case(int fd, int fd2, uint8_t *buf, size_t size, size_t plen,
    int start_seq, const struct capture_test_params params[4])
{
	uint32_t caplen[4];
	uint32_t datalen[4];
	ssize_t len;

	for (int i = 0; i < 4; i++) {
		size_t payload_len = params[i].data_len - plen;
		test94_add_specific(fd2, buf, payload_len, start_seq + i);
		caplen[i] = params[i].cap_len;
		datalen[i] = params[i].data_len;
	}

	memset(buf, 0, size);
	len = read(fd, buf, size);
	if (test94_check(buf, len, start_seq, 1, caplen, datalen) !=
	    (uint32_t)start_seq + 4)
		e(0);
}

static void
test_aligned_unaligned_captures(int fd, int fd2, int fd3, uint8_t *buf,
    size_t size)
{
	size_t plen = sizeof(struct ip) + sizeof(struct udphdr) + sizeof(uint32_t);
	if (BPF_WORDALIGN(plen) != plen) e(0);
	size_t alen = BPF_WORDALIGN(plen + 1);
	if (alen - 2 <= plen + 1) e(0);

	const size_t filter_len = __arraycount(test94_filter);
	struct bpf_insn *last_filter_insn = &test94_filter[filter_len - 1];

	last_filter_insn->k = alen;
	set_bpf_filter(fd, test94_filter, filter_len);
	test94_comm(fd, fd2, fd3, 1 /*filtered*/);

	const struct capture_test_params aligned_params[4] = {
		{ alen, alen + 1 },
		{ alen, alen },
		{ alen, alen + 3 },
		{ alen - 1, alen - 1 }
	};
	run_capture_test_case(fd, fd2, buf, size, plen, 1, aligned_params);

	last_filter_insn->k = alen + 1;
	set_bpf_filter(fd, test94_filter, filter_len);

	const struct capture_test_params unaligned_params[4] = {
		{ alen + 1, alen + 2 },
		{ alen + 1, alen + 1 },
		{ alen + 1, alen + 9 },
		{ alen, alen }
	};
	run_capture_test_case(fd, fd2, buf, size, plen, 5, unaligned_params);
}

static void
test_single_byte_capture(int fd, int fd2, uint8_t *buf, size_t size)
{
	struct bpf_hdr bh;
	ssize_t len;
	size_t off;
	const size_t filter_len = __arraycount(test94_filter);
	const size_t plen = sizeof(struct ip) + sizeof(struct udphdr) + sizeof(uint32_t);

	test94_filter[filter_len - 1].k = 1;
	set_bpf_filter(fd, test94_filter, filter_len);

	test94_add_random(fd2, buf, size, 9);
	test94_add_random(fd2, buf, size, 10);
	test94_add_random(fd2, buf, size, 11);

	memset(buf, 0, size);
	len = read(fd, buf, size);
	if (len <= 0)
		e(0);

	off = 0;
	for (int i = 0; i < 3; i++) {
		if ((size_t)len - off < sizeof(bh)) e(0);
		memcpy(&bh, &buf[off], sizeof(bh));

		if (bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) e(0);
		if (bh.bh_caplen != 1) e(0);
		if (bh.bh_datalen < plen) e(0);
		if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh))) e(0);

		off += bh.bh_hdrlen;

		if (off >= (size_t)len) e(0);
		if (buf[off] != 0x45) e(0);

		off += BPF_WORDALIGN(bh.bh_caplen);
	}
	if (off != (size_t)len) e(0);
}

static void
test_zero_byte_capture(int fd, int fd2, uint8_t *buf, size_t size)
{
	struct bpf_stat bs;
	const size_t filter_len = __arraycount(test94_filter);

	test94_filter[filter_len - 1].k = 0;
	set_bpf_filter(fd, test94_filter, filter_len);

	test94_add_random(fd2, buf, size, 12);
	test94_add_random(fd2, buf, size, 13);
	test94_add_random(fd2, buf, size, 14);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_recv < 3) e(0);
	if (bs.bs_capt != 0) e(0);
	if (bs.bs_drop != 0) e(0);
}

static void
test94e(void)
{
	uint8_t *buf;
	size_t size;
	int fd, fd2, fd3, val;

	subtest = 5;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0 /*size*/,
	    0 /*set_filter*/);

	val = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &val) != 0) e(0);

	test_invalid_filters(fd);
	test_filter_installation(fd, fd2, fd3);
	test_aligned_unaligned_captures(fd, fd2, fd3, buf, size);
	test_single_byte_capture(fd, fd2, buf, size);
	test_zero_byte_capture(fd, fd2, buf, size);

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
	const uint8_t *data = buf;

	while (len > 1) {
		sum += ((uint16_t)data[0] << 8) | data[1];
		data += 2;
		len -= 2;
	}

	if (len == 1) {
		sum += (uint16_t)data[0] << 8;
	}

	while (sum > UINT16_MAX) {
		sum = (sum & UINT16_MAX) + (sum >> 16);
	}

	return ~(uint16_t)sum;
}

/*
 * Set up UDP headers for a packet.  The packet uses IPv4 unless 'v6' is set,
 * in which case IPv6 is used.  The given buffer must be large enough to
 * contain the headers and the (to be appended) data.  The function returns the
 * offset into the buffer to the data portion of the packet.
 */
static size_t
test94_make_pkt(uint8_t * buf, size_t len, int v6)
{
	size_t off;

	if (!v6) {
		const struct ip ip_header = {
			.ip_v = IPVERSION,
			.ip_hl = sizeof(struct ip) >> 2,
			.ip_len = htons(sizeof(struct ip) + sizeof(struct udphdr) + len),
			.ip_ttl = 255,
			.ip_p = IPPROTO_UDP,
			.ip_src.s_addr = htonl(INADDR_LOOPBACK),
			.ip_dst.s_addr = htonl(INADDR_LOOPBACK),
			.ip_sum = 0
		};

		memcpy(buf, &ip_header, sizeof(ip_header));

		uint16_t checksum = test94_cksum(buf, sizeof(ip_header));
		((struct ip *)buf)->ip_sum = htons(checksum);

		if (test94_cksum(buf, sizeof(ip_header)) != 0) {
			e(0);
		}

		off = sizeof(ip_header);
	} else {
		const struct ip6_hdr ip6_header = {
			.ip6_vfc = IPV6_VERSION,
			.ip6_plen = htons(sizeof(struct udphdr) + len),
			.ip6_nxt = IPPROTO_UDP,
			.ip6_hlim = 255,
			.ip6_src = in6addr_loopback,
			.ip6_dst = in6addr_loopback
		};

		memcpy(buf, &ip6_header, sizeof(ip6_header));
		off = sizeof(ip6_header);
	}

	const struct udphdr udp_header = {
		.uh_sport = htons(TEST_PORT_A),
		.uh_dport = htons(TEST_PORT_B),
		.uh_ulen = htons(sizeof(struct udphdr) + len),
		.uh_sum = 0
	};

	memcpy(buf + off, &udp_header, sizeof(udp_header));

	return off + sizeof(udp_header);
}

/*
 * Test sending packets by writing to a BPF device.
 */
#define TEST_BUF_SIZE (UINT16_MAX + 1)
#define SIMPLE_PACKET_PAYLOAD "Hello!"
#define SIMPLE_PACKET_PAYLOAD_SIZE (sizeof(SIMPLE_PACKET_PAYLOAD) - 1)
#define LARGE_PACKET_PAYLOAD_SIZE 12345
#define PAYLOAD_PRIME_MODULO 251

static void
check_bpf_is_writable(int fd)
{
	fd_set fds;
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, NULL, &fds, NULL, NULL) != 1)
		e(0);
	if (!FD_ISSET(fd, &fds))
		e(0);
}

static unsigned int
get_loopback_mtu(int sock_fd)
{
	struct ifreq ifr;
	memset(&ifr, 0, sizeof(ifr));
	strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));

	if (ioctl(sock_fd, SIOCGIFMTU, &ifr) != 0)
		e(0);

	return ifr.ifr_mtu;
}

static void
test_write_size_limits(int fd, unsigned int mtu, const uint8_t *buf)
{
	for (unsigned int i = TEST_BUF_SIZE; i > mtu; i--) {
		if (write(fd, buf, i) != -1)
			e(0);
		if (errno != EMSGSIZE)
			e(0);
	}

	if (write(fd, buf, mtu) != (ssize_t)mtu)
		e(0);

	if (write(fd, buf, 0) != 0)
		e(0);
}

static void
test_simple_packet_transmission(int bpf_fd, int sock_fd, uint8_t *buf,
    unsigned int mtu)
{
	size_t payload_len = SIMPLE_PACKET_PAYLOAD_SIZE;
	size_t header_len = test94_make_pkt(buf, payload_len, 0);
	memcpy(buf + header_len, SIMPLE_PACKET_PAYLOAD, payload_len);

	if (write(bpf_fd, buf, header_len + payload_len) !=
	    (ssize_t)(header_len + payload_len))
		e(0);

	memset(buf, 0, mtu);
	if (read(sock_fd, buf, mtu) != (ssize_t)payload_len)
		e(0);
	if (memcmp(buf, SIMPLE_PACKET_PAYLOAD, payload_len) != 0)
		e(0);
}

static void
verify_large_packet_payload(const uint8_t *buf)
{
	for (unsigned int i = 0; i < LARGE_PACKET_PAYLOAD_SIZE; i++) {
		if (buf[i] != 1 + (i % PAYLOAD_PRIME_MODULO))
			e(0);
	}
}

static void
test_feedback_mode(int bpf_fd, int sock_fd, uint8_t *buf)
{
	unsigned int uval = 1;
	if (ioctl(bpf_fd, BIOCSFEEDBACK, &uval) != 0)
		e(0);

	size_t payload_len = LARGE_PACKET_PAYLOAD_SIZE;
	size_t header_len = test94_make_pkt(buf, payload_len, 0);
	for (unsigned int i = 0; i < payload_len; i++)
		buf[header_len + i] = 1 + (i % PAYLOAD_PRIME_MODULO);

	if (write(bpf_fd, buf, header_len + payload_len) !=
	    (ssize_t)(header_len + payload_len))
		e(0);

	memset(buf, 0, UINT16_MAX);
	if (recv(sock_fd, buf, UINT16_MAX, 0) != (ssize_t)payload_len)
		e(0);
	verify_large_packet_payload(buf);

	memset(buf, 0, UINT16_MAX);
	if (recv(sock_fd, buf, UINT16_MAX, MSG_DONTWAIT) !=
	    (ssize_t)payload_len)
		e(0);
	verify_large_packet_payload(buf);

	if (recv(sock_fd, buf, UINT16_MAX, MSG_DONTWAIT) != -1)
		e(0);
	if (errno != EWOULDBLOCK)
		e(0);
}

static void
check_bpf_stats(int fd)
{
	struct bpf_stat bs;
	if (ioctl(fd, BIOCGSTATS, &bs) != 0)
		e(0);
	if (bs.bs_capt != 2)
		e(0);
}

static void
test94f(void)
{
	uint8_t *buf = NULL;
	unsigned int mtu;
	int fd, fd2, fd3;

	subtest = 6;

	(void)test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);

	check_bpf_is_writable(fd);

	mtu = get_loopback_mtu(fd2);

	uint8_t *new_buf = realloc(buf, TEST_BUF_SIZE);
	if (new_buf == NULL) {
		e(0);
	}
	buf = new_buf;

	memset(buf, 0, TEST_BUF_SIZE);

	test_write_size_limits(fd, mtu, buf);

	test_simple_packet_transmission(fd, fd3, buf, mtu);

	test_feedback_mode(fd, fd3, buf);

	check_bpf_stats(fd);

	check_bpf_is_writable(fd);

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
	int result = -1;

	subtest = 7;

	fd = open(_PATH_BPF, O_RDWR);
	if (fd < 0) {
		goto cleanup;
	}

	if (ioctl(fd, BIOCGBLEN, &size) != 0 || size < 1024 || size > BPF_MAXBUFSIZE) {
		goto cleanup;
	}

	buf = malloc(size);
	if (buf == NULL) {
		goto cleanup;
	}

	if (read(fd, buf, size) != -1 || errno != EINVAL) {
		goto cleanup;
	}

	if (write(fd, buf, size) != -1 || errno != EINVAL) {
		goto cleanup;
	}

	FD_ZERO(&rfds);
	FD_SET(fd, &rfds);
	FD_ZERO(&wfds);
	FD_SET(fd, &wfds);

	if (select(fd + 1, &rfds, &wfds, NULL, NULL) != 2) {
		goto cleanup;
	}

	if (!FD_ISSET(fd, &rfds) || !FD_ISSET(fd, &wfds)) {
		goto cleanup;
	}

	if (close(fd) == 0) {
		fd = -1;
		result = 0;
	}

cleanup:
	free(buf);
	if (fd >= 0) {
		(void)close(fd);
	}

	if (result != 0) {
		e(0);
	}
}

/*
 * Test various IOCTL calls.  Several of these tests are rather superficial,
 * because we would need a real interface, rather than the loopback device, to
 * test their functionality properly.  Also note that we skip various checks
 * performed as part of the earlier subtests.
 */
static void
check_ioctl_success(int fd, unsigned long request, void *arg)
{
	if (ioctl(fd, request, arg) != 0)
		e(0);
}

static void
check_ioctl_failure(int fd, unsigned long request, void *arg, int err)
{
	if (ioctl(fd, request, arg) != -1)
		e(0);
	if (errno != err)
		e(0);
}

static void
test_buffer_len(int ufd, int cfd, size_t configured_size)
{
	unsigned int uval;

	uval = 1;
	check_ioctl_success(ufd, BIOCSBLEN, &uval);
	check_ioctl_success(ufd, BIOCGBLEN, &uval);
	if (uval < sizeof(struct bpf_hdr) || uval > BPF_MAXBUFSIZE)
		e(0);

	uval = (unsigned int)-1;
	check_ioctl_success(ufd, BIOCSBLEN, &uval);
	check_ioctl_success(ufd, BIOCGBLEN, &uval);
	if (uval < sizeof(struct bpf_hdr) || uval > BPF_MAXBUFSIZE)
		e(0);

	uval = 0;
	check_ioctl_success(ufd, BIOCSBLEN, &uval);
	check_ioctl_success(ufd, BIOCGBLEN, &uval);
	if (uval < sizeof(struct bpf_hdr) || uval > BPF_MAXBUFSIZE)
		e(0);

	uval = 1024;
	check_ioctl_success(ufd, BIOCSBLEN, &uval);
	check_ioctl_success(ufd, BIOCGBLEN, &uval);
	if (uval != 1024)
		e(0);

	check_ioctl_failure(cfd, BIOCSBLEN, &uval, EINVAL);

	check_ioctl_success(cfd, BIOCGBLEN, &uval);
	if (uval != configured_size)
		e(0);
}

static void
test_stats_and_flush(int ufd, int cfd, int fd2, uint8_t *buf, size_t size)
{
	struct bpf_stat bs;
	int val;
	unsigned int uval;

	uval = 1;
	check_ioctl_success(cfd, BIOCIMMEDIATE, &uval);

	test94_fill_exact(fd2, buf, size, 1);
	test94_fill_exact(fd2, buf, size, 1);
	test94_fill_exact(fd2, buf, size, 1);

	check_ioctl_success(cfd, BIOCGSTATS, &bs);
	if (bs.bs_recv == 0 || bs.bs_drop == 0 || bs.bs_capt == 0)
		e(0);

	check_ioctl_success(cfd, BIOCGSTATS, &bs);
	if (bs.bs_recv == 0 || bs.bs_drop == 0 || bs.bs_capt == 0)
		e(0);

	check_ioctl_success(cfd, FIONREAD, &val);
	if (val == 0)
		e(0);

	check_ioctl_success(cfd, BIOCFLUSH, NULL);

	check_ioctl_success(cfd, BIOCGSTATS, &bs);
	if (bs.bs_drop != 0 || bs.bs_capt != 0)
		e(0);

	check_ioctl_success(cfd, FIONREAD, &val);
	if (val != 0)
		e(0);

	check_ioctl_success(ufd, BIOCFLUSH, NULL);
	check_ioctl_success(ufd, BIOCGSTATS, &bs);
	if (bs.bs_recv != 0 || bs.bs_drop != 0 || bs.bs_capt != 0)
		e(0);
}

static void
test_promisc_and_get_dlt(int ufd, int cfd)
{
	unsigned int uval;

	check_ioctl_failure(ufd, BIOCPROMISC, NULL, EINVAL);
	check_ioctl_success(cfd, BIOCPROMISC, NULL);

	check_ioctl_failure(ufd, BIOCGDLT, &uval, EINVAL);
}

static void
test_if_management(int ufd, int cfd)
{
	struct ifreq ifr;

	check_ioctl_failure(ufd, BIOCGETIF, &ifr, EINVAL);

	memset(&ifr, 'X', sizeof(ifr));
	check_ioctl_success(cfd, BIOCGETIF, &ifr);
	if (strcmp(ifr.ifr_name, LOOPBACK_IFNAME) != 0)
		e(0);

	memset(&ifr, 0, sizeof(ifr));
	strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
	check_ioctl_failure(cfd, BIOCSETIF, &ifr, EINVAL);

	memset(&ifr, 0, sizeof(ifr));
	memset(ifr.ifr_name, 'x', sizeof(ifr.ifr_name));
	check_ioctl_failure(ufd, BIOCSETIF, &ifr, ENXIO);

	memset(&ifr, 0, sizeof(ifr));
	strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
	ifr.ifr_name[strlen(ifr.ifr_name) - 1] += 9;
	check_ioctl_failure(ufd, BIOCSETIF, &ifr, ENXIO);
}

static void
test_immediate_mode(int ufd, int cfd, int fd2, uint8_t *buf, size_t size)
{
	int val;
	unsigned int uval;

	test94_add_random(fd2, buf, size, 1);

	check_ioctl_success(cfd, FIONREAD, &val);
	if (val == 0)
		e(0);

	uval = 0;
	check_ioctl_success(cfd, BIOCIMMEDIATE, &uval);
	check_ioctl_success(cfd, FIONREAD, &val);
	if (val != 0)
		e(0);

	uval = 1;
	check_ioctl_success(cfd, BIOCIMMEDIATE, &uval);
	check_ioctl_success(cfd, FIONREAD, &val);
	if (val == 0)
		e(0);

	check_ioctl_success(cfd, BIOCFLUSH, NULL);

	uval = 1;
	check_ioctl_success(ufd, BIOCIMMEDIATE, &uval);
	uval = 0;
	check_ioctl_success(ufd, BIOCIMMEDIATE, &uval);
}

static void
test_version(int ufd)
{
	struct bpf_version bv;

	check_ioctl_success(ufd, BIOCVERSION, &bv);
	if (bv.bv_major != BPF_MAJOR_VERSION || bv.bv_minor != BPF_MINOR_VERSION)
		e(0);
}

static void
test_header_complete(int ufd)
{
	unsigned int uval;

	uval = 1;
	check_ioctl_success(ufd, BIOCGHDRCMPLT, &uval);
	if (uval != 0)
		e(0);

	uval = 2;
	check_ioctl_success(ufd, BIOCSHDRCMPLT, &uval);
	check_ioctl_success(ufd, BIOCGHDRCMPLT, &uval);
	if (uval != 1)
		e(0);

	uval = 0;
	check_ioctl_success(ufd, BIOCSHDRCMPLT, &uval);
	uval = 1;
	check_ioctl_success(ufd, BIOCGHDRCMPLT, &uval);
	if (uval != 0)
		e(0);
}

static void
test_datalink_type(int ufd, int cfd)
{
	struct bpf_dltlist bfl;
	unsigned int uval, list[2] = {0, 0};

	uval = DLT_RAW;
	check_ioctl_failure(ufd, BIOCSDLT, &uval, EINVAL);
	check_ioctl_success(cfd, BIOCSDLT, &uval);

	uval = DLT_NULL;
	check_ioctl_failure(cfd, BIOCSDLT, &uval, EINVAL);

	check_ioctl_success(cfd, BIOCGDLT, &uval);
	if (uval != DLT_RAW)
		e(0);

	memset(&bfl, 0, sizeof(bfl));
	check_ioctl_failure(ufd, BIOCGDLTLIST, &bfl, EINVAL);

	memset(&bfl, 0, sizeof(bfl));
	check_ioctl_success(cfd, BIOCGDLTLIST, &bfl);
	if (bfl.bfl_len != 1 || bfl.bfl_list != NULL)
		e(0);

	bfl.bfl_len = 2;
	check_ioctl_success(cfd, BIOCGDLTLIST, &bfl);
	if (bfl.bfl_len != 1 || bfl.bfl_list != NULL)
		e(0);

	memset(&bfl, 0, sizeof(bfl));
	bfl.bfl_list = list;
	check_ioctl_failure(cfd, BIOCGDLTLIST, &bfl, ENOMEM);
	if (list[0] != 0)
		e(0);

	memset(&bfl, 0, sizeof(bfl));
	bfl.bfl_len = 1;
	bfl.bfl_list = list;
	check_ioctl_success(cfd, BIOCGDLTLIST, &bfl);
	if (bfl.bfl_len != 1 || bfl.bfl_list != list || list[0] != DLT_RAW ||
	    list[1] != 0)
		e(0);

	memset(&bfl, 0, sizeof(bfl));
	memset(list, 0, sizeof(list));
	bfl.bfl_len = 2;
	bfl.bfl_list = list;
	check_ioctl_success(cfd, BIOCGDLTLIST, &bfl);
	if (bfl.bfl_len != 1 || bfl.bfl_list != list || list[0] != DLT_RAW ||
	    list[1] != 0)
		e(0);
}

static void
test_see_sent(int ufd, int cfd, int fd2, uint8_t *buf, size_t size)
{
	struct bpf_stat bs;
	unsigned int uval;

	uval = 0;
	check_ioctl_success(ufd, BIOCGSEESENT, &uval);
	if (uval != 1)
		e(0);

	uval = 0;
	check_ioctl_success(ufd, BIOCSSEESENT, &uval);
	uval = 1;
	check_ioctl_success(ufd, BIOCGSEESENT, &uval);
	if (uval != 0)
		e(0);

	uval = 2;
	check_ioctl_success(ufd, BIOCSSEESENT, &uval);
	check_ioctl_success(ufd, BIOCGSEESENT, &uval);
	if (uval != 1)
		e(0);

	check_ioctl_success(cfd, BIOCGSEESENT, &uval);
	if (uval != 1)
		e(0);

	uval = 0;
	check_ioctl_success(cfd, BIOCSSEESENT, &uval);
	check_ioctl_success(cfd, BIOCFLUSH, NULL);
	test94_add_random(fd2, buf, size, 1);
	check_ioctl_success(cfd, BIOCGSTATS, &bs);
	if (bs.bs_recv != 0)
		e(0);

	uval = 1;
	check_ioctl_success(cfd, BIOCSSEESENT, &uval);
	check_ioctl_success(cfd, BIOCFLUSH, NULL);
	test94_add_random(fd2, buf, size, 1);
	check_ioctl_success(cfd, BIOCGSTATS, &bs);
	if (bs.bs_recv == 0)
		e(0);
}

static void
test_read_timeout(int ufd)
{
	struct timeval tv;

	tv.tv_sec = 99;
	tv.tv_usec = 0;
	check_ioctl_success(ufd, BIOCGRTIMEOUT, &tv);
	if (tv.tv_sec != 0 || tv.tv_usec != 0)
		e(0);

	tv.tv_usec = 1000000;
	check_ioctl_failure(ufd, BIOCSRTIMEOUT, &tv, EINVAL);
	tv.tv_usec = -1;
	check_ioctl_failure(ufd, BIOCSRTIMEOUT, &tv, EINVAL);
	tv.tv_sec = -1;
	tv.tv_usec = 0;
	check_ioctl_failure(ufd, BIOCSRTIMEOUT, &tv, EINVAL);
	tv.tv_sec = INT_MAX;
	check_ioctl_failure(ufd, BIOCSRTIMEOUT, &tv, EDOM);

	check_ioctl_success(ufd, BIOCGRTIMEOUT, &tv);
	if (tv.tv_sec != 0 || tv.tv_usec != 0)
		e(0);

	tv.tv_sec = 123;
	tv.tv_usec = 1;
	check_ioctl_success(ufd, BIOCSRTIMEOUT, &tv);
	check_ioctl_success(ufd, BIOCGRTIMEOUT, &tv);
	if (tv.tv_sec != 123 || tv.tv_usec == 0)
		e(0);

	tv.tv_sec = 0;
	tv.tv_usec = 0;
	check_ioctl_success(ufd, BIOCSRTIMEOUT, &tv);
	check_ioctl_success(ufd, BIOCGRTIMEOUT, &tv);
	if (tv.tv_sec != 0 || tv.tv_usec != 0)
		e(0);
}

static void
test_feedback_mode(int ufd)
{
	unsigned int uval;

	uval = 1;
	check_ioctl_success(ufd, BIOCGFEEDBACK, &uval);
	if (uval != 0)
		e(0);

	uval = 2;
	check_ioctl_success(ufd, BIOCSFEEDBACK, &uval);
	check_ioctl_success(ufd, BIOCGFEEDBACK, &uval);
	if (uval != 1)
		e(0);

	uval = 0;
	check_ioctl_success(ufd, BIOCSFEEDBACK, &uval);
	uval = 1;
	check_ioctl_success(ufd, BIOCGFEEDBACK, &uval);
	if (uval != 0)
		e(0);
}

static void
test94h(void)
{
	uint8_t *buf;
	size_t size;
	int cfd, ufd, fd2, fd3;

	subtest = 8;

	size = test94_setup(&cfd, &fd2, &fd3, &buf, 0, 1);

	if ((ufd = open(_PATH_BPF, O_RDWR)) < 0)
		e(0);

	test_buffer_len(ufd, cfd, size);
	test_stats_and_flush(ufd, cfd, fd2, buf, size);
	test_promisc_and_get_dlt(ufd, cfd);
	test_if_management(ufd, cfd);
	test_immediate_mode(ufd, cfd, fd2, buf, size);
	test_version(ufd);
	test_header_complete(ufd);
	test_datalink_type(ufd, cfd);
	test_see_sent(ufd, cfd, fd2, buf, size);
	test_read_timeout(ufd);
	test_feedback_mode(ufd);

	if (close(ufd) != 0)
		e(0);

	test94_cleanup(cfd, fd2, fd3, buf);
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
	subtest = 9;

	int fd = -1;
	int fd2 = -1;
	int fd3 = -1;
	uint8_t *buf = NULL;
	int close_err = 0;

	fd = open(_PATH_BPF, O_RDWR);
	if (fd < 0) {
		e(0);
		return;
	}

	unsigned int size;
	if (ioctl(fd, BIOCGBLEN, &size) != 0 || size < 1024 ||
	    size > BPF_MAXBUFSIZE) {
		e(0);
		goto cleanup;
	}

	buf = malloc(size);
	if (buf == NULL) {
		e(0);
		goto cleanup;
	}

	struct bpf_program bf = {
	    .bf_len = __arraycount(test94_filter6),
	    .bf_insns = test94_filter6,
	};
	if (ioctl(fd, BIOCSETF, &bf) != 0) {
		e(0);
		goto cleanup;
	}

	unsigned int uval = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &uval) != 0) {
		e(0);
		goto cleanup;
	}

	struct ifreq ifr;
	memset(&ifr, 0, sizeof(ifr));
	if (strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name)) >=
	    sizeof(ifr.ifr_name)) {
		e(0);
		goto cleanup;
	}
	if (ioctl(fd, BIOCSETIF, &ifr) != 0) {
		e(0);
		goto cleanup;
	}

	unsigned int dlt;
	if (ioctl(fd, BIOCGDLT, &dlt) != 0 || dlt != DLT_RAW) {
		e(0);
		goto cleanup;
	}

	fd2 = socket(AF_INET6, SOCK_DGRAM, 0);
	if (fd2 < 0) {
		e(0);
		goto cleanup;
	}

	struct sockaddr_in6 sin6A;
	memset(&sin6A, 0, sizeof(sin6A));
	sin6A.sin6_family = AF_INET6;
	sin6A.sin6_port = htons(TEST_PORT_A);
	memcpy(&sin6A.sin6_addr, &in6addr_loopback, sizeof(sin6A.sin6_addr));
	if (bind(fd2, (struct sockaddr *)&sin6A, sizeof(sin6A)) != 0) {
		e(0);
		goto cleanup;
	}

	struct sockaddr_in6 sin6B;
	memcpy(&sin6B, &sin6A, sizeof(sin6B));
	sin6B.sin6_port = htons(TEST_PORT_B);
	if (connect(fd2, (struct sockaddr *)&sin6B, sizeof(sin6B)) != 0) {
		e(0);
		goto cleanup;
	}

	fd3 = socket(AF_INET6, SOCK_DGRAM, 0);
	if (fd3 < 0) {
		e(0);
		goto cleanup;
	}
	if (bind(fd3, (struct sockaddr *)&sin6B, sizeof(sin6B)) != 0) {
		e(0);
		goto cleanup;
	}
	if (connect(fd3, (struct sockaddr *)&sin6A, sizeof(sin6A)) != 0) {
		e(0);
		goto cleanup;
	}

	uint8_t c;
	if (write(fd2, "A", 1) != 1) {
		e(0);
		goto cleanup;
	}
	if (read(fd3, &c, 1) != 1 || c != 'A') {
		e(0);
		goto cleanup;
	}

	if (write(fd3, "B", 1) != 1) {
		e(0);
		goto cleanup;
	}
	if (read(fd2, &c, 1) != 1 || c != 'B') {
		e(0);
		goto cleanup;
	}

	struct bpf_stat bs;
	if (ioctl(fd, BIOCGSTATS, &bs) != 0 || bs.bs_recv < 2 ||
	    bs.bs_capt != 1 || bs.bs_drop != 0) {
		e(0);
		goto cleanup;
	}

	memset(buf, 0, size);
	const ssize_t len = read(fd, buf, size);

	const size_t expected_hdr_len = BPF_WORDALIGN(sizeof(struct bpf_hdr));
	const size_t expected_payload_len =
	    sizeof(struct ip6_hdr) + sizeof(struct udphdr) + 1;
	const size_t expected_total_len =
	    expected_hdr_len + BPF_WORDALIGN(expected_payload_len);
	if (len != expected_total_len) {
		e(0);
		goto cleanup;
	}

	struct bpf_hdr bh;
	memcpy(&bh, buf, sizeof(bh));
	if ((bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) ||
	    bh.bh_caplen != expected_payload_len ||
	    bh.bh_datalen != bh.bh_caplen || bh.bh_hdrlen != expected_hdr_len) {
		e(0);
		goto cleanup;
	}

	const size_t payload_offset =
	    bh.bh_hdrlen + sizeof(struct ip6_hdr) + sizeof(struct udphdr);
	if (buf[payload_offset] != 'A') {
		e(0);
		goto cleanup;
	}

	const char hello_msg[] = "Hello!";
	const size_t hello_len = sizeof(hello_msg) - 1;
	size_t off = test94_make_pkt(buf, hello_len, 1);
	memcpy(buf + off, hello_msg, hello_len);

	const size_t write_len = off + hello_len;
	if (write(fd, buf, write_len) != write_len) {
		e(0);
		goto cleanup;
	}

	socklen_t socklen = sizeof(sin6A);
	if (recvfrom(fd3, buf, size, 0, (struct sockaddr *)&sin6A, &socklen) !=
	    hello_len) {
		e(0);
		goto cleanup;
	}

	if (memcmp(buf, hello_msg, hello_len) != 0 || socklen != sizeof(sin6A) ||
	    sin6A.sin6_family != AF_INET6 ||
	    sin6A.sin6_port != htons(TEST_PORT_A) ||
	    memcmp(&sin6A.sin6_addr, &in6addr_loopback,
		sizeof(sin6A.sin6_addr)) != 0) {
		e(0);
		goto cleanup;
	}

cleanup:
	free(buf);
	if (fd3 >= 0 && close(fd3) != 0)
		close_err = 1;
	if (fd2 >= 0 && close(fd2) != 0)
		close_err = 1;
	if (fd >= 0 && close(fd) != 0)
		close_err = 1;
	if (close_err)
		e(0);
}

/*
 * Test the BPF sysctl(7) interface at a basic level.
 */
#include <sys/types.h>
#include <sys/sysctl.h>
#include <net/bpf.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/ioctl.h>

#ifndef __arraycount
#define __arraycount(x) (sizeof(x) / sizeof((x)[0]))
#endif

#ifndef _PATH_BPF
#define _PATH_BPF "/dev/bpf"
#endif

#ifndef LOOPBACK_IFNAME
#define LOOPBACK_IFNAME "lo0"
#endif

extern int subtest;
extern void e(int);
extern size_t test94_setup(int *, int *, int *, uint8_t **, size_t, int);
extern unsigned int test94_fill_exact(int, uint8_t *, size_t, int);
extern void test94_cleanup(int, int, int, uint8_t *);

struct bpf_peer_exp {
	size_t exp_bufsize;
	int exp_promisc;
	enum bpf_state exp_state;
	int exp_immediate;
	int exp_hdrcmplt;
	int exp_seesent;
	u_int exp_rcount;
	int use_rcount_min;
	u_int exp_dcount;
	u_int exp_ccount;
	const char *exp_ifname;
};

static void
get_sysctl_mib_by_name(const char *name, int *mib, size_t *len,
    size_t expected_len)
{
	if (sysctlnametomib(name, mib, len) != 0)
		e(0);
	if (*len != expected_len)
		e(0);
}

static void
check_bpf_peer(const struct bpf_d_ext *bde, const struct bpf_peer_exp *exp)
{
	if (bde->bde_bufsize != exp->exp_bufsize) e(0);
	if (bde->bde_promisc != exp->exp_promisc) e(0);
	if (bde->bde_state != exp->exp_state) e(0);
	if (bde->bde_immediate != exp->exp_immediate) e(0);
	if (bde->bde_hdrcmplt != exp->exp_hdrcmplt) e(0);
	if (bde->bde_seesent != exp->exp_seesent) e(0);

	if (exp->use_rcount_min) {
		if (bde->bde_rcount < exp->exp_rcount) e(0);
	} else {
		if (bde->bde_rcount != exp->exp_rcount) e(0);
	}

	if (bde->bde_dcount != exp->exp_dcount) e(0);
	if (bde->bde_ccount != exp->exp_ccount) e(0);

	if (exp->exp_ifname[0] == '\0') {
		if (bde->bde_ifname[0] != '\0') e(0);
	} else {
		if (strcmp(bde->bde_ifname, exp->exp_ifname) != 0) e(0);
	}
}

static void
find_and_verify_pid_peer(const int *mib, size_t miblen,
    const struct bpf_peer_exp *exp)
{
	struct bpf_d_ext *bde;
	size_t buflen;
	int found = 0;
	pid_t pid = getpid();

	if (sysctl(mib, miblen, NULL, &buflen, NULL, 0) != 0) e(0);
	if (buflen == 0) e(0);

	size_t alloc_size = buflen + sizeof(*bde) * 8;
	if (alloc_size < buflen) e(0);
	bde = malloc(alloc_size);
	if (bde == NULL) e(0);

	buflen = alloc_size;
	if (sysctl(mib, miblen, bde, &buflen, NULL, 0) != 0) {
		free(bde);
		e(0);
	}
	if (buflen % sizeof(*bde) != 0) {
		free(bde);
		e(0);
	}

	for (unsigned int i = 0; i < buflen / sizeof(*bde); i++) {
		if (bde[i].bde_pid == pid) {
			check_bpf_peer(&bde[i], exp);
			found++;
		}
	}

	free(bde);
	if (found != 1) e(0);
}

static void
verify_no_pid_peer(const int *mib, size_t miblen)
{
	struct bpf_d_ext *bde;
	size_t buflen = 0;
	pid_t pid = getpid();

	if (sysctl(mib, miblen, NULL, &buflen, NULL, 0) != 0) e(0);
	if (buflen == 0) return;

	bde = malloc(buflen);
	if (bde == NULL) e(0);

	if (sysctl(mib, miblen, bde, &buflen, NULL, 0) != 0) {
		free(bde);
		e(0);
	}
	if (buflen % sizeof(*bde) != 0) {
		free(bde);
		e(0);
	}

	for (unsigned int i = 0; i < buflen / sizeof(*bde); i++) {
		if (bde[i].bde_pid == pid) {
			free(bde);
			e(0);
		}
	}
	free(bde);
}

static void
test94j(void)
{
	struct bpf_stat bs1, bs2;
	uint8_t *buf;
	int fd, fd2, fd3, val;
	int mib[5], smib[3];
	size_t len, oldlen;

	subtest = 10;

	len = __arraycount(mib);
	get_sysctl_mib_by_name("net.bpf.maxbufsize", mib, &len, 3);

	oldlen = sizeof(val);
	if (sysctl(mib, len, &val, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen != sizeof(val)) e(0);
	if (val < 1024 || val > INT_MAX / 2) e(0);

	if (sysctl(mib, len, NULL, NULL, &val, sizeof(val)) != -1) e(0);
	if (errno != EPERM) e(0);

	len = __arraycount(smib);
	get_sysctl_mib_by_name("net.bpf.stats", smib, &len, 3);
	oldlen = sizeof(bs1);
	if (sysctl(smib, len, &bs1, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen != sizeof(bs1)) e(0);

	len = __arraycount(mib);
	get_sysctl_mib_by_name("net.bpf.peers", mib, &len, 3);
	mib[len++] = sizeof(struct bpf_d_ext);
	mib[len++] = INT_MAX;

	size_t size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);
	unsigned int count = test94_fill_exact(fd2, buf, size, 0);
	test94_fill_exact(fd2, buf, size, 0);
	test94_fill_exact(fd2, buf, size, 0);
	if (write(fd3, "X", 1) != 1) e(0);

	const struct bpf_peer_exp active_exp = {
		.exp_bufsize = size,
		.exp_promisc = 0,
		.exp_state = BPF_IDLE,
		.exp_immediate = 0,
		.exp_hdrcmplt = 0,
		.exp_seesent = 1,
		.exp_rcount = count * 3 + 1,
		.use_rcount_min = 1,
		.exp_dcount = count,
		.exp_ccount = count * 3,
		.exp_ifname = LOOPBACK_IFNAME
	};
	find_and_verify_pid_peer(mib, len, &active_exp);

	if (ioctl(fd, BIOCFLUSH) != 0) e(0);
	test94_cleanup(fd, fd2, fd3, buf);

	oldlen = sizeof(bs2);
	if (sysctl(smib, __arraycount(smib), &bs2, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen != sizeof(bs2)) e(0);
	if (bs2.bs_recv < bs1.bs_recv + count * 3 + 1) e(0);
	if (bs2.bs_drop != bs1.bs_drop + count) e(0);
	if (bs2.bs_capt != bs1.bs_capt + count * 3) e(0);

	if ((fd = open(_PATH_BPF, O_RDWR)) < 0) e(0);
	unsigned int uval = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &uval) != 0) e(0);
	if (ioctl(fd, BIOCSHDRCMPLT, &uval) != 0) e(0);
	uval = 0;
	if (ioctl(fd, BIOCSSEESENT, &uval) != 0) e(0);

	const struct bpf_peer_exp idle_exp = {
		.exp_bufsize = size,
		.exp_promisc = 0,
		.exp_state = BPF_IDLE,
		.exp_immediate = 1,
		.exp_hdrcmplt = 1,
		.exp_seesent = 0,
		.exp_rcount = 0,
		.use_rcount_min = 0,
		.exp_dcount = 0,
		.exp_ccount = 0,
		.exp_ifname = ""
	};
	find_and_verify_pid_peer(mib, len, &idle_exp);

	close(fd);

	verify_no_pid_peer(mib, len);
}

/*
 * Test privileged operations as an unprivileged caller.
 */
static void
test94k_child_process(void)
{
	struct passwd *pw;
	size_t len, oldlen;
	int mib[5];
	int fd;

	errct = 0;

	pw = getpwnam(NONROOT_USER);
	if (pw == NULL) {
		e(0);
		goto out;
	}

	if (setuid(pw->pw_uid) != 0) {
		e(0);
	}

	/*
	 * Opening /dev/bpf must fail.  Note that this is a system
	 * configuration issue rather than a LWIP service issue.
	 */
	fd = open(_PATH_BPF, O_RDWR);
	if (fd != -1) {
		e(0);
		close(fd);
	} else if (errno != EACCES) {
		e(0);
	}

	/*
	 * Retrieving the net.bpf.peers list must fail, too.
	 */
	memset(mib, 0, sizeof(mib));
	len = __arraycount(mib);
	if (sysctlnametomib("net.bpf.peers", mib, &len) != 0) {
		e(0);
		goto out;
	}

	if (len != 3) {
		e(0);
		goto out;
	}

	mib[len++] = sizeof(struct bpf_d_ext);
	mib[len++] = INT_MAX;

	if (sysctl(mib, len, NULL, &oldlen, NULL, 0) != -1) {
		e(0);
	} else if (errno != EPERM) {
		e(0);
	}

out:
	exit(errct);
}

static void
test94k(void)
{
	pid_t pid;
	int status;

	subtest = 11;

	pid = fork();
	if (pid == -1) {
		e(0);
		return;
	}

	if (pid == 0) {
		test94k_child_process();
	}

	if (wait(&status) != pid) {
		e(0);
	} else if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
		e(0);
	}
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
#define PAYLOAD_MSG "Hello!"
#define PAYLOAD_SIZE (sizeof(PAYLOAD_MSG) - 1)

static struct ifaddrs *
find_suitable_ifp(struct ifaddrs *ifa)
{
	struct ifaddrs *ifp;

	for (ifp = ifa; ifp != NULL; ifp = ifp->ifa_next) {
		if ((ifp->ifa_flags & IFF_UP) && ifp->ifa_addr != NULL &&
		    ifp->ifa_addr->sa_family == AF_LINK) {
			struct if_data *ifdata =
			    (struct if_data *)ifp->ifa_data;
			if (ifdata != NULL && ifdata->ifi_type == IFT_ETHER &&
			    ifdata->ifi_link_state != LINK_STATE_DOWN) {
				return ifp;
			}
		}
	}
	return NULL;
}

static bool
find_ethernet_interface(struct ifreq *ifr, struct ether_header *ether)
{
	struct ifaddrs *ifa = NULL;
	struct ifaddrs *ifp;
	bool result = false;

	if (getifaddrs(&ifa) != 0) {
		e(0);
	}

	ifp = find_suitable_ifp(ifa);
	if (ifp != NULL) {
		struct sockaddr_dl *sdl = (struct sockaddr_dl *)ifp->ifa_addr;

		if (sdl->sdl_alen != sizeof(ether->ether_dhost)) {
			freeifaddrs(ifa);
			e(0);
		}
		strlcpy(ifr->ifr_name, ifp->ifa_name, sizeof(ifr->ifr_name));
		memcpy(ether->ether_dhost, sdl->sdl_data + sdl->sdl_nlen,
		    sdl->sdl_alen);
		result = true;
	}

	freeifaddrs(ifa);
	return result;
}

static int
setup_bpf_device(const struct ifreq *ifr)
{
	int bfd;
	unsigned int val;

	bfd = open(_PATH_BPF, O_RDWR);
	if (bfd < 0) {
		e(0);
	}

	if (ioctl(bfd, BIOCSETIF, ifr) != 0) {
		goto fail;
	}

	if (ioctl(bfd, BIOCGDLT, &val) != 0) {
		goto fail;
	}
	if (val != DLT_EN10MB) {
		goto fail;
	}

	val = 1;
	if (ioctl(bfd, BIOCSFEEDBACK, &val) != 0) {
		goto fail;
	}

	return bfd;

fail:
	close(bfd);
	e(0);
	return -1;
}

static void
create_sockaddr(struct sockaddr_storage *ss, socklen_t *sslen, int af)
{
	memset(ss, 0, sizeof(*ss));
	if (af == AF_INET6) {
		struct sockaddr_in6 *sin6 = (struct sockaddr_in6 *)ss;
		sin6->sin6_family = AF_INET6;
		sin6->sin6_port = htons(TEST_PORT_B);
		memcpy(&sin6->sin6_addr, &in6addr_loopback,
		    sizeof(sin6->sin6_addr));
		*sslen = sizeof(*sin6);
	} else {
		struct sockaddr_in *sin = (struct sockaddr_in *)ss;
		sin->sin_family = AF_INET;
		sin->sin_port = htons(TEST_PORT_B);
		sin->sin_addr.s_addr = htonl(INADDR_LOOPBACK);
		*sslen = sizeof(*sin);
	}
}

static void
perform_bpf_test(int bfd, struct ether_header *ether_hdr, int af, bool is_ipv6)
{
	int sfd = -1;
	struct sockaddr_storage ss;
	socklen_t sslen;
	uint8_t buf[sizeof(struct ether_header) + MAX(sizeof(struct ip),
	    sizeof(struct ip6_hdr)) + sizeof(struct udphdr) + PAYLOAD_SIZE];
	size_t headers_len;
	size_t packet_len;

	sfd = socket(af, SOCK_DGRAM, 0);
	if (sfd < 0) {
		e(0);
	}

	create_sockaddr(&ss, &sslen, af);
	if (bind(sfd, (struct sockaddr *)&ss, sslen) != 0) {
		goto fail;
	}

	ether_hdr->ether_type = htons(is_ipv6 ? ETHERTYPE_IPV6 : ETHERTYPE_IP);
	memcpy(buf, ether_hdr, sizeof(*ether_hdr));

	headers_len = sizeof(*ether_hdr);
	headers_len += test94_make_pkt(buf + headers_len, PAYLOAD_SIZE, is_ipv6);

	packet_len = headers_len + PAYLOAD_SIZE;
	if (packet_len > sizeof(buf)) {
		goto fail;
	}
	memcpy(buf + headers_len, PAYLOAD_MSG, PAYLOAD_SIZE);

	if (write(bfd, buf, packet_len) != (ssize_t)packet_len) {
		goto fail;
	}

	if (recv(sfd, buf, sizeof(buf), MSG_DONTWAIT) != -1) {
		goto fail;
	}
	if (errno != EWOULDBLOCK) {
		goto fail;
	}

	if (close(sfd) != 0) {
		e(0);
	}
	return;

fail:
	close(sfd);
	e(0);
}

static void
test94l(void)
{
	struct ifreq ifr;
	struct ether_header ether;
	const uint8_t ether_src[ETHER_ADDR_LEN] =
	    { 0x02, 0x00, 0x01, 0x12, 0x34, 0x56 };
	int bfd;

	subtest = 12;

	if (!get_setting_use_network()) {
		return;
	}

	memset(&ifr, 0, sizeof(ifr));
	memset(&ether, 0, sizeof(ether));

	if (!find_ethernet_interface(&ifr, &ether)) {
		return;
	}

	bfd = setup_bpf_device(&ifr);

	memcpy(ether.ether_shost, ether_src, sizeof(ether.ether_shost));

	perform_bpf_test(bfd, &ether, AF_INET, false);
	perform_bpf_test(bfd, &ether, AF_INET6, true);

	if (close(bfd) != 0) {
		e(0);
	}
}

/*
 * Test program for LWIP BPF.
 */
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

void start(int value);
void quit(void);

void test94a(void);
void test94b(void);
void test94c(void);
void test94d(void);
void test94e(void);
void test94f(void);
void test94g(void);
void test94h(void);
void test94i(void);
void test94j(void);
void test94k(void);
void test94l(void);

#ifndef ITERATIONS
#define ITERATIONS 1000
#endif

enum {
    START_VALUE = 94,
    DEFAULT_MASK = 0xFFF,
    NUM_TESTS = 12
};

typedef void (*TestFunc)(void);

static const TestFunc TEST_FUNCTIONS[NUM_TESTS] = {
    test94a, test94b, test94c, test94d,
    test94e, test94f, test94g, test94h,
    test94i, test94j, test94k, test94l
};

int main(int argc, char **argv) {
    start(START_VALUE);

    time_t current_time = time(NULL);
    if (current_time == (time_t)-1) {
        perror("time");
        return EXIT_FAILURE;
    }
    srand48(current_time);

    unsigned long m = DEFAULT_MASK;
    if (argc > 2) {
        fprintf(stderr, "Usage: %s [mask]\n", argv[0]);
        return EXIT_FAILURE;
    }
    if (argc == 2) {
        char *endptr;
        errno = 0;
        m = strtoul(argv[1], &endptr, 0);

        if (errno != 0 || *endptr != '\0' || endptr == argv[1]) {
            fprintf(stderr, "Error: Invalid mask value: '%s'\n", argv[1]);
            return EXIT_FAILURE;
        }
    }

    for (int i = 0; i < ITERATIONS; i++) {
        for (size_t j = 0; j < NUM_TESTS; j++) {
            if (m & (1UL << j)) {
                TEST_FUNCTIONS[j]();
            }
        }
    }

    quit();
    return EXIT_SUCCESS;
}
