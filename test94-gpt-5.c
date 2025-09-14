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
static void test94_signal(int sig)
{
    if (sig != SIGUSR1) {
        e(0);
    }
    ++got_signal;
}

/*
 * Send UDP packets on the given socket 'fd' so as to fill up a BPF store
 * buffer of size 'size' exactly.  The provided buffer 'buf' may be used for
 * packet generation and is at least of 'size' bytes.  Return the number of
 * packets sent.
 */
static uint32_t
test94_fill_exact(int fd, uint8_t *buf, size_t size, uint32_t seq)
{
	size_t header_len = BPF_WORDALIGN(sizeof(struct bpf_hdr)) + sizeof(struct ip) + sizeof(struct udphdr) + sizeof(seq);
	size_t len = 16;

	if (fd < 0 || buf == NULL) e(0);

	while (len <= header_len) {
		len <<= 1;
	}
	if (len > size) e(0);

	header_len = BPF_WORDALIGN(header_len - sizeof(seq));
	{
		size_t payload_len = len - header_len;

		if (payload_len == 0) e(0);
		if ((size % len) != 0) e(0);

		for (size_t remaining = size; remaining > 0; remaining -= len, seq++) {
			memset(buf, 'Y', payload_len);
			if (payload_len > sizeof(seq)) {
				buf[sizeof(seq)] = 'X';
			}
			buf[payload_len - 1] = 'Z';
			memcpy(buf, &seq, sizeof(seq));

			if ((size_t)write(fd, buf, payload_len) != payload_len) e(0);
		}
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
test94_fill_random(int fd, uint8_t *buf, size_t size)
{
	size_t hdrlen = BPF_WORDALIGN(BPF_WORDALIGN(sizeof(struct bpf_hdr)) +
	    sizeof(struct ip) + sizeof(struct udphdr));
	ssize_t left;
	uint32_t seq;

	for (left = (ssize_t)size, seq = 1; left >= 0; seq++) {
		size_t max_extra = size / 10;
		size_t extra, payload_len, remaining;
		size_t total_len;

		if (max_extra == 0) {
			max_extra = 1;
		}
		extra = (size_t)(lrand48() % max_extra);
		payload_len = sizeof(seq) + extra;

		memset(buf, 'Y', payload_len);
		if (payload_len > sizeof(seq)) {
			buf[sizeof(seq)] = 'X';
		}
		buf[payload_len - 1] = 'Z';
		memcpy(buf, &seq, sizeof(seq));

		remaining = payload_len;
		while (remaining > 0) {
			ssize_t w = write(fd, buf + (payload_len - remaining), remaining);
			if (w < 0) {
				if (errno == EINTR) {
					continue;
				}
				e(0);
				break;
			}
			if (w == 0) {
				e(0);
				break;
			}
			remaining -= (size_t)w;
		}

		total_len = hdrlen + payload_len;
		left -= (ssize_t)BPF_WORDALIGN(total_len);
	}
}

/*
 * Send a UDP packet with a specific size of 'size' bytes and sequence number
 * 'seq' on socket 'fd', using 'buf' as scratch buffer.
 */
static void
test94_add_specific(int fd, uint8_t *buf, size_t size, uint32_t seq)
{
    if (buf == NULL) {
        e(0);
        return;
    }

    if (size > SIZE_MAX - sizeof(seq)) {
        e(0);
        return;
    }

    size_t total_size = size + sizeof(seq);

    memset(buf, 'Y', total_size);
    if (total_size > sizeof(seq)) {
        buf[sizeof(seq)] = 'X';
    }
    buf[total_size - 1] = 'Z';
    memcpy(buf, &seq, sizeof(seq));

    ssize_t written = write(fd, buf, total_size);
    if (written < 0 || (size_t)written != total_size) {
        e(0);
    }
}

/*
 * Send a randomly sized, relatively small UDP packet on the given socket 'fd',
 * using sequence number 'seq'.  The buffer 'buf' may be used as scratch buffer
 * which is at most 'size' bytes--the same size as the total BPF buffer.
 */
static void
test94_add_random(int fd, uint8_t *buf, size_t size, uint32_t seq)
{
    size_t max_len = size / 10;
    size_t rand_len = 0;

    if (max_len > 0) {
        unsigned long r = (unsigned long)lrand48();
        rand_len = (size_t)(r % max_len);
    }

    test94_add_specific(fd, buf, rand_len, seq);
}

/*
 * Check whether the packet in 'buf' of 'caplen' captured bytes out of
 * 'datalen' data bytes is one we sent.  If so, return an offset to the packet
 * data.  If not, return a negative value.
 */
static ssize_t
test94_check_pkt(uint8_t *buf, ssize_t caplen, ssize_t datalen)
{
	struct ip ip;
	struct udphdr uh;
	const size_t ip_len = sizeof(ip);
	const size_t udp_len = sizeof(uh);

	if (buf == NULL)
		return -1;

	if (caplen < 0 || datalen < 0)
		return -1;

	if ((size_t)caplen < ip_len)
		return -1;

	memcpy(&ip, buf, ip_len);

	if (ip.ip_v != IPVERSION)
		return -1;
	if (ip.ip_hl != (ip_len >> 2))
		return -1;
	if (ip.ip_p != IPPROTO_UDP)
		return -1;

	if ((size_t)(caplen - (ssize_t)ip_len) < udp_len)
		return -1;

	memcpy(&uh, buf + ip_len, udp_len);

	if (uh.uh_sport != htons(TEST_PORT_A))
		return -1;
	if (uh.uh_dport != htons(TEST_PORT_B))
		return -1;

	if ((datalen - (ssize_t)ip_len) != (ssize_t)ntohs(uh.uh_ulen))
		e(0);

	return (ssize_t)(ip_len + udp_len);
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

	while (len > 0) {
		size_t expected_hdrlen = BPF_WORDALIGN(sizeof(bh));
		if (len < (ssize_t)expected_hdrlen) e(0);

		memcpy(&bh, buf, sizeof(bh));

		if (bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) e(0);

		if (caplen != NULL) {
			if (bh.bh_caplen != *caplen) e(0);
			if (bh.bh_datalen != *datalen) e(0);
			caplen++;
			datalen++;
		} else {
			if (bh.bh_datalen != bh.bh_caplen) e(0);
		}

		if (bh.bh_hdrlen != expected_hdrlen) e(0);

		{
			size_t aligned_caplen = BPF_WORDALIGN(bh.bh_caplen);
			if ((size_t)bh.bh_hdrlen + aligned_caplen > (size_t)len) e(0);

			buf += bh.bh_hdrlen;
			len -= bh.bh_hdrlen;

			off = test94_check_pkt(buf, bh.bh_caplen, bh.bh_datalen);
			if (off < 0) {
				if (filtered) e(0);
				buf += aligned_caplen;
				len -= aligned_caplen;
				continue;
			}

			{
				size_t offz = (size_t)off;
				if (offz > bh.bh_caplen || (size_t)bh.bh_caplen - offz < sizeof(nseq)) e(0);

				memcpy(&nseq, buf + offz, sizeof(nseq));
				if (nseq != seq++) e(0);

				offz += sizeof(nseq);
				if (offz < bh.bh_caplen) {
					uint32_t dminus1 = bh.bh_datalen - 1;

					if (offz < (size_t)dminus1) {
						if (buf[offz] != 'X') e(0);
						offz++;
						{
							size_t limit = dminus1;
							while (offz < bh.bh_caplen && offz < limit) {
								if (buf[offz] != 'Y') e(0);
								offz++;
							}
						}
					}
					if (offz < bh.bh_caplen && offz == (size_t)dminus1) {
						if (buf[offz] != 'Z') e(0);
					}
				}
			}

			buf += aligned_caplen;
			len -= aligned_caplen;
		}
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
test94_setup(int *fd, int *fd2, int *fd3, uint8_t **buf, unsigned int size,
    int set_filter)
{
    struct sockaddr_in sinA, sinB;
    struct ifreq ifr;
    struct bpf_program bf;
    unsigned int dlt;

    if (fd == NULL || fd2 == NULL || fd3 == NULL || buf == NULL) e(0);

    *fd = -1;
    *fd2 = -1;
    *fd3 = -1;
    *buf = NULL;

    if ((*fd = open(_PATH_BPF, O_RDWR)) < 0) goto fail;

    if (size != 0 && ioctl(*fd, BIOCSBLEN, &size) != 0) goto fail;

    if (ioctl(*fd, BIOCGBLEN, &size) != 0) goto fail;
    if (size < 1024 || size > BPF_MAXBUFSIZE) goto fail;

    *buf = malloc(size);
    if (*buf == NULL) goto fail;

    if (set_filter) {
        memset(&bf, 0, sizeof(bf));
        bf.bf_len = __arraycount(test94_filter);
        bf.bf_insns = test94_filter;
        if (ioctl(*fd, BIOCSETF, &bf) != 0) goto fail;
    }

    memset(&ifr, 0, sizeof(ifr));
    if (strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name)) >= sizeof(ifr.ifr_name))
        goto fail;
    if (ioctl(*fd, BIOCSETIF, &ifr) != 0) goto fail;

    if (ioctl(*fd, BIOCGDLT, &dlt) != 0) goto fail;
    if (dlt != DLT_RAW) goto fail;

    if ((*fd2 = socket(AF_INET, SOCK_DGRAM, 0)) < 0) goto fail;

    memset(&sinA, 0, sizeof(sinA));
    sinA.sin_family = AF_INET;
    sinA.sin_port = htons(TEST_PORT_A);
    sinA.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if (bind(*fd2, (struct sockaddr *)&sinA, sizeof(sinA)) != 0) goto fail;

    memcpy(&sinB, &sinA, sizeof(sinB));
    sinB.sin_port = htons(TEST_PORT_B);
    if (connect(*fd2, (struct sockaddr *)&sinB, sizeof(sinB)) != 0) goto fail;

    if ((*fd3 = socket(AF_INET, SOCK_DGRAM, 0)) < 0) goto fail;

    if (bind(*fd3, (struct sockaddr *)&sinB, sizeof(sinB)) != 0) goto fail;

    if (connect(*fd3, (struct sockaddr *)&sinA, sizeof(sinA)) != 0) goto fail;

    return size;

fail:
    if (*fd3 >= 0) { close(*fd3); *fd3 = -1; }
    if (*fd2 >= 0) { close(*fd2); *fd2 = -1; }
    if (*fd >= 0) { close(*fd); *fd = -1; }
    if (*buf != NULL) { free(*buf); *buf = NULL; }
    e(0);
    return 0;
}

/*
 * Clean up resources allocated by test94_setup().
 */
static void close_checked(int fd)
{
	if (close(fd) != 0) e(0);
}

static void
test94_cleanup(int fd, int fd2, int fd3, uint8_t * buf)
{
	close_checked(fd3);
	close_checked(fd2);
	free(buf);
	close_checked(fd);
}

/*
 * Test reading packets from a BPF device, using regular mode.
 */
static void expect_select_empty_now(int fd)
{
	struct timeval tv;
	fd_set fds;

	tv.tv_sec = 0;
	tv.tv_usec = 0;
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv) != 0) e(0);
	if (FD_ISSET(fd, &fds)) e(0);
}

static void expect_select_ready_blocking(int fd)
{
	fd_set fds;

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);
}

static int get_fionread(int fd)
{
	int bytes;

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);
	return bytes;
}

static void wait_child_ok(pid_t pid)
{
	int status;

	if (waitpid(pid, &status, 0) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);
}

typedef struct {
	int fd;
	uint8_t *buf;
	size_t size;
} IOArgs;

typedef struct {
	int fd;
	uint8_t *buf;
	size_t size;
	uint32_t seq;
} AddArgs;

static void child_fill_random_delay(void *arg)
{
	IOArgs *a = (IOArgs *)arg;

	usleep(SLEEP_TIME);
	test94_fill_random(a->fd, a->buf, a->size);
}

static void child_add_random_delay_with_signal(void *arg)
{
	AddArgs *a = (AddArgs *)arg;

	signal(SIGUSR1, test94_signal);

	usleep(SLEEP_TIME);

	test94_add_random(a->fd, a->buf, a->size, a->seq);

	usleep(SLEEP_TIME);

	if (got_signal != 0) e(0);
	pause();
	if (got_signal != 1) e(0);
}

static void child_read_expect_eintr(void *arg)
{
	IOArgs *a = (IOArgs *)arg;

	signal(SIGUSR1, test94_signal);

	if (read(a->fd, a->buf, a->size) != -1) e(0);
	if (errno != EINTR) e(0);

	if (got_signal != 1) e(0);
}

static void child_usleep_add_seq(void *arg)
{
	AddArgs *a = (AddArgs *)arg;

	usleep(SLEEP_TIME);

	test94_add_random(a->fd, a->buf, a->size, a->seq);
}

static pid_t spawn_child(void (*fn)(void *), void *arg)
{
	pid_t pid = fork();

	switch (pid) {
	case 0:
		errct = 0;
		fn(arg);
		exit(errct);
	case -1:
		e(0);
		break;
	default:
		break;
	}
	return pid;
}

static void
test94a(void)
{
	struct bpf_program bf;
	struct timeval tv;
	uint8_t *buf;
	pid_t pid;
	size_t size;
	ssize_t len;
	uint32_t seq;
	int fd, fd2, fd3, bytes, fl;

	subtest = 1;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 0);

	{
		IOArgs args = { fd2, buf, size };
		pid = spawn_child(child_fill_random_delay, &args);
	}

	len = read(fd, buf, size);

	if (len < size * 3 / 4) e(0);
	if (len > size) e(0);
	test94_check(buf, len, 1, 0, NULL, NULL);

	wait_child_ok(pid);

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

	expect_select_empty_now(fd);

	if (get_fionread(fd) != 0) e(0);

	{
		IOArgs args = { fd2, buf, size };
		pid = spawn_child(child_fill_random_delay, &args);
	}

	expect_select_ready_blocking(fd);

	bytes = get_fionread(fd);

	expect_select_ready_blocking(fd);

	len = read(fd, buf, size);

	if (len < size * 3 / 4) e(0);
	if (len > size) e(0);
	seq = test94_check(buf, len, 1, 1, NULL, NULL);

	if (len != bytes) e(0);

	wait_child_ok(pid);

	expect_select_empty_now(fd);

	if (get_fionread(fd) != 0) e(0);

	got_signal = 0;

	{
		AddArgs args = { fd2, buf, size, seq + 1 };
		pid = spawn_child(child_add_random_delay_with_signal, &args);
	}

	tv.tv_sec = 0;
	tv.tv_usec = SLEEP_TIME * 3;
	if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= size * 3 / 4) e(0);
	if (test94_check(buf, len, seq, 1, NULL, NULL) != seq + 2) e(0);

	if (kill(pid, SIGUSR1) != 0) e(0);

	wait_child_ok(pid);

	tv.tv_sec = 0;
	tv.tv_usec = SLEEP_TIME;
	if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	if (read(fd, buf, size) != -1) e(0);
	if (errno != EAGAIN) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = 0;
	if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	{
		IOArgs args = { fd, buf, size };
		pid = spawn_child(child_read_expect_eintr, &args);
	}

	usleep(SLEEP_TIME * 2);

	if (kill(pid, SIGUSR1) != 0) e(0);

	wait_child_ok(pid);

	{
		IOArgs args = { fd, buf, size };
		pid = spawn_child(child_read_expect_eintr, &args);
	}

	usleep(SLEEP_TIME);

	test94_add_random(fd2, buf, size, 2);

	usleep(SLEEP_TIME);

	if (kill(pid, SIGUSR1) != 0) e(0);

	wait_child_ok(pid);

	if ((fl = fcntl(fd, F_GETFL)) == -1) e(0);
	if (fcntl(fd, F_SETFL, fl | O_NONBLOCK) != 0) e(0);

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= size * 3 / 4) e(0);
	seq = test94_check(buf, len, 2, 1, NULL, NULL);

	if (read(fd, buf, size) != -1) e(0);
	if (errno != EAGAIN) e(0);

	test94_fill_random(fd2, buf, size);

	len = read(fd, buf, size);
	if (len < size * 3 / 4) e(0);
	if (len > size) e(0);
	seq = test94_check(buf, len, 1, 1, NULL, NULL);

	len = read(fd, buf, size);

	if (len <= 0) e(0);
	if (len >= size * 3 / 4) e(0);
	if (test94_check(buf, len, seq, 1, NULL, NULL) != seq + 1) e(0);

	if (fcntl(fd, F_SETFL, fl) != 0) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = SLEEP_TIME * 2;
	if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	{
		AddArgs args = { fd2, buf, size, 1 };
		pid = spawn_child(child_usleep_add_seq, &args);
	}

	tv.tv_sec = 1;
	tv.tv_usec = 0;
	expect_select_empty_now(fd);

	wait_child_ok(pid);

	test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test reading packets from a BPF device, using immediate mode.
 */
static int select_readable(int fd, const struct timeval *tv_in, int *is_set)
{
	fd_set fds;
	struct timeval tv_local, *ptv = NULL;
	int r;

	if (tv_in != NULL) {
		tv_local = *tv_in;
		ptv = &tv_local;
	}

	do {
		FD_ZERO(&fds);
		FD_SET(fd, &fds);
		if (ptv != NULL)
			tv_local = *tv_in;
		r = select(fd + 1, &fds, NULL, NULL, ptv);
	} while (r == -1 && errno == EINTR);

	if (is_set)
		*is_set = (r > 0 && FD_ISSET(fd, &fds));

	return r;
}

static ssize_t read_nointr(int fd, void *buf, size_t size)
{
	ssize_t r;
	do {
		r = read(fd, buf, size);
	} while (r == -1 && errno == EINTR);
	return r;
}

static int ioctl_nointr(int fd, unsigned long req, void *arg)
{
	int r;
	do {
		r = ioctl(fd, req, arg);
	} while (r == -1 && errno == EINTR);
	return r;
}

static int fcntl_getfl_nointr(int fd)
{
	int r;
	do {
		r = fcntl(fd, F_GETFL);
	} while (r == -1 && errno == EINTR);
	return r;
}

static int fcntl_setfl_nointr(int fd, int flags)
{
	int r;
	do {
		r = fcntl(fd, F_SETFL, flags);
	} while (r == -1 && errno == EINTR);
	return r;
}

static pid_t waitpid_nointr(pid_t pid, int *status, int options)
{
	pid_t r;
	do {
		r = waitpid(pid, status, options);
	} while (r == -1 && errno == EINTR);
	return r;
}

static void
test94b(void)
{
	struct timeval tv;
	uint8_t *buf;
	unsigned int val;
	size_t size;
	ssize_t len;
	uint32_t seq;
	pid_t pid;
	int fd, fd2, fd3, bytes, status, fl, ready;
	size_t thr;

	subtest = 2;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0 /*size*/, 1 /*set_filter*/);

	thr = (size / 4) * 3;

	val = 1;
	if (ioctl_nointr(fd, BIOCIMMEDIATE, &val) != 0) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = 0;
	if (select_readable(fd, &tv, &ready) != 0) e(0);

	if (ioctl_nointr(fd, FIONREAD, &bytes) != 0) e(0);
	if (bytes != 0) e(0);

	/*
	 * Ensure that if the hold buffer is full, an immediate-mode read
	 * returns the content of the hold buffer, even if the store buffer is
	 * not empty.
	 */
	test94_fill_random(fd2, buf, size);

	if (select_readable(fd, &tv, &ready) != 1) e(0);
	if (!ready) e(0);

	if (ioctl_nointr(fd, FIONREAD, &bytes) != 0) e(0);

	len = read_nointr(fd, buf, size);
	if (len < (ssize_t)thr) e(0);
	if (len > (ssize_t)size) e(0);
	seq = test94_check(buf, len, 1 /*seq*/, 1 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/);

	if (len != bytes) e(0);

	/*
	 * There is one packet left in the buffer.  In immediate mode, this
	 * packet should be returned immediately.
	 */
	if (select_readable(fd, &tv, &ready) != 1) e(0);
	if (!ready) e(0);

	if (ioctl_nointr(fd, FIONREAD, &bytes) != 0) e(0);

	len = read_nointr(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)thr) e(0);	/* one packet < 3/4 of the size */
	if (test94_check(buf, len, seq, 1 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/) != seq + 1) e(0);

	if (len != bytes) e(0);

	/* The buffer is now empty again. */
	if (select_readable(fd, &tv, &ready) != 0) e(0);

	if (ioctl_nointr(fd, FIONREAD, &bytes) != 0) e(0);
	if (bytes != 0) e(0);

	/*
	 * Immediate-mode reads may return multiple packets from the store
	 * buffer.
	 */
	test94_add_random(fd2, buf, size, seq + 1);
	test94_add_random(fd2, buf, size, seq + 2);

	if (select_readable(fd, &tv, &ready) != 1) e(0);
	if (!ready) e(0);

	if (ioctl_nointr(fd, FIONREAD, &bytes) != 0) e(0);

	len = read_nointr(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)thr) e(0);	/* two packets < 3/4 of the size */
	if (test94_check(buf, len, seq + 1, 1 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/) != seq + 3) e(0);

	if (len != bytes) e(0);

	/*
	 * Now test waking up suspended calls, read(2) first.
	 */
	pid = fork();
	switch (pid) {
	case 0:
		errct = 0;

		usleep(SLEEP_TIME);

		test94_add_random(fd2, buf, size, seq + 3);

		exit(errct);
	case -1:
		e(0);
		break;
	default:
		break;
	}

	len = read_nointr(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)thr) e(0);	/* one packet < 3/4 of the size */
	if (test94_check(buf, len, seq + 3, 1 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/) != seq + 4) e(0);

	if (waitpid_nointr(pid, &status, 0) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	/*
	 * Then select(2).
	 */
	pid = fork();
	switch (pid) {
	case 0:
		errct = 0;

		usleep(SLEEP_TIME);

		test94_add_random(fd2, buf, size, seq + 4);

		exit(errct);
	case -1:
		e(0);
		break;
	default:
		break;
	}

	if (select_readable(fd, NULL, &ready) != 1) e(0);
	if (!ready) e(0);

	if (ioctl_nointr(fd, FIONREAD, &bytes) != 0) e(0);

	if (select_readable(fd, NULL, &ready) != 1) e(0);
	if (!ready) e(0);

	len = read_nointr(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)thr) e(0);	/* one packet < 3/4 of the size */
	if (test94_check(buf, len, seq + 4, 1 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/) != seq + 5) e(0);

	if (len != bytes) e(0);

	if (waitpid_nointr(pid, &status, 0) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	/*
	 * Non-blocking reads should behave just as with regular mode.
	 */
	fl = fcntl_getfl_nointr(fd);
	if (fl == -1) e(0);
	if (fcntl_setfl_nointr(fd, fl | O_NONBLOCK) != 0) e(0);

	if (read_nointr(fd, buf, size) != -1) e(0);
	if (errno != EAGAIN) e(0);

	test94_fill_random(fd2, buf, size);

	len = read_nointr(fd, buf, size);
	if (len < (ssize_t)thr) e(0);
	if (len > (ssize_t)size) e(0);
	seq = test94_check(buf, len, 1 /*seq*/, 1 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/);

	len = read_nointr(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)thr) e(0);	/* one packet < 3/4 of the size */
	if (test94_check(buf, len, seq, 1 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/) != seq + 1) e(0);

	if (fcntl_setfl_nointr(fd, fl) != 0) e(0);

	/*
	 * Timeouts should work with immediate mode.
	 */
	tv.tv_sec = 0;
	tv.tv_usec = SLEEP_TIME;
	if (ioctl_nointr(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);

	if (read_nointr(fd, buf, size) != -1) e(0);
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
static void assert_stats_exact(int fd, uint32_t capt, uint32_t drop)
{
	struct bpf_stat bs;

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != capt) e(0);
	if (bs.bs_recv < bs.bs_capt) e(0);
	if (bs.bs_drop != drop) e(0);
}

static void expect_fionread(int fd, int expected)
{
	int bytes;

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);
	if (bytes != expected) e(0);
}

static void select_expect_readable(int fd)
{
	fd_set fds;

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);
}

static void set_nonblock_flag(int fd)
{
	int fl = fcntl(fd, F_GETFL);

	if (fl == -1) e(0);
	if (fcntl(fd, F_SETFL, fl | O_NONBLOCK) != 0) e(0);
}

static pid_t spawn_writer_child(int fd2, uint8_t *buf, size_t size, uint32_t seq)
{
	pid_t pid = fork();

	switch (pid) {
	case 0:
		errct = 0;
		usleep(SLEEP_TIME);
		test94_fill_exact(fd2, buf, size, seq);
		exit(errct);
	case -1:
		e(0);
		break;
	default:
		break;
	}

	return pid;
}

static void wait_child_ok(pid_t pid)
{
	int status;

	if (waitpid(pid, &status, 0) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);
}

static void test94c(void)
{
	uint8_t *buf;
	size_t size;
	pid_t pid;
	uint32_t count, seq;
	int fd, fd2, fd3;

	subtest = 3;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);

	assert_stats_exact(fd, 0, 0);

	count = test94_fill_exact(fd2, buf, size, 0);

	assert_stats_exact(fd, count, 0);

	expect_fionread(fd, (int)size);
	select_expect_readable(fd);

	if (read(fd, buf, size) != (ssize_t)size) e(0);
	test94_check(buf, size, 0, 1, NULL, NULL);

	seq = test94_fill_exact(fd2, buf, size, 1);
	test94_fill_exact(fd2, buf, size, seq);

	assert_stats_exact(fd, count * 3, 0);

	test94_add_random(fd2, buf, size, 0);
	assert_stats_exact(fd, count * 3 + 1, 1);

	test94_add_random(fd2, buf, size, 0);
	assert_stats_exact(fd, count * 3 + 2, 2);

	expect_fionread(fd, (int)size);

	if (read(fd, buf, size) != (ssize_t)size) e(0);
	if (test94_check(buf, size, 1, 1, NULL, NULL) != seq) e(0);

	if (read(fd, buf, size) != (ssize_t)size) e(0);
	if (test94_check(buf, size, seq, 1, NULL, NULL) != count * 2 + 1) e(0);

	pid = spawn_writer_child(fd2, buf, size, 1);

	if (read(fd, buf, size) != (ssize_t)size) e(0);
	test94_check(buf, size, 1, 1, NULL, NULL);

	wait_child_ok(pid);

	pid = spawn_writer_child(fd2, buf, size, seq);

	select_expect_readable(fd);
	set_nonblock_flag(fd);

	if (read(fd, buf, size) != (ssize_t)size) e(0);
	test94_check(buf, size, seq, 1, NULL, NULL);

	if (read(fd, buf, size) != -1) e(0);
	if (errno != EAGAIN) e(0);

	wait_child_ok(pid);

	assert_stats_exact(fd, count * 5 + 2, 2);

	test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test receipt of large packets on BPF devices.  Large packets should be
 * truncated to the size of the buffer, but unless the filter specifies a
 * smaller capture size, no more than that.
 */
static void verify_packet(const uint8_t *buf, size_t size, size_t payload_len)
{
	struct bpf_hdr bh;
	const size_t hdr_size = BPF_WORDALIGN(sizeof(struct bpf_hdr));
	const size_t l3l4_size = sizeof(struct ip) + sizeof(struct udphdr);
	size_t idx_x;

	if (size < hdr_size + l3l4_size + 1) e(0);
	if (size < 2) e(0);

	memcpy(&bh, buf, sizeof(bh));

	if (bh.bh_hdrlen != hdr_size) e(0);
	if (bh.bh_caplen != size - hdr_size) e(0);
	if (bh.bh_datalen != l3l4_size + payload_len) e(0);

	idx_x = hdr_size + l3l4_size;
	if (idx_x >= size) e(0);
	if (buf[idx_x] != 'X') e(0);
	if (buf[size - 2] != 'Y') e(0);
	if (buf[size - 1] != 'Z') e(0);
}

static void
test94d(void)
{
	uint8_t *buf, *buf2;
	const size_t req_size = 32768;
	const int sndbuf = 65000;
	const size_t datalen = (size_t)sndbuf;
	const size_t hdr_size = BPF_WORDALIGN(sizeof(struct bpf_hdr));
	const size_t l3l4_size = sizeof(struct ip) + sizeof(struct udphdr);
	size_t size;
	ssize_t len;
	int fd, fd2, fd3;

	subtest = 4;

	size = test94_setup(&fd, &fd2, &fd3, &buf, req_size, 1);
	if (size != req_size) e(0);

	if (setsockopt(fd2, SOL_SOCKET, SO_SNDBUF, &sndbuf, sizeof(sndbuf)) != 0) e(0);

	buf2 = malloc(datalen);
	if (buf2 == NULL) e(0);

	memset(buf2, 'Y', datalen);
	if (datalen > 0) buf2[0] = 'X';

	if (size <= hdr_size + l3l4_size + 1) e(0);
	{
		size_t z_index = size - hdr_size - l3l4_size - 1;
		if (z_index < datalen) buf2[z_index] = 'Z'; else e(0);
	}

	if (write(fd2, buf2, datalen) != (ssize_t)datalen) e(0);

	if (read(fd, buf, size) != (ssize_t)size) e(0);

	verify_packet(buf, size, datalen);

	test94_add_random(fd2, buf, size, 1);

	if (write(fd2, buf2, datalen) != (ssize_t)datalen) e(0);

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if ((size_t)len >= size * 3 / 4) e(0);
	if (test94_check(buf, len, 1, 1, NULL, NULL) != 2) e(0);

	if (read(fd, buf, size) != (ssize_t)size) e(0);

	verify_packet(buf, size, datalen);

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
static void write_one(int fd, char ch)
{
	if (write(fd, &ch, 1) != 1) e(0);
}

static char read_one(int fd)
{
	char c;
	if (read(fd, &c, 1) != 1) e(0);
	return c;
}

static void bpf_flush(int fd)
{
	if (ioctl(fd, BIOCFLUSH) != 0) e(0);
}

static void get_bpf_stats(int fd, struct bpf_stat *bs)
{
	if (ioctl(fd, BIOCGSTATS, bs) != 0) e(0);
}

static void
test94_comm(int fd, int fd2, int fd3, int filtered)
{
	struct bpf_stat bs;
	char c;

	write_one(fd2, 'A');
	c = read_one(fd3);
	if (c != 'A') e(0);

	get_bpf_stats(fd, &bs);
	if (bs.bs_recv == 0) e(0);
	if (bs.bs_capt == 0) e(0);

	bpf_flush(fd);

	write_one(fd3, 'B');
	c = read_one(fd2);
	if (c != 'B') e(0);

	get_bpf_stats(fd, &bs);
	if (bs.bs_recv == 0) e(0);

	if (filtered) {
		if (bs.bs_capt != 0) e(0);
		if (bs.bs_drop != 0) e(0);
	} else {
		if (bs.bs_capt == 0) e(0);
	}

	bpf_flush(fd);
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
	size_t size, plen, alen, off;
	uint32_t caplen[4], datalen[4];
	ssize_t len;
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

	plen = sizeof(struct ip) + sizeof(struct udphdr) + sizeof(uint32_t);
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
	if (len < 0) e(0);

	if (test94_check(buf, (size_t)len, 1, 1, caplen, datalen) != 5) e(0);

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
	if (len < 0) e(0);

	if (test94_check(buf, (size_t)len, 5, 1, caplen, datalen) != 9) e(0);

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
		if ((size_t)len - off < sizeof(bh)) e(0);
		memcpy(&bh, &buf[off], sizeof(bh));

		if (bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) e(0);
		if (bh.bh_caplen != 1) e(0);
		if (bh.bh_datalen < plen) e(0);
		if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh))) e(0);

		off += bh.bh_hdrlen;

		if (buf[off] != 0x45) e(0);

		off += BPF_WORDALIGN(bh.bh_caplen);
	}
	if (off != (size_t)len) e(0);

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
test94_cksum(uint8_t *buf, size_t len)
{
	uint32_t sum = 0;
	const uint8_t *p = buf;

	if (p == NULL && len > 0U)
		return 0;

	while (len > 1U) {
		uint32_t word = ((uint32_t)p[0] << 8) | (uint32_t)p[1];
		sum += word;
		p += 2;
		len -= 2;
	}

	if (len == 1U)
		sum += ((uint32_t)p[0] << 8);

	while (sum >> 16)
		sum = (sum & UINT16_MAX) + (sum >> 16);

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
	struct udphdr uh;
	size_t off;

	if (!v6) {
		struct ip ip;

		memset(&ip, 0, sizeof(ip));
		ip.ip_v = IPVERSION;
		ip.ip_hl = sizeof(ip) >> 2;
		ip.ip_len = htons((uint16_t)(sizeof(ip) + sizeof(uh) + len));
		ip.ip_ttl = 255;
		ip.ip_p = IPPROTO_UDP;
		ip.ip_sum = 0;
		ip.ip_src.s_addr = htonl(INADDR_LOOPBACK);
		ip.ip_dst.s_addr = htonl(INADDR_LOOPBACK);

		ip.ip_sum = htons(test94_cksum((uint8_t *)&ip, sizeof(ip)));
		memcpy(buf, &ip, sizeof(ip));
		if (test94_cksum(buf, sizeof(ip)) != 0) e(0);

		off = sizeof(ip);
	} else {
		struct ip6_hdr ip6;

		memset(&ip6, 0, sizeof(ip6));
		ip6.ip6_vfc = IPV6_VERSION;
		ip6.ip6_plen = htons((uint16_t)(sizeof(uh) + len));
		ip6.ip6_nxt = IPPROTO_UDP;
		ip6.ip6_hlim = 255;
		ip6.ip6_src = in6addr_loopback;
		ip6.ip6_dst = in6addr_loopback;

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
static void assert_fd_writable(int fd)
{
	fd_set fds;

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, NULL, &fds, NULL, NULL) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);
}

static void
test94f(void)
{
	struct bpf_stat bs;
	struct ifreq ifr;
	uint8_t *buf;
	size_t off;
	size_t i;
	unsigned int uval, mtu;
	size_t mtu_sz;
	int fd, fd2, fd3;
	ssize_t rw;

	const size_t HELLO_LEN = 6;
	const size_t PAT_LEN = 12345;
	const unsigned int PRIME_251 = 251;
	const size_t MAX_BUF = (size_t)UINT16_MAX + 1;

	subtest = 6;

	(void)test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);

	assert_fd_writable(fd);

	memset(&ifr, 0, sizeof(ifr));
	if (strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name)) >= sizeof(ifr.ifr_name)) e(0);
	if (ioctl(fd2, SIOCGIFMTU, &ifr) != 0) e(0);
	mtu = ifr.ifr_mtu;
	mtu_sz = (size_t)mtu;

	{
		void *tmp = realloc(buf, MAX_BUF);
		if (tmp == NULL) e(0);
		buf = tmp;
	}

	memset(buf, 0, MAX_BUF);

	for (i = MAX_BUF; i > mtu_sz; i--) {
		rw = write(fd, buf, i);
		if (rw != -1) e(0);
		if (errno != EMSGSIZE) e(0);
	}

	rw = write(fd, buf, mtu_sz);
	if (rw != (ssize_t)mtu_sz) e(0);

	rw = write(fd, buf, 0);
	if (rw != 0) e(0);

	off = test94_make_pkt(buf, HELLO_LEN, 0);
	memcpy(buf + off, "Hello!", HELLO_LEN);

	rw = write(fd, buf, off + HELLO_LEN);
	if (rw != (ssize_t)(off + HELLO_LEN)) e(0);

	memset(buf, 0, mtu_sz);
	rw = read(fd3, buf, mtu_sz);
	if (rw != (ssize_t)HELLO_LEN) e(0);
	if (memcmp(buf, "Hello!", HELLO_LEN) != 0) e(0);

	uval = 1;
	if (ioctl(fd, BIOCSFEEDBACK, &uval) != 0) e(0);

	off = test94_make_pkt(buf, PAT_LEN, 0);
	for (i = 0; i < PAT_LEN; i++)
		buf[off + i] = (uint8_t)(1 + (i % PRIME_251));

	rw = write(fd, buf, off + PAT_LEN);
	if (rw != (ssize_t)(off + PAT_LEN)) e(0);

	memset(buf, 0, MAX_BUF);
	rw = recv(fd3, buf, UINT16_MAX, 0);
	if (rw != (ssize_t)PAT_LEN) e(0);
	for (i = 0; i < PAT_LEN; i++)
		if (buf[i] != (uint8_t)(1 + (i % PRIME_251))) e(0);

	memset(buf, 0, MAX_BUF);
	rw = recv(fd3, buf, UINT16_MAX, MSG_DONTWAIT);
	if (rw != (ssize_t)PAT_LEN) e(0);
	for (i = 0; i < PAT_LEN; i++)
		if (buf[i] != (uint8_t)(1 + (i % PRIME_251))) e(0);

	rw = recv(fd3, buf, UINT16_MAX, MSG_DONTWAIT);
	if (rw != -1) e(0);
	if (errno != EWOULDBLOCK) e(0);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != 2) e(0);

	assert_fd_writable(fd);

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
	unsigned int size = 0;
	int fd = -1;

	subtest = 7;

	fd = open(_PATH_BPF, O_RDWR);
	if (fd < 0) {
		e(0);
		goto cleanup;
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

	errno = 0;
	if (read(fd, buf, size) != -1) {
		e(0);
		goto cleanup;
	}
	if (errno != EINVAL) {
		e(0);
		goto cleanup;
	}

	errno = 0;
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
		if (close(fd) != 0) e(0);
	}
}

/*
 * Test various IOCTL calls.  Several of these tests are rather superficial,
 * because we would need a real interface, rather than the loopback device, to
 * test their functionality properly.  Also note that we skip various checks
 * performed as part of the earlier subtests.
 */
static void ioctl_expect_ok(int fd, unsigned long req, void *arg)
{
	if (ioctl(fd, req, arg) != 0) e(0);
}

static void ioctl_expect_ok_noarg(int fd, unsigned long req)
{
	if (ioctl(fd, req) != 0) e(0);
}

static void ioctl_expect_fail(int fd, unsigned long req, void *arg)
{
	if (ioctl(fd, req, arg) != -1) e(0);
}

static void ioctl_expect_fail_noarg(int fd, unsigned long req)
{
	if (ioctl(fd, req) != -1) e(0);
}

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

	if ((ufd = open(_PATH_BPF, O_RDWR)) < 0) e(0);

	uval = 1;
	ioctl_expect_ok(ufd, BIOCSBLEN, &uval);

	ioctl_expect_ok(ufd, BIOCGBLEN, &uval);
	if (uval < sizeof(struct bpf_hdr) || uval > BPF_MAXBUFSIZE) e(0);

	uval = (unsigned int)-1;
	ioctl_expect_ok(ufd, BIOCSBLEN, &uval);

	ioctl_expect_ok(ufd, BIOCGBLEN, &uval);
	if (uval < sizeof(struct bpf_hdr) || uval > BPF_MAXBUFSIZE) e(0);

	uval = 0;
	ioctl_expect_ok(ufd, BIOCSBLEN, &uval);

	ioctl_expect_ok(ufd, BIOCGBLEN, &uval);
	if (uval < sizeof(struct bpf_hdr) || uval > BPF_MAXBUFSIZE) e(0);

	uval = 1024;
	ioctl_expect_ok(ufd, BIOCSBLEN, &uval);
	ioctl_expect_ok(ufd, BIOCGBLEN, &uval);
	if (uval != 1024) e(0);

	ioctl_expect_fail(cfd, BIOCSBLEN, &uval);
	if (errno != EINVAL) e(0);

	ioctl_expect_ok(cfd, BIOCGBLEN, &uval);
	if (uval != size) e(0);

	uval = 1;
	ioctl_expect_ok(cfd, BIOCIMMEDIATE, &uval);

	test94_fill_exact(fd2, buf, size, 1);
	test94_fill_exact(fd2, buf, size, 1);
	test94_fill_exact(fd2, buf, size, 1);

	ioctl_expect_ok(cfd, BIOCGSTATS, &bs);
	if (bs.bs_recv == 0) e(0);
	if (bs.bs_drop == 0) e(0);
	if (bs.bs_capt == 0) e(0);

	ioctl_expect_ok(cfd, BIOCGSTATS, &bs);
	if (bs.bs_recv == 0) e(0);
	if (bs.bs_drop == 0) e(0);
	if (bs.bs_capt == 0) e(0);

	ioctl_expect_ok(cfd, FIONREAD, &val);
	if (val == 0) e(0);

	ioctl_expect_ok_noarg(cfd, BIOCFLUSH);

	ioctl_expect_ok(cfd, BIOCGSTATS, &bs);
	if (bs.bs_drop != 0) e(0);
	if (bs.bs_capt != 0) e(0);

	ioctl_expect_ok(cfd, FIONREAD, &val);
	if (val != 0) e(0);

	ioctl_expect_ok_noarg(ufd, BIOCFLUSH);

	ioctl_expect_ok(ufd, BIOCGSTATS, &bs);
	if (bs.bs_recv != 0) e(0);
	if (bs.bs_drop != 0) e(0);
	if (bs.bs_capt != 0) e(0);

	ioctl_expect_fail_noarg(ufd, BIOCPROMISC);
	if (errno != EINVAL) e(0);

	ioctl_expect_ok_noarg(cfd, BIOCPROMISC);

	ioctl_expect_fail(ufd, BIOCGDLT, &uval);
	if (errno != EINVAL) e(0);

	if (ioctl(ufd, BIOCGETIF, &ifr) != -1) e(0);
	if (errno != EINVAL) e(0);

	memset(&ifr, 'X', sizeof(ifr));
	ioctl_expect_ok(cfd, BIOCGETIF, &ifr);
	if (strcmp(ifr.ifr_name, LOOPBACK_IFNAME) != 0) e(0);

	memset(&ifr, 0, sizeof(ifr));
	strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
	ioctl_expect_fail(cfd, BIOCSETIF, &ifr);
	if (errno != EINVAL) e(0);

	memset(&ifr, 0, sizeof(ifr));
	memset(ifr.ifr_name, 'x', sizeof(ifr.ifr_name));
	ioctl_expect_fail(ufd, BIOCSETIF, &ifr);
	if (errno != ENXIO) e(0);

	memset(&ifr, 0, sizeof(ifr));
	strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
	ifr.ifr_name[strlen(ifr.ifr_name) - 1] += 9;
	ioctl_expect_fail(ufd, BIOCSETIF, &ifr);
	if (errno != ENXIO) e(0);

	test94_add_random(fd2, buf, size, 1);

	ioctl_expect_ok(cfd, FIONREAD, &val);
	if (val == 0) e(0);

	uval = 0;
	ioctl_expect_ok(cfd, BIOCIMMEDIATE, &uval);

	ioctl_expect_ok(cfd, FIONREAD, &val);
	if (val != 0) e(0);

	uval = 1;
	ioctl_expect_ok(cfd, BIOCIMMEDIATE, &uval);

	ioctl_expect_ok(cfd, FIONREAD, &val);
	if (val == 0) e(0);

	ioctl_expect_ok_noarg(cfd, BIOCFLUSH);

	uval = 1;
	ioctl_expect_ok(ufd, BIOCIMMEDIATE, &uval);

	uval = 0;
	ioctl_expect_ok(ufd, BIOCIMMEDIATE, &uval);

	ioctl_expect_ok(ufd, BIOCVERSION, &bv);
	if (bv.bv_major != BPF_MAJOR_VERSION) e(0);
	if (bv.bv_minor != BPF_MINOR_VERSION) e(0);

	uval = 1;
	ioctl_expect_ok(ufd, BIOCGHDRCMPLT, &uval);
	if (uval != 0) e(0);

	uval = 2;
	ioctl_expect_ok(ufd, BIOCSHDRCMPLT, &uval);

	ioctl_expect_ok(ufd, BIOCGHDRCMPLT, &uval);
	if (uval != 1) e(0);

	uval = 0;
	ioctl_expect_ok(ufd, BIOCSHDRCMPLT, &uval);

	uval = 1;
	ioctl_expect_ok(ufd, BIOCGHDRCMPLT, &uval);
	if (uval != 0) e(0);

	uval = DLT_RAW;
	ioctl_expect_fail(ufd, BIOCSDLT, &uval);
	if (errno != EINVAL) e(0);

	uval = DLT_RAW;
	ioctl_expect_ok(cfd, BIOCSDLT, &uval);

	uval = DLT_NULL;
	ioctl_expect_fail(cfd, BIOCSDLT, &uval);
	if (errno != EINVAL) e(0);

	ioctl_expect_ok(cfd, BIOCGDLT, &uval);
	if (uval != DLT_RAW) e(0);

	memset(&bfl, 0, sizeof(bfl));
	ioctl_expect_fail(ufd, BIOCGDLTLIST, &bfl);
	if (errno != EINVAL) e(0);

	memset(&bfl, 0, sizeof(bfl));
	ioctl_expect_ok(cfd, BIOCGDLTLIST, &bfl);
	if (bfl.bfl_len != 1) e(0);
	if (bfl.bfl_list != NULL) e(0);

	memset(&bfl, 0, sizeof(bfl));
	bfl.bfl_len = 2;
	ioctl_expect_ok(cfd, BIOCGDLTLIST, &bfl);
	if (bfl.bfl_len != 1) e(0);
	if (bfl.bfl_list != NULL) e(0);

	memset(&bfl, 0, sizeof(bfl));
	memset(list, 0, sizeof(list));
	bfl.bfl_list = list;
	ioctl_expect_fail(cfd, BIOCGDLTLIST, &bfl);
	if (errno != ENOMEM) e(0);
	if (list[0] != 0) e(0);

	memset(&bfl, 0, sizeof(bfl));
	bfl.bfl_len = 1;
	bfl.bfl_list = list;
	ioctl_expect_ok(cfd, BIOCGDLTLIST, &bfl);
	if (bfl.bfl_len != 1) e(0);
	if (bfl.bfl_list != list) e(0);
	if (list[0] != DLT_RAW) e(0);
	if (list[1] != 0) e(0);

	memset(&bfl, 0, sizeof(bfl));
	memset(list, 0, sizeof(list));
	bfl.bfl_len = 2;
	bfl.bfl_list = list;
	ioctl_expect_ok(cfd, BIOCGDLTLIST, &bfl);
	if (bfl.bfl_len != 1) e(0);
	if (bfl.bfl_list != list) e(0);
	if (list[0] != DLT_RAW) e(0);
	if (list[1] != 0) e(0);

	uval = 0;
	ioctl_expect_ok(ufd, BIOCGSEESENT, &uval);
	if (uval != 1) e(0);

	uval = 0;
	ioctl_expect_ok(ufd, BIOCSSEESENT, &uval);

	uval = 1;
	ioctl_expect_ok(ufd, BIOCGSEESENT, &uval);
	if (uval != 0) e(0);

	uval = 2;
	ioctl_expect_ok(ufd, BIOCSSEESENT, &uval);

	ioctl_expect_ok(ufd, BIOCGSEESENT, &uval);
	if (uval != 1) e(0);

	ioctl_expect_ok(cfd, BIOCGSEESENT, &uval);
	if (uval != 1) e(0);

	uval = 0;
	ioctl_expect_ok(cfd, BIOCSSEESENT, &uval);

	ioctl_expect_ok_noarg(cfd, BIOCFLUSH);

	test94_add_random(fd2, buf, size, 1);

	ioctl_expect_ok(cfd, BIOCGSTATS, &bs);
	if (bs.bs_recv != 0) e(0);

	uval = 1;
	ioctl_expect_ok(cfd, BIOCSSEESENT, &uval);

	ioctl_expect_ok_noarg(cfd, BIOCFLUSH);

	test94_add_random(fd2, buf, size, 1);

	ioctl_expect_ok(cfd, BIOCGSTATS, &bs);
	if (bs.bs_recv == 0) e(0);

	tv.tv_sec = 99;
	tv.tv_usec = 0;
	ioctl_expect_ok(ufd, BIOCGRTIMEOUT, &tv);
	if (tv.tv_sec != 0) e(0);
	if (tv.tv_usec != 0) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = 1000000;
	ioctl_expect_fail(ufd, BIOCSRTIMEOUT, &tv);
	if (errno != EINVAL) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = -1;
	ioctl_expect_fail(ufd, BIOCSRTIMEOUT, &tv);
	if (errno != EINVAL) e(0);

	tv.tv_sec = -1;
	tv.tv_usec = 0;
	ioctl_expect_fail(ufd, BIOCSRTIMEOUT, &tv);
	if (errno != EINVAL) e(0);

	tv.tv_sec = INT_MAX;
	tv.tv_usec = 0;
	ioctl_expect_fail(ufd, BIOCSRTIMEOUT, &tv);
	if (errno != EDOM) e(0);

	ioctl_expect_ok(ufd, BIOCGRTIMEOUT, &tv);
	if (tv.tv_sec != 0) e(0);
	if (tv.tv_usec != 0) e(0);

	tv.tv_sec = 123;
	tv.tv_usec = 1;
	ioctl_expect_ok(ufd, BIOCSRTIMEOUT, &tv);

	ioctl_expect_ok(ufd, BIOCGRTIMEOUT, &tv);
	if (tv.tv_sec != 123) e(0);
	if (tv.tv_usec == 0) e(0);

	tv.tv_sec = 0;
	tv.tv_usec = 0;
	ioctl_expect_ok(ufd, BIOCSRTIMEOUT, &tv);

	ioctl_expect_ok(ufd, BIOCGRTIMEOUT, &tv);
	if (tv.tv_sec != 0) e(0);
	if (tv.tv_usec != 0) e(0);

	uval = 1;
	ioctl_expect_ok(ufd, BIOCGFEEDBACK, &uval);
	if (uval != 0) e(0);

	uval = 2;
	ioctl_expect_ok(ufd, BIOCSFEEDBACK, &uval);

	ioctl_expect_ok(ufd, BIOCGFEEDBACK, &uval);
	if (uval != 1) e(0);

	uval = 0;
	ioctl_expect_ok(ufd, BIOCSFEEDBACK, &uval);

	uval = 1;
	ioctl_expect_ok(ufd, BIOCGFEEDBACK, &uval);
	if (uval != 0) e(0);

	if (close(ufd) != 0) e(0);

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
	struct sockaddr_in6 sin6A, sin6B;
	struct bpf_program bf;
	struct bpf_stat bs;
	struct bpf_hdr bh;
	struct ifreq ifr;
	struct ip6_hdr ip6;
	struct udphdr uh;
	uint8_t *buf = NULL, c;
	socklen_t socklen;
	ssize_t len;
	size_t off;
	unsigned int uval, size, dlt;
	int fd = -1, fd2 = -1, fd3 = -1;

	subtest = 9;

	fd = open(_PATH_BPF, O_RDWR);
	if (fd < 0) { e(0); goto cleanup; }

	if (ioctl(fd, BIOCGBLEN, &size) != 0) { e(0); goto cleanup; }
	if (size < 1024 || size > BPF_MAXBUFSIZE) { e(0); goto cleanup; }

	buf = malloc(size);
	if (buf == NULL) { e(0); goto cleanup; }

	memset(&bf, 0, sizeof(bf));
	bf.bf_len = __arraycount(test94_filter6);
	bf.bf_insns = test94_filter6;
	if (ioctl(fd, BIOCSETF, &bf) != 0) { e(0); goto cleanup; }

	uval = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &uval) != 0) { e(0); goto cleanup; }

	memset(&ifr, 0, sizeof(ifr));
	strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
	if (ioctl(fd, BIOCSETIF, &ifr) != 0) { e(0); goto cleanup; }

	if (ioctl(fd, BIOCGDLT, &dlt) != 0) { e(0); goto cleanup; }
	if (dlt != DLT_RAW) { e(0); goto cleanup; }

	fd2 = socket(AF_INET6, SOCK_DGRAM, 0);
	if (fd2 < 0) { e(0); goto cleanup; }

	memset(&sin6A, 0, sizeof(sin6A));
	sin6A.sin6_family = AF_INET6;
	sin6A.sin6_port = htons(TEST_PORT_A);
	memcpy(&sin6A.sin6_addr, &in6addr_loopback, sizeof(sin6A.sin6_addr));
	if (bind(fd2, (struct sockaddr *)&sin6A, sizeof(sin6A)) != 0) { e(0); goto cleanup; }

	memcpy(&sin6B, &sin6A, sizeof(sin6B));
	sin6B.sin6_port = htons(TEST_PORT_B);
	if (connect(fd2, (struct sockaddr *)&sin6B, sizeof(sin6B)) != 0) { e(0); goto cleanup; }

	fd3 = socket(AF_INET6, SOCK_DGRAM, 0);
	if (fd3 < 0) { e(0); goto cleanup; }

	if (bind(fd3, (struct sockaddr *)&sin6B, sizeof(sin6B)) != 0) { e(0); goto cleanup; }

	if (connect(fd3, (struct sockaddr *)&sin6A, sizeof(sin6A)) != 0) { e(0); goto cleanup; }

	if (write(fd2, "A", 1) != 1) { e(0); goto cleanup; }

	if (read(fd3, &c, 1) != 1) { e(0); goto cleanup; }
	if (c != 'A') { e(0); goto cleanup; }

	if (write(fd3, "B", 1) != 1) { e(0); goto cleanup; }

	if (read(fd2, &c, 1) != 1) { e(0); goto cleanup; }
	if (c != 'B') { e(0); goto cleanup; }

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) { e(0); goto cleanup; }
	if (bs.bs_recv < 2) { e(0); goto cleanup; }
	if (bs.bs_capt != 1) { e(0); goto cleanup; }
	if (bs.bs_drop != 0) { e(0); goto cleanup; }

	memset(buf, 0, size);

	len = read(fd, buf, size);
	if (len < 0) { e(0); goto cleanup; }

	if ((size_t)len != BPF_WORDALIGN(sizeof(bh)) +
	    BPF_WORDALIGN(sizeof(ip6) + sizeof(uh) + 1)) { e(0); goto cleanup; }

	if ((size_t)len < sizeof(bh)) { e(0); goto cleanup; }
	memcpy(&bh, buf, sizeof(bh));

	if (bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) { e(0); goto cleanup; }
	if (bh.bh_caplen != sizeof(ip6) + sizeof(uh) + 1) { e(0); goto cleanup; }
	if (bh.bh_datalen != bh.bh_caplen) { e(0); goto cleanup; }
	if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh))) { e(0); goto cleanup; }

	if (bh.bh_hdrlen + sizeof(ip6) + sizeof(uh) >= (size_t)len) { e(0); goto cleanup; }
	if (buf[bh.bh_hdrlen + sizeof(ip6) + sizeof(uh)] != 'A') { e(0); goto cleanup; }

	off = test94_make_pkt(buf, 6, 1);
	if (off > size || size - off < 6) { e(0); goto cleanup; }
	memcpy(buf + off, "Hello!", 6);

	if (write(fd, buf, off + 6) != (ssize_t)(off + 6)) { e(0); goto cleanup; }

	socklen = sizeof(sin6A);
	len = recvfrom(fd3, buf, size, 0, (struct sockaddr *)&sin6A, &socklen);
	if (len != 6) { e(0); goto cleanup; }

	if (memcmp(buf, "Hello!", 6) != 0) { e(0); goto cleanup; }
	if (socklen != sizeof(sin6A)) { e(0); goto cleanup; }
	if (sin6A.sin6_family != AF_INET6) { e(0); goto cleanup; }
	if (sin6A.sin6_port != htons(TEST_PORT_A)) { e(0); goto cleanup; }
	if (memcmp(&sin6A.sin6_addr, &in6addr_loopback,
	    sizeof(sin6A.sin6_addr)) != 0) { e(0); goto cleanup; }

cleanup:
	if (buf != NULL) free(buf);
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
	size_t slot = 0, len = 0, oldlen = 0, size = 0, bdesize = 0, items = 0;
	unsigned int count = 0, uval = 0;
	int fd = -1, fd2 = -1, fd3 = -1, val = 0, mib[5], smib[3], found = 0;
	const size_t elem_size = sizeof(*bde);
	int i;

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
	if (len + 2 > __arraycount(mib)) e(0);
	mib[len++] = sizeof(*bde);
	mib[len++] = INT_MAX;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);

	count = test94_fill_exact(fd2, buf, size, 0);
	for (i = 0; i < 2; i++) test94_fill_exact(fd2, buf, size, 0);

	if (write(fd3, "X", 1) != 1) e(0);

	if (sysctl(mib, len, NULL, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen == 0) e(0);

	{
		size_t slack;
		if (elem_size != 0 && 8 > SIZE_MAX / elem_size) e(0);
		slack = elem_size * 8;
		if (oldlen > SIZE_MAX - slack) e(0);
		bdesize = oldlen + slack;
	}
	bde = malloc(bdesize);
	if (bde == NULL) e(0);

	oldlen = bdesize;
	if (sysctl(mib, len, bde, &oldlen, NULL, 0) != 0) e(0);
	if (elem_size == 0 || oldlen % elem_size) e(0);

	found = 0;
	items = (elem_size == 0) ? 0 : oldlen / elem_size;
	for (slot = 0; slot < items; slot++) {
		if (bde[slot].bde_pid != getpid()) continue;

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

	oldlen = sizeof(bs2);
	if (sysctl(smib, __arraycount(smib), &bs2, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen != sizeof(bs2)) e(0);

	if (bs2.bs_recv < bs1.bs_recv + count * 3 + 1) e(0);
	if (bs2.bs_drop != bs1.bs_drop + count) e(0);
	if (bs2.bs_capt != bs1.bs_capt + count * 3) e(0);

	if ((fd = open(_PATH_BPF, O_RDWR)) < 0) e(0);

	uval = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &uval) != 0) e(0);
	if (ioctl(fd, BIOCSHDRCMPLT, &uval) != 0) e(0);

	uval = 0;
	if (ioctl(fd, BIOCSSEESENT, &uval) != 0) e(0);

	oldlen = bdesize;
	if (sysctl(mib, len, bde, &oldlen, NULL, 0) != 0) e(0);
	if (elem_size == 0 || oldlen % elem_size) e(0);

	found = 0;
	items = (elem_size == 0) ? 0 : oldlen / elem_size;
	for (slot = 0; slot < items; slot++) {
		if (bde[slot].bde_pid != getpid()) continue;

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
	if (sysctl(mib, len, bde, &oldlen, NULL, 0) != 0) e(0);
	if (elem_size == 0 || oldlen % elem_size) e(0);

	items = (elem_size == 0) ? 0 : oldlen / elem_size;
	for (slot = 0; slot < items; slot++) {
		if (bde[slot].bde_pid == getpid()) e(0);
	}

	free(bde);
}

/*
 * Test privileged operations as an unprivileged caller.
 */
static void
test94k(void)
{
	struct passwd *pw = NULL;
	pid_t pid;
	size_t len = 0, oldlen = 0;
	int mib[5];
	int status = 0;

	subtest = 11;

	pid = fork();
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

		_exit(errct);
	} else if (pid < 0) {
		e(0);
		return;
	}

	if (waitpid(pid, &status, 0) != pid) e(0);
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
static int choose_eth_interface(struct ifreq *ifr, struct ether_header *ether)
{
	struct ifaddrs *ifa = NULL, *ifp;
	struct if_data *ifdata;
	struct sockaddr_dl sdl;

	if (getifaddrs(&ifa) != 0) e(0);

	for (ifp = ifa; ifp != NULL; ifp = ifp->ifa_next) {
		if (!(ifp->ifa_flags & IFF_UP) || ifp->ifa_addr == NULL ||
		    ifp->ifa_addr->sa_family != AF_LINK)
			continue;

		ifdata = (struct if_data *)ifp->ifa_data;
		if (ifdata != NULL && ifdata->ifi_type == IFT_ETHER &&
		    ifdata->ifi_link_state != LINK_STATE_DOWN) {
			const struct sockaddr_dl *psdl =
			    (const struct sockaddr_dl *)ifp->ifa_addr;

			strlcpy(ifr->ifr_name, ifp->ifa_name,
			    sizeof(ifr->ifr_name));

			memcpy(&sdl, psdl, offsetof(struct sockaddr_dl, sdl_data));
			if (sdl.sdl_alen != sizeof(ether->ether_dhost)) e(0);

			memcpy(ether->ether_dhost, psdl->sdl_data + sdl.sdl_nlen,
			    sdl.sdl_alen);

			freeifaddrs(ifa);
			return 0;
		}
	}

	freeifaddrs(ifa);
	return 1;
}

static void run_udp_block_test(int bfd, const struct ether_header *base_ether,
    int family)
{
	int sfd;
	size_t off;
	ssize_t res;
	unsigned int v6 = (family == AF_INET6) ? 1U : 0U;
	const size_t payload_len = sizeof("Hello!") - 1;
	uint8_t buf[sizeof(struct ether_header) +
	    MAX(sizeof(struct ip), sizeof(struct ip6_hdr)) +
	    sizeof(struct udphdr) + sizeof("Hello!") - 1];
	struct ether_header ether;

	memcpy(&ether, base_ether, sizeof(ether));
	ether.ether_type = htons(v6 ? ETHERTYPE_IPV6 : ETHERTYPE_IP);

	if (family == AF_INET) {
		struct sockaddr_in sin;
		memset(&sin, 0, sizeof(sin));
		sin.sin_family = AF_INET;
		sin.sin_port = htons(TEST_PORT_B);
		sin.sin_addr.s_addr = htonl(INADDR_LOOPBACK);

		if ((sfd = socket(AF_INET, SOCK_DGRAM, 0)) < 0) e(0);
		if (bind(sfd, (struct sockaddr *)&sin, sizeof(sin)) != 0) e(0);
	} else {
		struct sockaddr_in6 sin6;
		memset(&sin6, 0, sizeof(sin6));
		sin6.sin6_family = AF_INET6;
		sin6.sin6_port = htons(TEST_PORT_B);
		memcpy(&sin6.sin6_addr, &in6addr_loopback, sizeof(sin6.sin6_addr));

		if ((sfd = socket(AF_INET6, SOCK_DGRAM, 0)) < 0) e(0);
		if (bind(sfd, (struct sockaddr *)&sin6, sizeof(sin6)) != 0) e(0);
	}

	memcpy(buf, &ether, sizeof(ether));
	off = sizeof(ether);
	off += test94_make_pkt(buf + off, payload_len, v6);
	if (off + payload_len > sizeof(buf)) e(0);
	memcpy(buf + off, "Hello!", payload_len);

	res = write(bfd, buf, off + payload_len);
	if (res != (ssize_t)(off + payload_len)) e(0);

	res = recv(sfd, buf, sizeof(buf), MSG_DONTWAIT);
	if (res != -1) e(0);
	if (errno != EWOULDBLOCK) e(0);

	if (close(sfd) != 0) e(0);
}

static void
test94l(void)
{
	struct ifreq ifr;
	struct ether_header ether;
	unsigned int val;
	int bfd;
	const uint8_t ether_src[ETHER_ADDR_LEN] = { 0x02, 0x00, 0x01, 0x12, 0x34, 0x56 };

	subtest = 12;

	if (!get_setting_use_network())
		return;

	memset(&ifr, 0, sizeof(ifr));
	memset(&ether, 0, sizeof(ether));

	if (choose_eth_interface(&ifr, &ether) != 0)
		return;

	if ((bfd = open(_PATH_BPF, O_RDWR)) < 0) e(0);
	if (ioctl(bfd, BIOCSETIF, &ifr) != 0) e(0);
	if (ioctl(bfd, BIOCGDLT, &val) != 0) e(0);
	if (val != DLT_EN10MB) e(0);

	val = 1;
	if (ioctl(bfd, BIOCSFEEDBACK, &val) != 0) e(0);

	memcpy(ether.ether_shost, ether_src, sizeof(ether.ether_shost));

	run_udp_block_test(bfd, &ether, AF_INET);
	run_udp_block_test(bfd, &ether, AF_INET6);

	if (close(bfd) != 0) e(0);
}

/*
 * Test program for LWIP BPF.
 */
#include <stdlib.h>
#include <time.h>
#include <limits.h>
#include <errno.h>

extern void start(int);
extern void quit(void);
extern void test94a(void);
extern void test94b(void);
extern void test94c(void);
extern void test94d(void);
extern void test94e(void);
extern void test94f(void);
extern void test94g(void);
extern void test94h(void);
extern void test94i(void);
extern void test94j(void);
extern void test94k(void);
extern void test94l(void);

static int parse_mask(int argc, char **argv) {
    if (argc == 2 && argv != NULL && argv[1] != NULL) {
        char *end = NULL;
        long val;
        errno = 0;
        val = strtol(argv[1], &end, 10);
        if (errno == ERANGE) {
            return (val > 0) ? INT_MAX : INT_MIN;
        }
        if (end == argv[1]) {
            return 0;
        }
        if (val > INT_MAX) return INT_MAX;
        if (val < INT_MIN) return INT_MIN;
        return (int)val;
    }
    return 0xFFF;
}

int main(int argc, char **argv) {
    typedef void (*test_fn)(void);
    static const test_fn tests[] = {
        test94a, test94b, test94c, test94d,
        test94e, test94f, test94g, test94h,
        test94i, test94j, test94k, test94l
    };
    int i, j;
    int iterations;
    int m;
    int ntests;
    int bit;

    start(94);
    srand48((long)time(NULL));

    m = parse_mask(argc, argv);
    iterations = ITERATIONS;
    if (iterations < 0) iterations = 0;

    ntests = (int)(sizeof(tests) / sizeof(tests[0]));

    for (i = 0; i < iterations; i++) {
        bit = 1;
        for (j = 0; j < ntests; j++) {
            if (m & bit) {
                tests[j]();
            }
            bit <<= 1;
        }
    }

    quit();
    return 0;
}
