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
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>

volatile sig_atomic_t got_signal = 0;

static void handle_signal(int sig) {
    if (sig == SIGUSR1) {
        got_signal++;
    } else {
        fprintf(stderr, "Unexpected signal received\n");
        exit(EXIT_FAILURE);
    }
}

/*
 * Send UDP packets on the given socket 'fd' so as to fill up a BPF store
 * buffer of size 'size' exactly.  The provided buffer 'buf' may be used for
 * packet generation and is at least of 'size' bytes.  Return the number of
 * packets sent.
 */
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <unistd.h>
#include <arpa/inet.h>

#define BPF_WORDALIGN(x) (((x) + (sizeof(long) - 1)) & ~(sizeof(long) - 1))

uint32_t test94_fill_exact(int fd, uint8_t *buf, size_t size, uint32_t seq) {
    size_t hdrlen = BPF_WORDALIGN(sizeof(struct bpf_hdr)) + sizeof(struct ip) + sizeof(struct udphdr) + sizeof(seq);
    size_t len;
    
    for (len = 16; len <= hdrlen; len <<= 1);
    if (len > size) return seq;
    
    hdrlen = BPF_WORDALIGN(hdrlen - sizeof(seq));
    
    while (size > 0) {
        memset(buf, 'Y', len - hdrlen);
        if (len - hdrlen > sizeof(seq))
            buf[sizeof(seq)] = 'X';
        buf[len - hdrlen - 1] = 'Z';
        memcpy(buf, &seq, sizeof(seq));

        ssize_t written = write(fd, buf, len - hdrlen);
        if (written != len - hdrlen) return seq;

        size -= len;
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
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <string.h>

#define BPF_WORDALIGN(x) (((x) + (sizeof(uint32_t) - 1)) & ~(sizeof(uint32_t) - 1))

static void handleError() {
    // Implement appropriate error handling
}

static void test94_fill_random(int fd, uint8_t *buf, size_t size) {
    size_t hdrlen, len, max_len, payload_size;
    ssize_t left;
    uint32_t seq;

    hdrlen = BPF_WORDALIGN(BPF_WORDALIGN(sizeof(struct bpf_hdr)) + sizeof(struct ip) + sizeof(struct udphdr));
    max_len = hdrlen + sizeof(seq) + (size / 10);

    for (left = size, seq = 1; left > 0; seq++) {
        len = hdrlen + sizeof(seq) + (lrand48() % (size / 10));
        payload_size = len - hdrlen;

        if (payload_size > 0) {
            memset(buf, 'Y', payload_size);
            if (payload_size > sizeof(seq)) {
                buf[sizeof(seq)] = 'X';
            }
            buf[payload_size - 1] = 'Z';
            memcpy(buf, &seq, sizeof(seq));

            if (write(fd, buf, payload_size) != (ssize_t)payload_size) {
                handleError();
                return;
            }
        }

        left -= BPF_WORDALIGN(len);
    }
}

/*
 * Send a UDP packet with a specific size of 'size' bytes and sequence number
 * 'seq' on socket 'fd', using 'buf' as scratch buffer.
 */
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>

static void test94_add_specific(int fd, uint8_t *buf, size_t size, uint32_t seq) {
    if (buf == NULL || size < sizeof(seq)) {
        // Handle error for invalid buffer or size
        return;
    }

    size_t totalSize = size + sizeof(seq);
    memset(buf, 'Y', totalSize);

    if (totalSize > sizeof(seq)) {
        buf[sizeof(seq)] = 'X';
    }

    buf[totalSize - 1] = 'Z';
    memcpy(buf, &seq, sizeof(seq));

    ssize_t bytesWritten = write(fd, buf, totalSize);
    if (bytesWritten != (ssize_t)totalSize) {
        // Handle write error
        return;
    }
}

/*
 * Send a randomly sized, relatively small UDP packet on the given socket 'fd',
 * using sequence number 'seq'.  The buffer 'buf' may be used as scratch buffer
 * which is at most 'size' bytes--the same size as the total BPF buffer.
 */
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>

static void test94_add_specific(int fd, uint8_t *buf, size_t size, uint32_t seq);

static void test94_add_random(int fd, uint8_t *buf, size_t size, uint32_t seq) {
    if (fd < 0 || buf == NULL || size == 0) {
        return; // Handle invalid inputs
    }

    size_t random_size = lrand48() % (size / 10);
    test94_add_specific(fd, buf, random_size, seq);
}

/*
 * Check whether the packet in 'buf' of 'caplen' captured bytes out of
 * 'datalen' data bytes is one we sent.  If so, return an offset to the packet
 * data.  If not, return a negative value.
 */
#include <stdint.h>
#include <string.h>
#include <arpa/inet.h>
#include <netinet/ip.h>
#include <netinet/udp.h>

#define TEST_PORT_A 12345
#define TEST_PORT_B 54321

static ssize_t test94_check_pkt(uint8_t *buf, ssize_t caplen, ssize_t datalen) {
    if (caplen < (ssize_t)sizeof(struct ip)) {
        return -1;
    }

    struct ip *ip = (struct ip *)buf;

    if (ip->ip_v != IPVERSION || ip->ip_hl != (sizeof(struct ip) >> 2) || ip->ip_p != IPPROTO_UDP) {
        return -1;
    }

    if (caplen < (ssize_t)(sizeof(struct ip) + sizeof(struct udphdr))) {
        return -1;
    }

    struct udphdr *uh = (struct udphdr *)(buf + sizeof(struct ip));

    if (uh->uh_sport != htons(TEST_PORT_A) || uh->uh_dport != htons(TEST_PORT_B)) {
        return -1;
    }

    if (datalen - (ssize_t)sizeof(struct ip) != ntohs(uh->uh_ulen)) {
        return -1;
    }

    return (ssize_t)(sizeof(struct ip) + sizeof(struct udphdr));
}

/*
 * Check whether the capture in 'buf' of 'len' bytes looks like a valid set of
 * captured packets.  The valid packets start from sequence number 'seq'; the
 * next expected sequence number is returned.  If 'filtered' is set, there
 * should be no other packets in the capture; otherwise, other packets are
 * ignored.
 */
#include <stdint.h>
#include <string.h>
#include <sys/types.h>

#define BPF_WORDALIGN(x) (((x)+(sizeof(uint32_t)-1))&~(sizeof(uint32_t)-1))

static uint32_t test94_check(uint8_t *buf, ssize_t len, uint32_t seq, int filtered, uint32_t *caplen, uint32_t *datalen) {
    struct bpf_hdr {
        struct timeval bh_tstamp;
        uint32_t bh_caplen;
        uint32_t bh_datalen;
        uint16_t bh_hdrlen;
    };
    struct bpf_hdr bh;
    ssize_t off;
    uint32_t nseq;
    
    while (len > 0) {
        if (len < BPF_WORDALIGN(sizeof(bh))) return 0;

        memcpy(&bh, buf, sizeof(bh));

        if ((bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) || 
            (caplen && (bh.bh_caplen != *caplen || bh.bh_datalen != *datalen)) ||
            (!caplen && bh.bh_datalen != bh.bh_caplen) || 
            bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh)) || 
            bh.bh_hdrlen + BPF_WORDALIGN(bh.bh_caplen) > len) {
            return 0;
        }

        buf += bh.bh_hdrlen;
        len -= bh.bh_hdrlen;

        if ((off = test94_check_pkt(buf, bh.bh_caplen, bh.bh_datalen)) < 0) {
            if (!filtered) {
                buf += BPF_WORDALIGN(bh.bh_caplen);
                len -= BPF_WORDALIGN(bh.bh_caplen);
            }
            continue;
        }

        if (bh.bh_caplen < off + sizeof(seq)) return 0;
        memcpy(&nseq, &buf[off], sizeof(nseq));
        if (nseq != seq++) return 0;

        off += sizeof(seq);
        if (off < bh.bh_caplen) {
            if (off < bh.bh_datalen - 1) {
                if (buf[off] != 'X') return 0;
                for (off++; off < bh.bh_caplen && off < bh.bh_datalen - 1; off++) {
                    if (buf[off] != 'Y') return 0;
                }
            }
            if (off == bh.bh_datalen - 1 && buf[off] != 'Z') return 0;
        }

        buf += BPF_WORDALIGN(bh.bh_caplen);
        len -= BPF_WORDALIGN(bh.bh_caplen);

        if (caplen) {
            caplen++;
            datalen++;
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
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <net/if.h>
#include <netinet/if_ether.h>
#include <net/bpf.h>

#define CHECK_ERROR(cond, action) \
    do { if (cond) { perror(#cond); action; } } while (0)

static size_t test94_setup(int *fd, int *fd2, int *fd3, uint8_t **buf, unsigned int size, int set_filter) {
    struct sockaddr_in sinA = {0}, sinB = {0};
    struct ifreq ifr = {0};
    struct bpf_program bf = {0};
    unsigned int dlt;

    *fd = open(_PATH_BPF, O_RDWR);
    CHECK_ERROR(*fd < 0, return 0);

    if (size != 0) {
        CHECK_ERROR(ioctl(*fd, BIOCSBLEN, &size) != 0, goto cleanup1);
    }

    CHECK_ERROR(ioctl(*fd, BIOCGBLEN, &size) != 0, goto cleanup1);
    CHECK_ERROR(size < 1024 || size > BPF_MAXBUFSIZE, goto cleanup1);

    *buf = malloc(size);
    CHECK_ERROR(*buf == NULL, goto cleanup1);

    if (set_filter) {
        bf.bf_len = __arraycount(test94_filter);
        bf.bf_insns = test94_filter;
        CHECK_ERROR(ioctl(*fd, BIOCSETF, &bf) != 0, goto cleanup2);
    }

    strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
    CHECK_ERROR(ioctl(*fd, BIOCSETIF, &ifr) != 0, goto cleanup2);

    CHECK_ERROR(ioctl(*fd, BIOCGDLT, &dlt) != 0 || dlt != DLT_RAW, goto cleanup2);

    *fd2 = socket(AF_INET, SOCK_DGRAM, 0);
    CHECK_ERROR(*fd2 < 0, goto cleanup2);

    sinA.sin_family = AF_INET;
    sinA.sin_port = htons(TEST_PORT_A);
    sinA.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    CHECK_ERROR(bind(*fd2, (struct sockaddr *)&sinA, sizeof(sinA)) != 0, goto cleanup3);

    memcpy(&sinB, &sinA, sizeof(sinB));
    sinB.sin_port = htons(TEST_PORT_B);
    CHECK_ERROR(connect(*fd2, (struct sockaddr *)&sinB, sizeof(sinB)) != 0, goto cleanup3);

    *fd3 = socket(AF_INET, SOCK_DGRAM, 0);
    CHECK_ERROR(*fd3 < 0, goto cleanup3);

    CHECK_ERROR(bind(*fd3, (struct sockaddr *)&sinB, sizeof(sinB)) != 0, goto cleanup4);
    CHECK_ERROR(connect(*fd3, (struct sockaddr *)&sinA, sizeof(sinA)) != 0, goto cleanup4);

    return size;

cleanup4:
    close(*fd3);
cleanup3:
    close(*fd2);
cleanup2:
    free(*buf);
cleanup1:
    close(*fd);
    return 0;
}

/*
 * Clean up resources allocated by test94_setup().
 */
static void test94_cleanup(int fd, int fd2, int fd3, uint8_t *buf) {
    if (fd3 >= 0 && close(fd3) != 0) {
        e(0);
    }

    if (fd2 >= 0 && close(fd2) != 0) {
        e(0);
    }

    if (buf != NULL) {
        free(buf);
    }

    if (fd >= 0 && close(fd) != 0) {
        e(0);
    }
}

/*
 * Test reading packets from a BPF device, using regular mode.
 */
#include <sys/types.h>
#include <sys/select.h>
#include <sys/time.h>
#include <sys/ioctl.h>
#include <unistd.h>
#include <string.h>
#include <stddef.h>
#include <stdint.h>
#include <signal.h>
#include <fcntl.h>
#include <stdlib.h>
#include <errno.h>
#include <wait.h>

#define SLEEP_TIME 100000

static void handle_error() {
    // Replace with meaningful error handling
    exit(EXIT_FAILURE);
}

static void check_wait_status(int status, pid_t pid) {
    if (wait(&status) != pid || !WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        handle_error();
    }
}

static void perform_fork_and_test(int (*test_func)(int, uint8_t *, size_t), int fd2, uint8_t *buf, size_t size) {
    pid_t pid = fork();
    if (pid == 0) {
        usleep(SLEEP_TIME);
        test_func(fd2, buf, size);
        exit(0);
    } else if (pid < 0) {
        handle_error();
    }
    check_wait_status(0, pid);
}

static void setup_read_test_timeout(int fd, uint8_t *buf, size_t size, uint32_t seq) {
    struct timeval tv = {0, SLEEP_TIME * 3};
    if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) handle_error();

    ssize_t len = read(fd, buf, size);
    if (len <= 0 || len >= size * 3 / 4) handle_error();
    if (test94_check(buf, len, seq, 1, NULL, NULL) != seq + 2) handle_error();
}

static void setup_read_test_no_timeout(int fd, uint8_t *buf, size_t size, int fd2) {
    struct timeval tv = {0, 0};
    if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) handle_error();

    pid_t pid = fork();
    if (pid == 0) {
        signal(SIGUSR1, test94_signal);
        if (read(fd, buf, size) != -1 || errno != EINTR || got_signal != 1) handle_error();
        exit(0);
    } else if (pid < 0) {
        handle_error();
    }

    usleep(SLEEP_TIME * 2);
    if (kill(pid, SIGUSR1) != 0) handle_error();
    check_wait_status(0, pid);
}

static void test_non_blocking_reads(int fd, uint8_t *buf, size_t size, int fd2) {
    int fl = fcntl(fd, F_GETFL);
    if (fl == -1 || fcntl(fd, F_SETFL, fl | O_NONBLOCK) != 0) handle_error();

    ssize_t len = read(fd, buf, size);
    if (len <= 0 || len >= size * 3 / 4) handle_error();
    uint32_t seq = test94_check(buf, len, 2, 1, NULL, NULL);

    if (read(fd, buf, size) != -1 || errno != EAGAIN) handle_error();

    test94_fill_random(fd2, buf, size);

    len = read(fd, buf, size);
    if (len < size * 3 / 4 || len > size) handle_error();
    seq = test94_check(buf, len, 1, 1, NULL, NULL);

    len = read(fd, buf, size);
    if (len <= 0 || len >= size * 3 / 4 || test94_check(buf, len, seq, 1, NULL, NULL) != seq + 1) handle_error();

    if (fcntl(fd, F_SETFL, fl) != 0) handle_error();
}

static void test94a(void) {
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
    if (pid == 0) {
        usleep(SLEEP_TIME);
        test94_fill_random(fd2, buf, size);
        exit(0);
    } else if (pid < 0) {
        handle_error();
    }

    len = read(fd, buf, size);
    if (len < size * 3 / 4 || len > size) handle_error();
    test94_check(buf, len, 1, 0, NULL, NULL);
    check_wait_status(status, pid);

    if (read(fd, buf, size - 1) != -1 || errno != EINVAL || read(fd, buf, size + 1) != -1 || errno != EINVAL || read(fd, buf, sizeof(struct bpf_hdr)) != -1 || errno != EINVAL) handle_error();

    memset(&bf, 0, sizeof(bf));
    bf.bf_len = __arraycount(test94_filter);
    bf.bf_insns = test94_filter;
    if (ioctl(fd, BIOCSETF, &bf) != 0) handle_error();

    FD_ZERO(&fds);
    FD_SET(fd, &fds);
    if (select(fd + 1, &fds, NULL, NULL, NULL) != 1 || !FD_ISSET(fd, &fds)) handle_error();

    if (ioctl(fd, FIONREAD, &bytes) != 0 || bytes != 0) handle_error();

    perform_fork_and_test(test94_fill_random, fd2, buf, size);

    len = read(fd, buf, size);
    if (len < size * 3 / 4 || len > size) handle_error();
    seq = test94_check(buf, len, 1, 1, NULL, NULL);
    if (len != bytes) handle_error();
    check_wait_status(status, pid);

    FD_ZERO(&fds);
    FD_SET(fd, &fds);

    pid = fork();
    if (pid == 0) {
        signal(SIGUSR1, test94_signal);
        usleep(SLEEP_TIME);
        test94_add_random(fd2, buf, size, seq + 1);
        usleep(SLEEP_TIME);
        if (got_signal != 0) handle_error();
        pause();
        if (got_signal != 1) handle_error();
        exit(0);
    } else if (pid < 0) {
        handle_error();
    }

    setup_read_test_timeout(fd, buf, size, seq);

    if (kill(pid, SIGUSR1) != 0) handle_error();
    check_wait_status(status, pid);

    tv.tv_sec = 0;
    tv.tv_usec = SLEEP_TIME;
    if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0 || read(fd, buf, size) != -1 || errno != EAGAIN) handle_error();

    setup_read_test_no_timeout(fd, buf, size, fd2);

    test_non_blocking_reads(fd, buf, size, fd2);

    test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test reading packets from a BPF device, using immediate mode.
 */
#include <sys/types.h>
#include <sys/time.h>
#include <sys/ioctl.h>
#include <sys/select.h>
#include <sys/wait.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdlib.h>
#include <errno.h>

static void test94b(void) {
    struct timeval tv;
    fd_set fds;
    uint8_t *buf;
    unsigned int val = 1;
    size_t size;
    ssize_t len;
    uint32_t seq;
    pid_t pid;
    int fd, fd2, fd3, bytes, status, fl;

    subtest = 2;

    size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);

    if (ioctl(fd, BIOCIMMEDIATE, &val) != 0) {
        e(0);
    }

    tv.tv_sec = 0;
    tv.tv_usec = 0;
    FD_ZERO(&fds);
    FD_SET(fd, &fds);

    if (select(fd + 1, &fds, NULL, NULL, &tv) != 0) {
        e(0);
    }

    if (ioctl(fd, FIONREAD, &bytes) != 0 || bytes != 0) {
        e(0);
    }

    test94_fill_random(fd2, buf, size);

    FD_ZERO(&fds);
    FD_SET(fd, &fds);

    if (select(fd + 1, &fds, NULL, NULL, &tv) != 1 || !FD_ISSET(fd, &fds)) {
        e(0);
    }

    if (ioctl(fd, FIONREAD, &bytes) != 0) {
        e(0);
    }

    len = read(fd, buf, size);
    if (len < size * 3 / 4 || len > size || len != bytes) {
        e(0);
    }

    seq = test94_check(buf, len, 1, 1, NULL, NULL);

    FD_ZERO(&fds);
    FD_SET(fd, &fds);

    if (select(fd + 1, &fds, NULL, NULL, &tv) != 1 || !FD_ISSET(fd, &fds)) {
        e(0);
    }

    if (ioctl(fd, FIONREAD, &bytes) != 0) {
        e(0);
    }

    len = read(fd, buf, size);
    if (len <= 0 || len >= size * 3 / 4 || test94_check(buf, len, seq, 1, NULL, NULL) != seq + 1 || len != bytes) {
        e(0);
    }

    FD_ZERO(&fds);
    FD_SET(fd, &fds);

    if (select(fd + 1, &fds, NULL, NULL, &tv) != 0) {
        e(0);
    }

    if (ioctl(fd, FIONREAD, &bytes) != 0 || bytes != 0) {
        e(0);
    }

    test94_add_random(fd2, buf, size, seq + 1);
    test94_add_random(fd2, buf, size, seq + 2);

    FD_ZERO(&fds);
    FD_SET(fd, &fds);

    if (select(fd + 1, &fds, NULL, NULL, &tv) != 1 || !FD_ISSET(fd, &fds)) {
        e(0);
    }

    if (ioctl(fd, FIONREAD, &bytes) != 0) {
        e(0);
    }

    len = read(fd, buf, size);
    if (len <= 0 || len >= size * 3 / 4 || test94_check(buf, len, seq + 1, 1, NULL, NULL) != seq + 3 || len != bytes) {
        e(0);
    }

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
    if (len <= 0 || len >= size * 3 / 4 || test94_check(buf, len, seq + 3, 1, NULL, NULL) != seq + 4) {
        e(0);
    }

    if (wait(&status) != pid || !WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        e(0);
    }

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

    if (select(fd + 1, &fds, NULL, NULL, NULL) != 1 || !FD_ISSET(fd, &fds)) {
        e(0);
    }

    if (ioctl(fd, FIONREAD, &bytes) != 0) {
        e(0);
    }

    len = read(fd, buf, size);
    if (len <= 0 || len >= size * 3 / 4 || test94_check(buf, len, seq + 4, 1, NULL, NULL) != seq + 5 || len != bytes) {
        e(0);
    }

    if (wait(&status) != pid || !WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        e(0);
    }

    if ((fl = fcntl(fd, F_GETFL)) == -1 || fcntl(fd, F_SETFL, fl | O_NONBLOCK) != 0) {
        e(0);
    }

    if (read(fd, buf, size) != -1 || errno != EAGAIN) {
        e(0);
    }

    test94_fill_random(fd2, buf, size);

    len = read(fd, buf, size);
    if (len < size * 3 / 4 || len > size) {
        e(0);
    }

    seq = test94_check(buf, len, 1, 1, NULL, NULL);

    len = read(fd, buf, size);
    if (len <= 0 || len >= size * 3 / 4 || test94_check(buf, len, seq, 1, NULL, NULL) != seq + 1) {
        e(0);
    }

    if (fcntl(fd, F_SETFL, fl) != 0) {
        e(0);
    }

    tv.tv_sec = 0;
    tv.tv_usec = SLEEP_TIME;
    if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) {
        e(0);
    }

    if (read(fd, buf, size) != -1 || errno != EAGAIN) {
        e(0);
    }

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
#include <sys/types.h>
#include <sys/ioctl.h>
#include <sys/select.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>
#include <stdlib.h>
#include <stdint.h>

#define e(code) do { handle_error(code); return; } while (0)

static void handle_error(int code) {
    // Error handling logic, e.g., logging
    exit(code);
}

static void test94c(void) {
    struct bpf_stat bs;
    fd_set fds;
    uint8_t *buf;
    size_t size;
    pid_t pid;
    uint32_t count, seq;
    int fd, fd2, fd3, bytes, status, fl;

    subtest = 3;

    size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);
    if (size == 0) e(1);

    if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(2);
    if (bs.bs_capt != 0) e(3);
    if (bs.bs_drop != 0) e(4);

    count = test94_fill_exact(fd2, buf, size, 0);
    if (count == 0) e(5);

    if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(6);
    if (bs.bs_capt != count) e(7);
    if (bs.bs_recv < bs.bs_capt) e(8);
    if (bs.bs_drop != 0) e(9);

    if (ioctl(fd, FIONREAD, &bytes) != 0) e(10);
    if (bytes != size) e(11);

    FD_ZERO(&fds);
    FD_SET(fd, &fds);
    if (select(fd + 1, &fds, NULL, NULL, NULL) != 1 || !FD_ISSET(fd, &fds)) e(12);

    if (read(fd, buf, size) != size) e(13);
    if (test94_check(buf, size, 0, 1, NULL, NULL) == 0) e(14);

    seq = test94_fill_exact(fd2, buf, size, 1);
    test94_fill_exact(fd2, buf, size, seq);

    if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(15);
    if (bs.bs_capt != count * 3) e(16);
    if (bs.bs_recv < bs.bs_capt) e(17);
    if (bs.bs_drop != 0) e(18);

    test94_add_random(fd2, buf, size, 0);
    if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(19);
    if (bs.bs_capt != count * 3 + 1 || bs.bs_drop != 1) e(20);

    test94_add_random(fd2, buf, size, 0);
    if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(21);
    if (bs.bs_capt != count * 3 + 2 || bs.bs_drop != 2) e(22);

    if (ioctl(fd, FIONREAD, &bytes) != 0) e(23);
    if (bytes != size) e(24);

    if (read(fd, buf, size) != size) e(25);
    if (test94_check(buf, size, 1, 1, NULL, NULL) != seq) e(26);

    if (read(fd, buf, size) != size) e(27);
    if (test94_check(buf, size, seq, 1, NULL, NULL) != count * 2 + 1) e(28);

    switch (pid = fork()) {
    case 0:
        errct = 0;
        usleep(SLEEP_TIME);
        test94_fill_exact(fd2, buf, size, 1);
        exit(errct);
    case -1:
        e(29);
    default:
        break;
    }

    if (read(fd, buf, size) != size) e(30);
    if (test94_check(buf, size, 1, 1, NULL, NULL) == 0) e(31);

    if (wait(&status) != pid || !WIFEXITED(status) || WEXITSTATUS(status) != 0) e(32);

    switch (pid = fork()) {
    case 0:
        errct = 0;
        usleep(SLEEP_TIME);
        test94_fill_exact(fd2, buf, size, seq);
        exit(errct);
    case -1:
        e(33);
    default:
        break;
    }

    FD_ZERO(&fds);
    FD_SET(fd, &fds);
    if (select(fd + 1, &fds, NULL, NULL, NULL) != 1 || !FD_ISSET(fd, &fds)) e(34);

    if ((fl = fcntl(fd, F_GETFL)) == -1) e(35);
    if (fcntl(fd, F_SETFL, fl | O_NONBLOCK) != 0) e(36);

    if (read(fd, buf, size) != size) e(37);
    if (test94_check(buf, size, seq, 1, NULL, NULL) == 0) e(38);

    if (read(fd, buf, size) != -1 || errno != EAGAIN) e(39);

    if (wait(&status) != pid || !WIFEXITED(status) || WEXITSTATUS(status) != 0) e(40);

    if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(41);
    if (bs.bs_capt != count * 5 + 2 || bs.bs_drop != 2) e(42);

    test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test receipt of large packets on BPF devices.  Large packets should be
 * truncated to the size of the buffer, but unless the filter specifies a
 * smaller capture size, no more than that.
 */
static void test94d(void) {
    struct bpf_hdr bh;
    uint8_t *buf = NULL, *buf2 = NULL;
    size_t size;
    ssize_t len;
    int fd = -1, fd2 = -1, fd3 = -1, datalen = 65000;

    subtest = 4;

    size = test94_setup(&fd, &fd2, &fd3, &buf, 32768, 1);
    if (size != 32768 || fd == -1 || fd2 == -1 || fd3 == -1 || buf == NULL) {
        e(0);
        goto cleanup;
    }

    if (setsockopt(fd2, SOL_SOCKET, SO_SNDBUF, &datalen, sizeof(datalen)) != 0) {
        e(0);
        goto cleanup;
    }

    buf2 = malloc(datalen);
    if (buf2 == NULL) {
        e(0);
        goto cleanup;
    }

    memset(buf2, 'Y', datalen);
    buf2[0] = 'X';
    buf2[size - sizeof(struct udphdr) - sizeof(struct ip) - BPF_WORDALIGN(sizeof(bh)) - 1] = 'Z';

    if (write(fd2, buf2, datalen) != datalen) {
        e(0);
        goto cleanup;
    }

    if (read(fd, buf, size) != size) {
        e(0);
        goto cleanup;
    }

    memcpy(&bh, buf, sizeof(bh));

    if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh)) || 
        bh.bh_caplen != size - BPF_WORDALIGN(sizeof(bh)) ||
        bh.bh_datalen != sizeof(struct ip) + sizeof(struct udphdr) + datalen) {
        e(0);
        goto cleanup;
    }

    if (buf[BPF_WORDALIGN(sizeof(bh)) + sizeof(struct ip) + sizeof(struct udphdr)] != 'X' ||
        buf[size - 2] != 'Y' ||
        buf[size - 1] != 'Z') {
        e(0);
        goto cleanup;
    }

    test94_add_random(fd2, buf, size, 1);

    if (write(fd2, buf2, datalen) != datalen) {
        e(0);
        goto cleanup;
    }

    len = read(fd, buf, size);
    if (len <= 0 || len >= size * 3 / 4) {
        e(0);
        goto cleanup;
    }

    if (test94_check(buf, len, 1, 1, NULL, NULL) != 2) {
        e(0);
        goto cleanup;
    }

    if (read(fd, buf, size) != size) {
        e(0);
        goto cleanup;
    }

    memcpy(&bh, buf, sizeof(bh));

    if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh)) || 
        bh.bh_caplen != size - BPF_WORDALIGN(sizeof(bh)) ||
        bh.bh_datalen != sizeof(struct ip) + sizeof(struct udphdr) + datalen) {
        e(0);
        goto cleanup;
    }

    if (buf[BPF_WORDALIGN(sizeof(bh)) + sizeof(struct ip) + sizeof(struct udphdr)] != 'X' ||
        buf[size - 2] != 'Y' ||
        buf[size - 1] != 'Z') {
        e(0);
        goto cleanup;
    }

cleanup:
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
#include <unistd.h>
#include <sys/ioctl.h>

static void test94_comm(int fd, int fd2, int fd3, int filtered) {
    struct bpf_stat bs;
    char c;

    if (write(fd2, "A", 1) != 1 || read(fd3, &c, 1) != 1 || c != 'A' ||
        ioctl(fd, BIOCGSTATS, &bs) != 0 || bs.bs_recv == 0 || bs.bs_capt == 0 ||
        ioctl(fd, BIOCFLUSH) != 0 || write(fd3, "B", 1) != 1 ||
        read(fd2, &c, 1) != 1 || c != 'B' ||
        ioctl(fd, BIOCGSTATS, &bs) != 0 || bs.bs_recv == 0) {
        e(0);
    }

    if (filtered) {
        if (bs.bs_capt != 0 || bs.bs_drop != 0) {
            e(0);
        }
    } else {
        if (bs.bs_capt == 0) {
            e(0);
        }
    }

    if (ioctl(fd, BIOCFLUSH) != 0) {
        e(0);
    }
}

/*
 * Test filter installation and mechanics.
 */
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <sys/ioctl.h>

static void test94e(void) {
    struct bpf_program bf = {0};
    struct bpf_stat bs;
    struct bpf_hdr bh;
    uint8_t *buf = NULL;
    size_t size = 0, len = 0, plen = 0, alen = 0, off = 0;
    uint32_t seq = 0, caplen[4] = {0}, datalen[4] = {0};
    int fd = -1, fd2 = -1, fd3 = -1, val = 1, i = 0;

    subtest = 5;
    size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 0);

    if (ioctl(fd, BIOCIMMEDIATE, &val) < 0) e(0);

    bf.bf_len = BPF_MAXINSNS + 1;
    if (ioctl(fd, BIOCSETF, &bf) != -1 || errno != EINVAL) e(0);

    bf.bf_len = __arraycount(test94_filter) - 1;
    bf.bf_insns = test94_filter;
    if (ioctl(fd, BIOCSETF, &bf) != -1 || errno != EINVAL) e(0);

    test94_comm(fd, fd2, fd3, 0);

    bf.bf_len++;
    if (ioctl(fd, BIOCSETF, &bf) < 0) e(0);

    test94_comm(fd, fd2, fd3, 1);

    memset(&bf, 0, sizeof(bf));
    if (ioctl(fd, BIOCSETF, &bf) < 0) e(0);

    test94_comm(fd, fd2, fd3, 0);
    if (ioctl(fd, BIOCSETF, &bf) < 0) e(0);
    test94_comm(fd, fd2, fd3, 0);

    plen = sizeof(struct ip) + sizeof(struct udphdr) + sizeof(seq);
    if (BPF_WORDALIGN(plen) != plen) e(0);
    alen = BPF_WORDALIGN(plen + 1);
    if (alen - 2 <= plen + 1) e(0);

    test94_filter[__arraycount(test94_filter) - 1].k = alen;
    bf.bf_len = __arraycount(test94_filter);
    bf.bf_insns = test94_filter;
    if (ioctl(fd, BIOCSETF, &bf) < 0) e(0);

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
    if (ioctl(fd, BIOCSETF, &bf) < 0) e(0);

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
    if (ioctl(fd, BIOCSETF, &bf) < 0) e(0);

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

        if (bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) e(0);
        if (bh.bh_caplen != 1) e(0);
        if (bh.bh_datalen < plen) e(0);
        if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh))) e(0);

        off += bh.bh_hdrlen;
        if (buf[off] != 0x45) e(0);

        off += BPF_WORDALIGN(bh.bh_caplen);
    }
    if (off != len) e(0);

    test94_filter[__arraycount(test94_filter) - 1].k = 0;
    if (ioctl(fd, BIOCSETF, &bf) < 0) e(0);

    test94_add_random(fd2, buf, size, 12);
    test94_add_random(fd2, buf, size, 13);
    test94_add_random(fd2, buf, size, 14);

    if (ioctl(fd, BIOCGSTATS, &bs) < 0) e(0);
    if (bs.bs_recv < 3) e(0);
    if (bs.bs_capt != 0) e(0);
    if (bs.bs_drop != 0) e(0);

    test94_filter[__arraycount(test94_filter) - 1].k = (uint32_t)-1;
    test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Compute an IP checksum.
 */
#include <stdint.h>
#include <stddef.h>

static uint16_t calculate_checksum(uint8_t *buf, size_t len) {
    uint32_t sum = 0;

    while (len > 1) {
        sum += (buf[0] << 8) | buf[1];
        buf += 2;
        len -= 2;
    }

    if (len > 0) {
        sum += buf[0] << 8;
    }

    sum = (sum & UINT16_MAX) + (sum >> 16);

    return ~(uint16_t)(sum + (sum >> 16));
}

/*
 * Set up UDP headers for a packet.  The packet uses IPv4 unless 'v6' is set,
 * in which case IPv6 is used.  The given buffer must be large enough to
 * contain the headers and the (to be appended) data.  The function returns the
 * offset into the buffer to the data portion of the packet.
 */
#include <stdint.h>
#include <string.h>
#include <arpa/inet.h>

static size_t test94_make_pkt(uint8_t *buf, size_t len, int v6) {
    struct ip {
        uint8_t ip_vhl; // version and header length
        uint8_t ip_tos; // type of service
        uint16_t ip_len;
        uint16_t ip_id;
        uint16_t ip_off;
        uint8_t ip_ttl;
        uint8_t ip_p;
        uint16_t ip_sum;
        struct in_addr ip_src;
        struct in_addr ip_dst;
    };

    struct ip6_hdr {
        uint32_t ip6_flow;   // version, traffic class, flow label
        uint16_t ip6_plen;   // payload length
        uint8_t ip6_nxt;     // next header
        uint8_t ip6_hlim;    // hop limit
        struct in6_addr ip6_src; // source address
        struct in6_addr ip6_dst; // destination address
    };

    struct udphdr {
        uint16_t uh_sport;   // source port
        uint16_t uh_dport;   // destination port
        uint16_t uh_ulen;    // udp length
        uint16_t uh_sum;     // udp checksum
    };

    struct ip ip;
    struct ip6_hdr ip6;
    struct udphdr uh;
    size_t off;

    memset(&uh, 0, sizeof(uh));
    uh.uh_sport = htons(TEST_PORT_A);
    uh.uh_dport = htons(TEST_PORT_B);
    uh.uh_ulen = htons(sizeof(uh) + len);

    if (!v6) {
        memset(&ip, 0, sizeof(ip));
        ip.ip_vhl = (IPVERSION << 4) | (sizeof(ip) >> 2);
        ip.ip_len = htons(sizeof(ip) + sizeof(uh) + len);
        ip.ip_ttl = 255;
        ip.ip_p = IPPROTO_UDP;
        ip.ip_src.s_addr = htonl(INADDR_LOOPBACK);
        ip.ip_dst.s_addr = htonl(INADDR_LOOPBACK);
        
        memcpy(buf, &ip, sizeof(ip));
        ip.ip_sum = htons(test94_cksum(buf, sizeof(ip)));
        memcpy(buf, &ip, sizeof(ip));

        if (test94_cksum(buf, sizeof(ip)) != 0) abort();

        off = sizeof(ip);
    } else {
        memset(&ip6, 0, sizeof(ip6));
        ip6.ip6_flow = htonl((IPV6_VERSION << 28) | (0 << 20) | 0);
        ip6.ip6_plen = htons(sizeof(uh) + len);
        ip6.ip6_nxt = IPPROTO_UDP;
        ip6.ip6_hlim = 255;
        ip6.ip6_src = in6addr_loopback;
        ip6.ip6_dst = in6addr_loopback;

        memcpy(buf, &ip6, sizeof(ip6));

        off = sizeof(ip6);
    }

    memcpy(buf + off, &uh, sizeof(uh));

    return off + sizeof(uh);
}

/*
 * Test sending packets by writing to a BPF device.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/select.h>
#include <sys/ioctl.h>
#include <unistd.h>
#include <net/if.h>
#include <fcntl.h>

#define LOOPBACK_IFNAME "lo0"
#define e(x) exit(EXIT_FAILURE) // Assuming e(x) is a macro for error handling

static void test94f(void) {
    struct bpf_stat bs;
    struct ifreq ifr;
    fd_set fds;
    uint8_t *buf = NULL;
    size_t off;
    unsigned int i, mtu;
    int fd, fd2, fd3;

    // Assumed to be some external initialization function
    if (test94_setup(&fd, &fd2, &fd3, &buf, 0, 1) != 0) e(0);

    // Always assert device is writable
    FD_ZERO(&fds);
    FD_SET(fd, &fds);
    if (select(fd + 1, NULL, &fds, NULL, NULL) != 1 || !FD_ISSET(fd, &fds)) e(0);

    // Obtain MTU
    memset(&ifr, 0, sizeof(ifr));
    strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
    if (ioctl(fd2, SIOCGIFMTU, &ifr) != 0) e(0);
    mtu = ifr.ifr_mtu;

    buf = realloc(buf, UINT16_MAX + 1);
    if (buf == NULL) e(0);

    memset(buf, 0, UINT16_MAX + 1);

    // Test packet size limits
    for (i = UINT16_MAX + 1; i > mtu; i--) {
        if (write(fd, buf, i) != -1 || errno != EMSGSIZE) e(0);
    }

    if (write(fd, buf, mtu) != (ssize_t)mtu) e(0);
    if (write(fd, buf, 0) != 0) e(0);

    // Send actual packet and check arrival
    off = test94_make_pkt(buf, 6, 0);
    memcpy(buf + off, "Hello!", 6);
    if (write(fd, buf, off + 6) != (ssize_t)(off + 6)) e(0);

    memset(buf, 0, mtu);
    if (read(fd3, buf, mtu) != 6 || memcmp(buf, "Hello!", 6) != 0) e(0);

    // Enable feedback mode
    unsigned int val = 1;
    if (ioctl(fd, BIOCSFEEDBACK, &val) != 0) e(0);

    off = test94_make_pkt(buf, 12345, 0);
    for (i = 0; i < 12345; i++) buf[off + i] = 1 + (i % 251);

    if (write(fd, buf, off + 12345) != (ssize_t)(off + 12345)) e(0);

    // Check packets are received twice
    for (int j = 0; j < 2; j++) {
        memset(buf, 0, UINT16_MAX);
        if (recv(fd3, buf, UINT16_MAX, 0) != 12345) e(0);
        for (i = 0; i < 12345; i++) if (buf[i] != 1 + (i % 251)) e(0);
    }

    memset(buf, 0, UINT16_MAX);
    if (recv(fd3, buf, UINT16_MAX, MSG_DONTWAIT) != -1 || errno != EWOULDBLOCK) e(0);

    // Check BPF device statistics
    if (ioctl(fd, BIOCGSTATS, &bs) != 0 || bs.bs_capt != 2) e(0);

    // Check select after writing data
    FD_ZERO(&fds);
    FD_SET(fd, &fds);
    if (select(fd + 1, NULL, &fds, NULL, NULL) != 1 || !FD_ISSET(fd, &fds)) e(0);

    // Assumed to be some external cleanup function
    test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test read, write, and select operations on unconfigured devices.
 */
#include <sys/select.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>

#define _PATH_BPF "/dev/bpf"
#define BPF_MAXBUFSIZE 4096

static void handle_error(int condition) {
    if (condition) {
        perror("Error");
        exit(EXIT_FAILURE);
    }
}

static void test94g(void) {
    fd_set rfds, wfds;
    uint8_t *buf;
    unsigned int size;
    int fd;

    fd = open(_PATH_BPF, O_RDWR);
    handle_error(fd < 0);

    handle_error(ioctl(fd, BIOCGBLEN, &size) != 0 || size < 1024 || size > BPF_MAXBUFSIZE);

    buf = (uint8_t *)malloc(size);
    handle_error(buf == NULL);

    handle_error(read(fd, buf, size) != -1 || errno != EINVAL);
    handle_error(write(fd, buf, size) != -1 || errno != EINVAL);

    FD_ZERO(&rfds);
    FD_SET(fd, &rfds);
    FD_ZERO(&wfds);
    FD_SET(fd, &wfds);

    handle_error(select(fd + 1, &rfds, &wfds, NULL, NULL) != 2);
    handle_error(!FD_ISSET(fd, &rfds) || !FD_ISSET(fd, &wfds));

    free(buf);
    handle_error(close(fd) != 0);
}

/*
 * Test various IOCTL calls.  Several of these tests are rather superficial,
 * because we would need a real interface, rather than the loopback device, to
 * test their functionality properly.  Also note that we skip various checks
 * performed as part of the earlier subtests.
 */
static void test94h(void) {
    struct bpf_stat bs = {0};
    struct bpf_version bv = {0};
    struct bpf_dltlist bfl = {0};
    struct ifreq ifr = {0};
    struct timeval tv = {0};
    uint8_t *buf = NULL;
    size_t size = 0;
    unsigned int uval = 0, list[2] = {0};
    int cfd = -1, ufd = -1, fd2 = -1, fd3 = -1, val = 0;

    subtest = 8;

    size = test94_setup(&cfd, &fd2, &fd3, &buf, 0, 1);

    ufd = open(_PATH_BPF, O_RDWR);
    if (ufd < 0) e(0);

    int bpf_ioctl_check(int fd, unsigned long request, void *arg, int expected_errno) {
        if (ioctl(fd, request, arg) == -1) {
            if (expected_errno == 0 || errno != expected_errno) e(0);
            return -1;
        }
        return 0;
    }

    int bpf_ioctl_validate(int fd, unsigned long request, void *arg, unsigned int min_val, unsigned int max_val) {
        if (ioctl(fd, request, arg) != 0) e(0);
        unsigned int val = *(unsigned int *)arg;
        if (val < min_val || val > max_val) e(0);
        return 0;
    }

    bpf_ioctl_check(ufd, BIOCSBLEN, &(unsigned int){1}, 0);
    bpf_ioctl_validate(ufd, BIOCGBLEN, &uval, sizeof(struct bpf_hdr), BPF_MAXBUFSIZE);

    bpf_ioctl_check(ufd, BIOCSBLEN, &(unsigned int){(unsigned int)-1}, 0);
    bpf_ioctl_validate(ufd, BIOCGBLEN, &uval, sizeof(struct bpf_hdr), BPF_MAXBUFSIZE);

    bpf_ioctl_check(ufd, BIOCSBLEN, &(unsigned int){0}, 0);
    bpf_ioctl_validate(ufd, BIOCGBLEN, &uval, sizeof(struct bpf_hdr), BPF_MAXBUFSIZE);

    bpf_ioctl_check(ufd, BIOCSBLEN, &(unsigned int){1024}, 0);
    if (ioctl(ufd, BIOCGBLEN, &uval) != 0 || uval != 1024) e(0);

    if (bpf_ioctl_check(cfd, BIOCSBLEN, &(unsigned int){1024}, EINVAL) != -1) e(0);
    bpf_ioctl_validate(cfd, BIOCGBLEN, &uval, size, size);

    uval = 1;
    bpf_ioctl_check(cfd, BIOCIMMEDIATE, &uval, 0);

    test94_fill_exact(fd2, buf, size, 1);
    test94_fill_exact(fd2, buf, size, 1);
    test94_fill_exact(fd2, buf, size, 1);

    bpf_ioctl_check(cfd, BIOCGSTATS, &bs, 0);
    if (bs.bs_recv == 0 || bs.bs_drop == 0 || bs.bs_capt == 0) e(0);

    bpf_ioctl_check(cfd, BIOCGSTATS, &bs, 0);
    if (bs.bs_recv == 0 || bs.bs_drop == 0 || bs.bs_capt == 0) e(0);

    bpf_ioctl_check(cfd, FIONREAD, &val, 0);
    if (val == 0) e(0);

    bpf_ioctl_check(cfd, BIOCFLUSH, NULL, 0);

    if (bpf_ioctl_check(cfd, BIOCGSTATS, &bs, 0) != 0 || bs.bs_drop != 0 || bs.bs_capt != 0) e(0);

    bpf_ioctl_check(cfd, FIONREAD, &val, 0);
    if (val != 0) e(0);

    bpf_ioctl_check(ufd, BIOCFLUSH, NULL, 0);

    bpf_ioctl_check(ufd, BIOCGSTATS, &bs, 0);
    if (bs.bs_recv != 0 || bs.bs_drop != 0 || bs.bs_capt != 0) e(0);

    if (bpf_ioctl_check(ufd, BIOCPROMISC, NULL, EINVAL) != -1) e(0);
    bpf_ioctl_check(cfd, BIOCPROMISC, NULL, 0);

    if (bpf_ioctl_check(ufd, BIOCGDLT, &uval, EINVAL) != -1) e(0);

    if (bpf_ioctl_check(ufd, BIOCGETIF, &ifr, EINVAL) != -1) e(0);

    memset(&ifr, 'X', sizeof(ifr));
    bpf_ioctl_check(cfd, BIOCGETIF, &ifr, 0);
    if (strcmp(ifr.ifr_name, LOOPBACK_IFNAME) != 0) e(0);

    memset(&ifr, 0, sizeof(ifr));
    strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
    if (bpf_ioctl_check(cfd, BIOCSETIF, &ifr, EINVAL) != -1) e(0);

    memset(&ifr, 0, sizeof(ifr));
    memset(ifr.ifr_name, 'x', sizeof(ifr.ifr_name));
    if (bpf_ioctl_check(ufd, BIOCSETIF, &ifr, ENXIO) != -1) e(0);

    memset(&ifr, 0, sizeof(ifr));
    strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
    ifr.ifr_name[strlen(ifr.ifr_name) - 1] += 9;
    if (bpf_ioctl_check(ufd, BIOCSETIF, &ifr, ENXIO) != -1) e(0);

    test94_add_random(fd2, buf, size, 1);

    bpf_ioctl_check(cfd, FIONREAD, &val, 0);
    if (val == 0) e(0);

    uval = 0;
    bpf_ioctl_check(cfd, BIOCIMMEDIATE, &uval, 0);

    bpf_ioctl_check(cfd, FIONREAD, &val, 0);
    if (val != 0) e(0);

    uval = 1;
    bpf_ioctl_check(cfd, BIOCIMMEDIATE, &uval, 0);

    bpf_ioctl_check(cfd, FIONREAD, &val, 0);
    if (val == 0) e(0);

    bpf_ioctl_check(cfd, BIOCFLUSH, NULL, 0);

    uval = 1;
    bpf_ioctl_check(ufd, BIOCIMMEDIATE, &uval, 0);
    uval = 0;
    bpf_ioctl_check(ufd, BIOCIMMEDIATE, &uval, 0);

    bpf_ioctl_check(ufd, BIOCVERSION, &bv, 0);
    if (bv.bv_major != BPF_MAJOR_VERSION || bv.bv_minor != BPF_MINOR_VERSION) e(0);

    uval = 1;
    bpf_ioctl_check(ufd, BIOCGHDRCMPLT, &uval, 0);
    if (uval != 0) e(0);

    uval = 2;
    bpf_ioctl_check(ufd, BIOCSHDRCMPLT, &uval, 0);

    bpf_ioctl_check(ufd, BIOCGHDRCMPLT, &uval, 0);
    if (uval != 1) e(0);

    uval = 0;
    bpf_ioctl_check(ufd, BIOCSHDRCMPLT, &uval, 0);

    uval = 1;
    bpf_ioctl_check(ufd, BIOCGHDRCMPLT, &uval, 0);
    if (uval != 0) e(0);

    if (bpf_ioctl_check(ufd, BIOCSDLT, &(unsigned int){DLT_RAW}, EINVAL) != -1) e(0);

    uval = DLT_RAW;
    bpf_ioctl_check(cfd, BIOCSDLT, &uval, 0);

    if (bpf_ioctl_check(cfd, BIOCSDLT, &(unsigned int){DLT_NULL}, EINVAL) != -1) e(0);

    bpf_ioctl_check(cfd, BIOCGDLT, &uval, 0);
    if (uval != DLT_RAW) e(0);

    if (bpf_ioctl_check(ufd, BIOCGDLTLIST, &bfl, EINVAL) != -1) e(0);

    bfl.bfl_len = 1;
    if (bpf_ioctl_check(cfd, BIOCGDLTLIST, &bfl, 0) != 0 || bfl.bfl_len != 1 || bfl.bfl_list != NULL) e(0);

    bfl.bfl_len = 2;
    bpf_ioctl_check(cfd, BIOCGDLTLIST, &bfl, 0);
    if (bfl.bfl_len != 1 || bfl.bfl_list != NULL) e(0);

    memset(list, 0, sizeof(list));
    bfl.bfl_list = list;
    if (bpf_ioctl_check(cfd, BIOCGDLTLIST, &bfl, ENOMEM) != -1) e(0);
    if (list[0] != 0) e(0);

    bfl.bfl_len = 1;
    bfl.bfl_list = list;
    bpf_ioctl_check(cfd, BIOCGDLTLIST, &bfl, 0);
    if (bfl.bfl_len != 1 || list[0] != DLT_RAW || list[1] != 0) e(0);

    bfl.bfl_len = 2;
    bfl.bfl_list = list;
    bpf_ioctl_check(cfd, BIOCGDLTLIST, &bfl, 0);
    if (bfl.bfl_len != 1 || list[0] != DLT_RAW || list[1] != 0) e(0);

    uval = 0;
    bpf_ioctl_check(ufd, BIOCGSEESENT, &uval, 0);
    if (uval != 1) e(0);

    uval = 0;
    bpf_ioctl_check(ufd, BIOCSSEESENT, &uval, 0);

    uval = 1;
    bpf_ioctl_check(ufd, BIOCGSEESENT, &uval, 0);
    if (uval != 0) e(0);

    uval = 2;
    bpf_ioctl_check(ufd, BIOCSSEESENT, &uval, 0);

    bpf_ioctl_check(ufd, BIOCGSEESENT, &uval, 0);
    if (uval != 1) e(0);

    bpf_ioctl_check(cfd, BIOCGSEESENT, &uval, 0);
    if (uval != 1) e(0);

    uval = 0;
    bpf_ioctl_check(cfd, BIOCSSEESENT, &uval, 0);

    bpf_ioctl_check(cfd, BIOCFLUSH, NULL, 0);

    test94_add_random(fd2, buf, size, 1);

    bpf_ioctl_check(cfd, BIOCGSTATS, &bs, 0);
    if (bs.bs_recv != 0) e(0);

    uval = 1;
    bpf_ioctl_check(cfd, BIOCSSEESENT, &uval, 0);

    bpf_ioctl_check(cfd, BIOCFLUSH, NULL, 0);

    test94_add_random(fd2, buf, size, 1);

    bpf_ioctl_check(cfd, BIOCGSTATS, &bs, 0);
    if (bs.bs_recv == 0) e(0);

    tv.tv_usec = 1000000;
    if (bpf_ioctl_check(ufd, BIOCSRTIMEOUT, &tv, EINVAL) != -1) e(0);

    tv.tv_usec = -1;
    if (bpf_ioctl_check(ufd, BIOCSRTIMEOUT, &tv, EINVAL) != -1) e(0);

    tv.tv_sec = -1;
    tv.tv_usec = 0;
    if (bpf_ioctl_check(ufd, BIOCSRTIMEOUT, &tv, EINVAL) != -1) e(0);

    tv.tv_sec = INT_MAX;
    if (bpf_ioctl_check(ufd, BIOCSRTIMEOUT, &tv, EDOM) != -1) e(0);

    if (bpf_ioctl_check(ufd, BIOCGRTIMEOUT, &tv, 0) != 0 || tv.tv_sec != 0 || tv.tv_usec != 0) e(0);

    tv.tv_sec = 123;
    tv.tv_usec = 1;
    bpf_ioctl_check(ufd, BIOCSRTIMEOUT, &tv, 0);

    bpf_ioctl_check(ufd, BIOCGRTIMEOUT, &tv, 0);
    if (tv.tv_sec != 123 || tv.tv_usec == 0) e(0);

    tv.tv_sec = 0;
    tv.tv_usec = 0;
    bpf_ioctl_check(ufd, BIOCSRTIMEOUT, &tv, 0);

    bpf_ioctl_check(ufd, BIOCGRTIMEOUT, &tv, 0);
    if (tv.tv_sec != 0 || tv.tv_usec != 0) e(0);

    uval = 1;
    bpf_ioctl_check(ufd, BIOCGFEEDBACK, &uval, 0);
    if (uval != 0) e(0);

    uval = 2;
    bpf_ioctl_check(ufd, BIOCSFEEDBACK, &uval, 0);

    bpf_ioctl_check(ufd, BIOCGFEEDBACK, &uval, 0);
    if (uval != 1) e(0);

    uval = 0;
    bpf_ioctl_check(ufd, BIOCSFEEDBACK, &uval, 0);

    uval = 1;
    bpf_ioctl_check(ufd, BIOCGFEEDBACK, &uval, 0);
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
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <net/if.h>
#include <netinet/in.h>
#include <netinet/ip6.h>
#include <netinet/udp.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <errno.h>
#include <stdint.h>

// Assuming required constants and functions are defined elsewhere
#define _PATH_BPF "/dev/bpf"
#define BPF_MAXBUFSIZE 4096
#define LOOPBACK_IFNAME "lo0"
#define DLT_RAW 12
#define TEST_PORT_A 12345
#define TEST_PORT_B 12346
extern struct bpf_program test94_filter6[];
extern unsigned int __arraycount(struct bpf_program*);
extern size_t test94_make_pkt(uint8_t*, int, int);

static void handle_error(const char *msg) {
    perror(msg);
    exit(EXIT_FAILURE);
}

static void test94i(void) {
    struct sockaddr_in6 sin6A, sin6B;
    struct bpf_program bf = {0};
    struct bpf_stat bs;
    struct bpf_hdr bh;
    struct ifreq ifr = {0};
    struct ip6_hdr ip6;
    struct udphdr uh;
    uint8_t *buf = NULL, c;
    socklen_t socklen;
    ssize_t len;
    size_t off;
    unsigned int uval, size, dlt;
    int fd, fd2, fd3;

    subtest = 9;

    if ((fd = open(_PATH_BPF, O_RDWR)) < 0) 
        handle_error("open");

    if (ioctl(fd, BIOCGBLEN, &size) != 0 || size < 1024 || size > BPF_MAXBUFSIZE)
        handle_error("ioctl BIOCGBLEN");

    buf = malloc(size);
    if (!buf)
        handle_error("malloc");

    bf.bf_len = __arraycount(test94_filter6);
    bf.bf_insns = test94_filter6;
    if (ioctl(fd, BIOCSETF, &bf) != 0)
        handle_error("ioctl BIOCSETF");

    uval = 1;
    if (ioctl(fd, BIOCIMMEDIATE, &uval) != 0)
        handle_error("ioctl BIOCIMMEDIATE");

    strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
    if (ioctl(fd, BIOCSETIF, &ifr) != 0)
        handle_error("ioctl BIOCSETIF");

    if (ioctl(fd, BIOCGDLT, &dlt) != 0 || dlt != DLT_RAW)
        handle_error("ioctl BIOCGDLT");

    if ((fd2 = socket(AF_INET6, SOCK_DGRAM, 0)) < 0)
        handle_error("socket fd2");

    memset(&sin6A, 0, sizeof(sin6A));
    sin6A.sin6_family = AF_INET6;
    sin6A.sin6_port = htons(TEST_PORT_A);
    memcpy(&sin6A.sin6_addr, &in6addr_loopback, sizeof(sin6A.sin6_addr));
    if (bind(fd2, (struct sockaddr *)&sin6A, sizeof(sin6A)) != 0)
        handle_error("bind fd2");

    sin6B = sin6A;
    sin6B.sin6_port = htons(TEST_PORT_B);
    if (connect(fd2, (struct sockaddr *)&sin6B, sizeof(sin6B)) != 0)
        handle_error("connect fd2");

    if ((fd3 = socket(AF_INET6, SOCK_DGRAM, 0)) < 0)
        handle_error("socket fd3");

    if (bind(fd3, (struct sockaddr *)&sin6B, sizeof(sin6B)) != 0)
        handle_error("bind fd3");

    if (connect(fd3, (struct sockaddr *)&sin6A, sizeof(sin6A)) != 0)
        handle_error("connect fd3");

    if (write(fd2, "A", 1) != 1 || read(fd3, &c, 1) != 1 || c != 'A')
        handle_error("IO test 1");

    if (write(fd3, "B", 1) != 1 || read(fd2, &c, 1) != 1 || c != 'B')
        handle_error("IO test 2");

    if (ioctl(fd, BIOCGSTATS, &bs) != 0 || bs.bs_recv < 2 || bs.bs_capt != 1 || bs.bs_drop != 0)
        handle_error("ioctl BIOCGSTATS");

    memset(buf, 0, size);
    len = read(fd, buf, size);
    if (len != BPF_WORDALIGN(sizeof(bh)) + BPF_WORDALIGN(sizeof(ip6) + sizeof(uh) + 1))
        handle_error("read length");

    memcpy(&bh, buf, sizeof(bh));
    if (bh.bh_caplen != sizeof(ip6) + sizeof(uh) + 1 || bh.bh_datalen != bh.bh_caplen || bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh)))
        handle_error("bh validation");

    if (buf[bh.bh_hdrlen + sizeof(ip6) + sizeof(uh)] != 'A')
        handle_error("buf content");

    off = test94_make_pkt(buf, 6, 1);
    memcpy(buf + off, "Hello!", 6);
    if (write(fd, buf, off + 6) != off + 6)
        handle_error("write BPF");

    socklen = sizeof(sin6A);
    if (recvfrom(fd3, buf, size, 0, (struct sockaddr *)&sin6A, &socklen) != 6 || memcmp(buf, "Hello!", 6) != 0 || socklen != sizeof(sin6A) || sin6A.sin6_family != AF_INET6 || sin6A.sin6_port != htons(TEST_PORT_A) || memcmp(&sin6A.sin6_addr, &in6addr_loopback, sizeof(sin6A.sin6_addr)) != 0)
        handle_error("recvfrom");

    free(buf);
    if (close(fd3) != 0 || close(fd2) != 0 || close(fd) != 0)
        handle_error("close");
}

/*
 * Test the BPF sysctl(7) interface at a basic level.
 */
#include <sys/types.h>
#include <sys/sysctl.h>
#include <sys/ioctl.h>
#include <fcntl.h>
#include <limits.h>
#include <string.h>
#include <unistd.h>
#include <stdlib.h>
#include <errno.h>

struct bpf_stat {
	unsigned int bs_recv;
	unsigned int bs_drop;
	unsigned int bs_capt;
};

struct bpf_d_ext {
	pid_t bde_pid;
	unsigned int bde_bufsize;
	int bde_promisc;
	int bde_state;
	int bde_immediate;
	int bde_hdrcmplt;
	int bde_seesent;
	unsigned int bde_rcount;
	unsigned int bde_dcount;
	unsigned int bde_ccount;
	char bde_ifname[16];
};

#define e(x) do { perror("error"); exit(x); } while (0)
#define __arraycount(__a) (sizeof(__a) / sizeof(__a[0]))
#define _PATH_BPF "/dev/bpf"
#define BPF_IDLE 0
#define BIOCFLUSH 1
#define BIOCIMMEDIATE 2
#define BIOCSHDRCMPLT 3
#define BIOCSSEESENT 4
#define LOOPBACK_IFNAME "lo0"

extern size_t test94_setup(int *fd, int *fd2, int *fd3, uint8_t **buf, size_t size, int set_filter);
extern void test94_cleanup(int fd, int fd2, int fd3, uint8_t *buf);
extern unsigned int test94_fill_exact(int fd, uint8_t *buf, size_t size, int flag);

static void test94j(void) {
	struct bpf_stat bs1, bs2;
	struct bpf_d_ext *bde = NULL;
	uint8_t *buf;
	unsigned int count;
	size_t len, oldlen, bdesize;
	int fd, fd2, fd3, val,  mib[5], smib[3];
	
	memset(mib, 0, sizeof(mib));
	len = __arraycount(mib);
	if (sysctlnametomib("net.bpf.maxbufsize", mib, &len) == -1) e(0);
	
	oldlen = sizeof(val);
	if (sysctl(mib, len, &val, &oldlen, NULL, 0) == -1 || oldlen != sizeof(val) || val < 1024 || val > INT_MAX / 2) e(0);
	
	if (sysctl(mib, len, NULL, NULL, &val, sizeof(val)) != -1 || errno != EPERM) e(0);
	
	memset(smib, 0, sizeof(smib));
	len = __arraycount(smib);
	if (sysctlnametomib("net.bpf.stats", smib, &len) == -1 || sysctl(smib, len, &bs1, &oldlen, NULL, 0) == -1 || oldlen != sizeof(bs1)) e(0);
	
	memset(mib, 0, sizeof(mib));
	len = 4;
	if (sysctlnametomib("net.bpf.peers", mib, &len) == -1) e(0);
	mib[len++] = sizeof(*bde);	
	mib[len++] = INT_MAX;		

	size_t size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);

	count = test94_fill_exact(fd2, buf, size, 0);
	test94_fill_exact(fd2, buf, size, 0);
	test94_fill_exact(fd2, buf, size, 0);

	if (write(fd3, "X", 1) != 1) e(0);

	if (sysctl(mib, len, NULL, &oldlen, NULL, 0) == -1 || oldlen == 0) e(0);

	bdesize = oldlen + sizeof(*bde) * 8;
	if ((bde = malloc(bdesize)) == NULL) e(0);

	oldlen = bdesize;
	if (sysctl(mib, len, bde, &oldlen, NULL, 0) == -1 || oldlen % sizeof(*bde)) e(0);

	int found = 0;
	for (size_t slot = 0; slot < oldlen / sizeof(*bde); slot++) {
		if (bde[slot].bde_pid != getpid()) continue;

		if (bde[slot].bde_bufsize != size || bde[slot].bde_promisc != 0 || 
			bde[slot].bde_state != BPF_IDLE || bde[slot].bde_immediate != 0 ||
			bde[slot].bde_hdrcmplt != 0 || bde[slot].bde_seesent != 1 || 
			bde[slot].bde_rcount < count * 3 + 1 || bde[slot].bde_dcount != count || 
			bde[slot].bde_ccount != count * 3 || 
			strcmp(bde[slot].bde_ifname, LOOPBACK_IFNAME) != 0) e(0);

		found++;
	}
	if (found != 1) e(0);

	if (ioctl(fd, BIOCFLUSH) != 0) e(0);

	test94_cleanup(fd, fd2, fd3, buf);

	oldlen = sizeof(bs2);
	if (sysctl(smib, __arraycount(smib), &bs2, &oldlen, NULL, 0) == -1 || 
		oldlen != sizeof(bs2) || 
		bs2.bs_recv < bs1.bs_recv + count * 3 + 1 || 
		bs2.bs_drop != bs1.bs_drop + count || 
		bs2.bs_capt != bs1.bs_capt + count * 3) e(0);

	if ((fd = open(_PATH_BPF, O_RDWR)) < 0) e(0);

	unsigned int uval = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &uval) != 0 || ioctl(fd, BIOCSHDRCMPLT, &uval) != 0) e(0);

	uval = 0;
	if (ioctl(fd, BIOCSSEESENT, &uval) != 0) e(0);

	oldlen = bdesize;
	if (sysctl(mib, len, bde, &oldlen, NULL, 0) == -1 || oldlen % sizeof(*bde)) e(0);

	found = 0;
	for (size_t slot = 0; slot < oldlen / sizeof(*bde); slot++) {
		if (bde[slot].bde_pid != getpid()) continue;

		if (bde[slot].bde_bufsize != size || bde[slot].bde_promisc != 0 || 
			bde[slot].bde_state != BPF_IDLE || bde[slot].bde_immediate != 1 ||
			bde[slot].bde_hdrcmplt != 1 || bde[slot].bde_seesent != 0 || 
			bde[slot].bde_rcount != 0 || bde[slot].bde_dcount != 0 || 
			bde[slot].bde_ccount != 0 || bde[slot].bde_ifname[0] != '\0') e(0);

		found++;
	}
	if (found != 1) e(0);

	close(fd);

	oldlen = bdesize;
	if (sysctl(mib, len, bde, &oldlen, NULL, 0) == -1 || oldlen % sizeof(*bde)) e(0);

	for (size_t slot = 0; slot < oldlen / sizeof(*bde); slot++) {
		if (bde[slot].bde_pid == getpid()) e(0);
	}

	free(bde);
}

/*
 * Test privileged operations as an unprivileged caller.
 */
#include <errno.h>
#include <limits.h>
#include <pwd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>
#include <sys/sysctl.h>
#include <unistd.h>
#include <sys/wait.h>
#include <fcntl.h>

#define NONROOT_USER "someuser"
#define _PATH_BPF "/dev/bpf"

static void handle_error(int condition) {
    if (condition) {
        fprintf(stderr, "An error occurred\n");
        exit(EXIT_FAILURE);
    }
}

static void test94k(void) {
    struct passwd *pw;
    pid_t pid;
    size_t len, oldlen;
    int mib[5], status;

    pid = fork();
    handle_error(pid == -1);

    if (pid == 0) { // Child process
        pw = getpwnam(NONROOT_USER);
        handle_error(pw == NULL || setuid(pw->pw_uid) != 0);

        int fd = open(_PATH_BPF, O_RDWR);
        handle_error(fd != -1 || errno != EACCES);

        memset(mib, 0, sizeof(mib));
        len = sizeof(mib) / sizeof(mib[0]);
        handle_error(sysctlnametomib("net.bpf.peers", mib, &len) != 0 || len != 3);
        
        mib[len++] = sizeof(struct bpf_d_ext);
        mib[len++] = INT_MAX;

        handle_error(sysctl(mib, len, NULL, &oldlen, NULL, 0) != -1 || errno != EPERM);

        exit(EXIT_SUCCESS);
    } 

    // Parent process
    handle_error(waitpid(pid, &status, 0) != pid);
    handle_error(!WIFEXITED(status) || WEXITSTATUS(status) != 0);
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
#include <sys/types.h>
#include <sys/socket.h>
#include <net/if.h>
#include <errno.h>
#include <netinet/in.h>
#include <netinet/if_ether.h>
#include <netinet/ip.h>
#include <netinet/ip6.h>
#include <netinet/udp.h>
#include <ifaddrs.h>
#include <net/if_dl.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <arpa/inet.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/ioctl.h>
#include <sys/errno.h>

#define ETHER_ADDR_LEN 6
#define TEST_PORT_B 12345
#define DLT_EN10MB 1
#define LINK_STATE_DOWN 0

static int get_setting_use_network() {
    return 1; // Placeholder function for checking network settings
}

size_t test94_make_pkt(uint8_t *buf, size_t len, int v6) {
    // Function stub for packet creation
    if (v6) {
        // Prepare an IPv6 packet
    } else {
        // Prepare an IPv4 packet
    }
    return 0; // Return the offset for the data
}

static void e(int error) {
    perror("Error");
    exit(EXIT_FAILURE);
}

static void test94l(void) {
    struct sockaddr_in sin;
    struct sockaddr_in6 sin6;
    struct sockaddr_dl sdl;
    struct ifreq ifr;
    struct ifaddrs *ifa, *ifp = NULL;
    struct if_data *ifdata;
    uint8_t buf[sizeof(struct ether_header) + MAX(sizeof(struct ip), sizeof(struct ip6_hdr)) + sizeof(struct udphdr) + 6];
    struct ether_header ether;
    const uint8_t ether_src[ETHER_ADDR_LEN] = { 0x02, 0x00, 0x01, 0x12, 0x34, 0x56 };
    unsigned int val;
    size_t off;
    int bfd = -1, sfd = -1;

    if (!get_setting_use_network()) return;

    memset(&ifr, 0, sizeof(ifr));
    memset(&ether, 0, sizeof(ether));

    if (getifaddrs(&ifa) != 0) e(errno);

    for (ifp = ifa; ifp != NULL; ifp = ifp->ifa_next) {
        if (!(ifp->ifa_flags & IFF_UP) || ifp->ifa_addr == NULL || ifp->ifa_addr->sa_family != AF_LINK) continue;

        ifdata = (struct if_data *)ifp->ifa_data;
        if (ifdata && ifdata->ifi_type == IFT_ETHER && ifdata->ifi_link_state != LINK_STATE_DOWN) {
            strlcpy(ifr.ifr_name, ifp->ifa_name, sizeof(ifr.ifr_name));

            memcpy(&sdl, (struct sockaddr_dl *)ifp->ifa_addr, offsetof(struct sockaddr_dl, sdl_data));
            if (sdl.sdl_alen != sizeof(ether.ether_dhost)) e(0);
            memcpy(ether.ether_dhost, ((struct sockaddr_dl *)ifp->ifa_addr)->sdl_data + sdl.sdl_nlen, sdl.sdl_alen);
            break;
        }
    }

    freeifaddrs(ifa);

    if (ifp == NULL) return;

    if ((bfd = open(_PATH_BPF, O_RDWR)) < 0) e(errno);

    if (ioctl(bfd, BIOCSETIF, &ifr) != 0) e(errno);

    if (ioctl(bfd, BIOCGDLT, &val) != 0) e(errno);
    if (val != DLT_EN10MB) e(0);

    val = 1;
    if (ioctl(bfd, BIOCSFEEDBACK, &val) != 0) e(errno);

    if ((sfd = socket(AF_INET, SOCK_DGRAM, 0)) < 0) e(errno);

    memset(&sin, 0, sizeof(sin));
    sin.sin_family = AF_INET;
    sin.sin_port = htons(TEST_PORT_B);
    sin.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if (bind(sfd, (struct sockaddr *)&sin, sizeof(sin)) != 0) e(errno);

    memcpy(ether.ether_shost, ether_src, sizeof(ether.ether_shost));
    ether.ether_type = htons(ETHERTYPE_IP);

    memcpy(buf, &ether, sizeof(ether));
    off = sizeof(ether);
    off += test94_make_pkt(buf + off, 6, 0);
    if (off + 6 > sizeof(buf)) e(0);
    memcpy(buf + off, "Hello!", 6);

    if (write(bfd, buf, off + 6) != off + 6) e(errno);

    if (recv(sfd, buf, sizeof(buf), MSG_DONTWAIT) != -1 || errno != EWOULDBLOCK) e(0);

    if (close(sfd) != 0) e(errno);

    if ((sfd = socket(AF_INET6, SOCK_DGRAM, 0)) < 0) e(errno);

    memset(&sin6, 0, sizeof(sin6));
    sin6.sin6_family = AF_INET6;
    sin6.sin6_port = htons(TEST_PORT_B);
    memcpy(&sin6.sin6_addr, &in6addr_loopback, sizeof(sin6.sin6_addr));
    if (bind(sfd, (struct sockaddr *)&sin6, sizeof(sin6)) != 0) e(errno);

    ether.ether_type = htons(ETHERTYPE_IPV6);

    memcpy(buf, &ether, sizeof(ether));
    off = sizeof(ether);
    off += test94_make_pkt(buf + off, 6, 1);
    if (off + 6 > sizeof(buf)) e(0);
    memcpy(buf + off, "Hello!", 6);

    if (write(bfd, buf, off + 6) != off + 6) e(errno);

    if (recv(sfd, buf, sizeof(buf), MSG_DONTWAIT) != -1 || errno != EWOULDBLOCK) e(0);

    if (close(sfd) != 0) e(errno);
    if (close(bfd) != 0) e(errno);
}

/*
 * Test program for LWIP BPF.
 */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define ITERATIONS 1000

void start(int code);
void quit();
void test94a();
void test94b();
void test94c();
void test94d();
void test94e();
void test94f();
void test94g();
void test94h();
void test94i();
void test94j();
void test94k();
void test94l();

int main(int argc, char** argv) {
    int m = 0xFFF;
    if (argc == 2) {
        m = atoi(argv[1]);
        if (m < 0) {
            fprintf(stderr, "Invalid input\n");
            return EXIT_FAILURE;
        }
    }

    start(94);
    srand48(time(NULL));

    for (int i = 0; i < ITERATIONS; i++) {
        if (m & 0x001) test94a();
        if (m & 0x002) test94b();
        if (m & 0x004) test94c();
        if (m & 0x008) test94d();
        if (m & 0x010) test94e();
        if (m & 0x020) test94f();
        if (m & 0x040) test94g();
        if (m & 0x080) test94h();
        if (m & 0x100) test94i();
        if (m & 0x200) test94j();
        if (m & 0x400) test94k();
        if (m & 0x800) test94l();
    }

    quit();
    return EXIT_SUCCESS;
}
