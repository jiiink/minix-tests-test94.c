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

	hdrlen = BPF_WORDALIGN(sizeof(struct bpf_hdr)) + sizeof(struct ip) +
	    sizeof(struct udphdr) + sizeof(seq);

	len = 16;
	while (len <= hdrlen) {
		len <<= 1;
	}
	
	if (len > size) {
		e(0);
	}

	hdrlen = BPF_WORDALIGN(hdrlen - sizeof(seq));

	while (size > 0) {
		size_t data_len = len - hdrlen;
		
		memset(buf, 'Y', data_len);
		
		if (data_len > sizeof(seq)) {
			buf[sizeof(seq)] = 'X';
		}
		
		buf[data_len - 1] = 'Z';
		memcpy(buf, &seq, sizeof(seq));

		if (write(fd, buf, data_len) != data_len) {
			e(0);
		}

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
static size_t calculate_header_length(void)
{
    return BPF_WORDALIGN(BPF_WORDALIGN(sizeof(struct bpf_hdr)) +
                         sizeof(struct ip) + sizeof(struct udphdr));
}

static size_t calculate_packet_length(size_t hdrlen, size_t buffer_size)
{
    return hdrlen + sizeof(uint32_t) + lrand48() % (buffer_size / 10);
}

static void fill_packet_buffer(uint8_t *buf, uint32_t seq, size_t payload_len)
{
    memset(buf, 'Y', payload_len);
    if (payload_len > sizeof(seq))
        buf[sizeof(seq)] = 'X';
    buf[payload_len - 1] = 'Z';
    memcpy(buf, &seq, sizeof(seq));
}

static void send_packet(int fd, uint8_t *buf, size_t payload_len)
{
    if (write(fd, buf, payload_len) != payload_len)
        e(0);
}

static void test94_fill_random(int fd, uint8_t *buf, size_t size)
{
    size_t hdrlen = calculate_header_length();
    ssize_t left = (ssize_t)size;
    uint32_t seq = 1;

    while (left >= 0) {
        size_t len = calculate_packet_length(hdrlen, size);
        size_t payload_len = len - hdrlen;
        
        fill_packet_buffer(buf, seq, payload_len);
        send_packet(fd, buf, payload_len);
        
        left -= BPF_WORDALIGN(len);
        seq++;
    }
}

/*
 * Send a UDP packet with a specific size of 'size' bytes and sequence number
 * 'seq' on socket 'fd', using 'buf' as scratch buffer.
 */
static void test94_add_specific(int fd, uint8_t *buf, size_t size, uint32_t seq)
{
    const char FILL_CHAR = 'Y';
    const char MARKER_CHAR = 'X';
    const char END_CHAR = 'Z';
    
    size += sizeof(seq);
    
    memset(buf, FILL_CHAR, size);
    
    if (size > sizeof(seq)) {
        buf[sizeof(seq)] = MARKER_CHAR;
    }
    
    buf[size - 1] = END_CHAR;
    memcpy(buf, &seq, sizeof(seq));
    
    if (write(fd, buf, size) != size) {
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
	const size_t RANDOM_SIZE_DIVISOR = 10;
	test94_add_specific(fd, buf, lrand48() % (size / RANDOM_SIZE_DIVISOR), seq);
}

/*
 * Check whether the packet in 'buf' of 'caplen' captured bytes out of
 * 'datalen' data bytes is one we sent.  If so, return an offset to the packet
 * data.  If not, return a negative value.
 */
static int check_ip_header(const struct ip *ip)
{
	if (ip->ip_v != IPVERSION)
		return -1;
	if (ip->ip_hl != sizeof(struct ip) >> 2)
		return -1;
	if (ip->ip_p != IPPROTO_UDP)
		return -1;
	return 0;
}

static int check_udp_header(const struct udphdr *uh)
{
	if (uh->uh_sport != htons(TEST_PORT_A))
		return -1;
	if (uh->uh_dport != htons(TEST_PORT_B))
		return -1;
	return 0;
}

static ssize_t
test94_check_pkt(uint8_t * buf, ssize_t caplen, ssize_t datalen)
{
	struct ip ip;
	struct udphdr uh;

	if (caplen < sizeof(ip))
		return -1;

	memcpy(&ip, buf, sizeof(ip));

	if (check_ip_header(&ip) < 0)
		return -1;

	if (caplen - sizeof(ip) < sizeof(uh))
		return -1;

	memcpy(&uh, buf + sizeof(ip), sizeof(uh));

	if (check_udp_header(&uh) < 0)
		return -1;

	if (datalen - sizeof(ip) != ntohs(uh.uh_ulen)) e(0);

	return sizeof(ip) + sizeof(uh);
}

/*
 * Check whether the capture in 'buf' of 'len' bytes looks like a valid set of
 * captured packets.  The valid packets start from sequence number 'seq'; the
 * next expected sequence number is returned.  If 'filtered' is set, there
 * should be no other packets in the capture; otherwise, other packets are
 * ignored.
 */
static uint32_t process_packet_sequence(uint8_t *buf, ssize_t off, ssize_t caplen, ssize_t datalen, uint32_t seq)
{
    uint32_t nseq;
    
    memcpy(&nseq, &buf[off], sizeof(nseq));
    if (nseq != seq) e(0);
    
    return seq + 1;
}

static void validate_packet_data(uint8_t *buf, ssize_t off, ssize_t caplen, ssize_t datalen)
{
    if (off >= caplen) return;
    
    if (off < caplen && off < datalen - 1) {
        if (buf[off] != 'X') e(0);
        
        for (off++; off < caplen && off < datalen - 1; off++) {
            if (buf[off] != 'Y') e(0);
        }
    }
    
    if (off < caplen && off == datalen - 1 && buf[off] != 'Z') e(0);
}

static void validate_header_fields(struct bpf_hdr *bh, uint32_t *caplen, uint32_t *datalen)
{
    if (bh->bh_tstamp.tv_sec == 0 && bh->bh_tstamp.tv_usec == 0) e(0);
    
    if (caplen != NULL) {
        if (bh->bh_caplen != *caplen) e(0);
        if (bh->bh_datalen != *datalen) e(0);
    } else {
        if (bh->bh_datalen != bh->bh_caplen) e(0);
    }
    
    if (bh->bh_hdrlen != BPF_WORDALIGN(sizeof(struct bpf_hdr))) e(0);
}

static uint32_t process_single_packet(uint8_t **buf, ssize_t *len, uint32_t seq, int filtered, uint32_t **caplen, uint32_t **datalen)
{
    struct bpf_hdr bh;
    ssize_t off;
    
    memcpy(&bh, *buf, sizeof(bh));
    
    validate_header_fields(&bh, *caplen, *datalen);
    
    if (*caplen != NULL) {
        (*caplen)++;
        (*datalen)++;
    }
    
    if (bh.bh_hdrlen + BPF_WORDALIGN(bh.bh_caplen) > *len) e(0);
    
    *buf += bh.bh_hdrlen;
    *len -= bh.bh_hdrlen;
    
    off = test94_check_pkt(*buf, bh.bh_caplen, bh.bh_datalen);
    
    if (off < 0) {
        if (filtered) e(0);
        *buf += BPF_WORDALIGN(bh.bh_caplen);
        *len -= BPF_WORDALIGN(bh.bh_caplen);
        return seq;
    }
    
    if (bh.bh_caplen < off + sizeof(seq)) e(0);
    
    seq = process_packet_sequence(*buf, off, bh.bh_caplen, bh.bh_datalen, seq);
    
    off += sizeof(uint32_t);
    validate_packet_data(*buf, off, bh.bh_caplen, bh.bh_datalen);
    
    *buf += BPF_WORDALIGN(bh.bh_caplen);
    *len -= BPF_WORDALIGN(bh.bh_caplen);
    
    return seq;
}

static uint32_t test94_check(uint8_t *buf, ssize_t len, uint32_t seq, int filtered, uint32_t *caplen, uint32_t *datalen)
{
    while (len > 0) {
        if (len < BPF_WORDALIGN(sizeof(struct bpf_hdr))) e(0);
        
        seq = process_single_packet(&buf, &len, seq, filtered, &caplen, &datalen);
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
static int open_bpf_device(void)
{
    int fd = open(_PATH_BPF, O_RDWR);
    if (fd < 0) e(0);
    return fd;
}

static unsigned int configure_buffer_size(int fd, unsigned int requested_size)
{
    unsigned int size = requested_size;
    
    if (size != 0 && ioctl(fd, BIOCSBLEN, &size) != 0) e(0);
    if (ioctl(fd, BIOCGBLEN, &size) != 0) e(0);
    if (size < 1024 || size > BPF_MAXBUFSIZE) e(0);
    
    return size;
}

static void install_bpf_filter(int fd)
{
    struct bpf_program bf;
    
    memset(&bf, 0, sizeof(bf));
    bf.bf_len = __arraycount(test94_filter);
    bf.bf_insns = test94_filter;
    if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);
}

static void bind_to_loopback(int fd)
{
    struct ifreq ifr;
    unsigned int dlt;
    
    memset(&ifr, 0, sizeof(ifr));
    strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
    if (ioctl(fd, BIOCSETIF, &ifr) != 0) e(0);
    
    if (ioctl(fd, BIOCGDLT, &dlt) != 0) e(0);
    if (dlt != DLT_RAW) e(0);
}

static void setup_socket_address(struct sockaddr_in *addr, uint16_t port)
{
    memset(addr, 0, sizeof(*addr));
    addr->sin_family = AF_INET;
    addr->sin_port = htons(port);
    addr->sin_addr.s_addr = htonl(INADDR_LOOPBACK);
}

static int create_udp_socket(void)
{
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) e(0);
    return fd;
}

static void bind_and_connect_socket(int fd, struct sockaddr_in *local, 
                                   struct sockaddr_in *remote)
{
    if (bind(fd, (struct sockaddr *)local, sizeof(*local)) != 0) e(0);
    if (connect(fd, (struct sockaddr *)remote, sizeof(*remote)) != 0) e(0);
}

static size_t
test94_setup(int * fd, int * fd2, int * fd3, uint8_t ** buf, unsigned int size,
	int set_filter)
{
    struct sockaddr_in sinA, sinB;
    
    *fd = open_bpf_device();
    size = configure_buffer_size(*fd, size);
    
    if ((*buf = malloc(size)) == NULL) e(0);
    
    if (set_filter) {
        install_bpf_filter(*fd);
    }
    
    bind_to_loopback(*fd);
    
    setup_socket_address(&sinA, TEST_PORT_A);
    setup_socket_address(&sinB, TEST_PORT_B);
    
    *fd2 = create_udp_socket();
    bind_and_connect_socket(*fd2, &sinA, &sinB);
    
    *fd3 = create_udp_socket();
    bind_and_connect_socket(*fd3, &sinB, &sinA);
    
    return size;
}

/*
 * Clean up resources allocated by test94_setup().
 */
static void
test94_cleanup(int fd, int fd2, int fd3, uint8_t * buf)
{
	if (close(fd3) != 0) e(0);
	if (close(fd2) != 0) e(0);
	free(buf);
	if (close(fd) != 0) e(0);
}

/*
 * Test reading packets from a BPF device, using regular mode.
 */
static void test94_validate_buffer_size(int fd, uint8_t *buf, size_t size) {
    if (read(fd, buf, size - 1) != -1) e(0);
    if (errno != EINVAL) e(0);
    if (read(fd, buf, size + 1) != -1) e(0);
    if (errno != EINVAL) e(0);
    if (read(fd, buf, sizeof(struct bpf_hdr)) != -1) e(0);
    if (errno != EINVAL) e(0);
}

static void test94_install_filter(int fd) {
    struct bpf_program bf;
    memset(&bf, 0, sizeof(bf));
    bf.bf_len = __arraycount(test94_filter);
    bf.bf_insns = test94_filter;
    if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);
}

static void test94_check_select_empty(int fd) {
    struct timeval tv;
    fd_set fds;
    int bytes;
    
    tv.tv_sec = 0;
    tv.tv_usec = 0;
    FD_ZERO(&fds);
    FD_SET(fd, &fds);
    if (select(fd + 1, &fds, NULL, NULL, &tv) != 0) e(0);
    if (FD_ISSET(fd, &fds)) e(0);
    
    if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);
    if (bytes != 0) e(0);
}

static void test94_wait_select_ready(int fd, int *bytes) {
    fd_set fds;
    
    FD_ZERO(&fds);
    FD_SET(fd, &fds);
    if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) e(0);
    if (!FD_ISSET(fd, &fds)) e(0);
    
    if (bytes) {
        if (ioctl(fd, FIONREAD, bytes) != 0) e(0);
    }
}

static pid_t test94_fork_child(void (*child_func)(int, uint8_t*, size_t, uint32_t), 
                               int fd2, uint8_t *buf, size_t size, uint32_t seq) {
    pid_t pid = fork();
    switch (pid) {
    case 0:
        errct = 0;
        child_func(fd2, buf, size, seq);
        exit(errct);
    case -1:
        e(0);
        break;
    default:
        break;
    }
    return pid;
}

static void test94_child_fill_after_delay(int fd2, uint8_t *buf, size_t size, uint32_t seq) {
    usleep(SLEEP_TIME);
    test94_fill_random(fd2, buf, size);
}

static void test94_child_add_after_delay(int fd2, uint8_t *buf, size_t size, uint32_t seq) {
    signal(SIGUSR1, test94_signal);
    usleep(SLEEP_TIME);
    test94_add_random(fd2, buf, size, seq + 1);
    usleep(SLEEP_TIME);
    if (got_signal != 0) e(0);
    pause();
    if (got_signal != 1) e(0);
}

static void test94_child_single_add(int fd2, uint8_t *buf, size_t size, uint32_t seq) {
    usleep(SLEEP_TIME);
    test94_add_random(fd2, buf, size, seq);
}

static void test94_child_read_interrupted(int fd, uint8_t *buf, size_t size, uint32_t seq) {
    signal(SIGUSR1, test94_signal);
    if (read(fd, buf, size) != -1) e(0);
    if (errno != EINTR) e(0);
    if (got_signal != 1) e(0);
}

static void test94_child_delayed_add_then_read(int fd, uint8_t *buf, size_t size, uint32_t seq) {
    signal(SIGUSR1, test94_signal);
    if (read(fd, buf, size) != -1) e(0);
    if (errno != EINTR) e(0);
    if (got_signal != 1) e(0);
}

static void test94_wait_child(pid_t pid) {
    int status;
    if (wait(&status) != pid) e(0);
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);
}

static void test94_set_timeout(int fd, long usec) {
    struct timeval tv;
    tv.tv_sec = 0;
    tv.tv_usec = usec;
    if (ioctl(fd, BIOCSRTIMEOUT, &tv) != 0) e(0);
}

static void test94_test_filled_buffer(int fd, int fd2, uint8_t *buf, size_t size) {
    pid_t pid;
    ssize_t len;
    
    pid = test94_fork_child(test94_child_fill_after_delay, fd2, buf, size, 0);
    
    len = read(fd, buf, size);
    if (len < size * 3/4) e(0);
    if (len > size) e(0);
    test94_check(buf, len, 1, 0, NULL, NULL);
    
    test94_wait_child(pid);
}

static uint32_t test94_test_select_wakeup(int fd, int fd2, uint8_t *buf, size_t size) {
    pid_t pid;
    ssize_t len;
    uint32_t seq;
    int bytes;
    
    test94_check_select_empty(fd);
    
    pid = test94_fork_child(test94_child_fill_after_delay, fd2, buf, size, 0);
    
    test94_wait_select_ready(fd, &bytes);
    
    if (select(fd + 1, NULL, NULL, NULL, NULL) != 1) e(0);
    
    len = read(fd, buf, size);
    if (len < size * 3/4) e(0);
    if (len > size) e(0);
    seq = test94_check(buf, len, 1, 1, NULL, NULL);
    if (len != bytes) e(0);
    
    test94_wait_child(pid);
    
    test94_check_select_empty(fd);
    
    return seq;
}

static void test94_test_read_timeout(int fd, int fd2, uint8_t *buf, size_t size, uint32_t seq) {
    pid_t pid;
    ssize_t len;
    
    got_signal = 0;
    
    pid = test94_fork_child(test94_child_add_after_delay, fd2, buf, size, seq);
    
    test94_set_timeout(fd, SLEEP_TIME * 3);
    
    len = read(fd, buf, size);
    if (len <= 0) e(0);
    if (len >= size * 3/4) e(0);
    if (test94_check(buf, len, seq, 1, NULL, NULL) != seq + 2) e(0);
    
    if (kill(pid, SIGUSR1) != 0) e(0);
    test94_wait_child(pid);
    
    test94_set_timeout(fd, SLEEP_TIME);
    
    if (read(fd, buf, size) != -1) e(0);
    if (errno != EAGAIN) e(0);
}

static void test94_test_blocking_interrupt(int fd, int fd2, uint8_t *buf, size_t size) {
    pid_t pid;
    
    test94_set_timeout(fd, 0);
    
    pid = fork();
    if (pid == 0) {
        test94_child_read_interrupted(fd, buf, size, 0);
        exit(errct);
    }
    if (pid == -1) e(0);
    
    usleep(SLEEP_TIME * 2);
    if (kill(pid, SIGUSR1) != 0) e(0);
    test94_wait_child(pid);
    
    pid = fork();
    if (pid == 0) {
        test94_child_delayed_add_then_read(fd, buf, size, 0);
        exit(errct);
    }
    if (pid == -1) e(0);
    
    usleep(SLEEP_TIME);
    test94_add_random(fd2, buf, size, 2);
    usleep(SLEEP_TIME);
    
    if (kill(pid, SIGUSR1) != 0) e(0);
    test94_wait_child(pid);
}

static void test94_test_nonblocking_reads(int fd, int fd2, uint8_t *buf, size_t size) {
    int fl;
    ssize_t len;
    uint32_t seq;
    
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
}

static void test94_test_select_single_packet(int fd, int fd2, uint8_t *buf, size_t size) {
    struct timeval tv;
    fd_set fds;
    pid_t pid;
    
    test94_set_timeout(fd, SLEEP_TIME * 2);
    
    pid = test94_fork_child(test94_child_single_add, fd2, buf, size, 1);
    
    tv.tv_sec = 1;
    tv.tv_usec = 0;
    FD_ZERO(&fds);
    FD_SET(fd, &fds);
    if (select(fd + 1, &fds, NULL, NULL, &tv) != 0) e(0);
    
    test94_wait_child(pid);
}

static void test94a(void) {
    int fd, fd2, fd3;
    uint8_t *buf;
    size_t size;
    uint32_t seq;
    
    subtest = 1;
    
    size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 0);
    
    test94_test_filled_buffer(fd, fd2, buf, size);
    test94_validate_buffer_size(fd, buf, size);
    test94_install_filter(fd);
    seq = test94_test_select_wakeup(fd, fd2, buf, size);
    test94_test_read_timeout(fd, fd2, buf, size, seq);
    test94_test_blocking_interrupt(fd, fd2, buf, size);
    test94_test_nonblocking_reads(fd, fd2, buf, size);
    test94_test_select_single_packet(fd, fd2, buf, size);
    
    test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test reading packets from a BPF device, using immediate mode.
 */
#define SLEEP_TIME_USEC SLEEP_TIME
#define PACKET_SIZE_THRESHOLD(size) ((size) * 3 / 4)

static int set_immediate_mode(int fd)
{
	unsigned int val = 1;
	return ioctl(fd, BIOCIMMEDIATE, &val);
}

static int check_buffer_empty(int fd)
{
	struct timeval tv = {0, 0};
	fd_set fds;
	int bytes;
	
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv) != 0) return -1;
	
	if (ioctl(fd, FIONREAD, &bytes) != 0) return -1;
	return (bytes == 0) ? 0 : -1;
}

static int check_buffer_ready(int fd, int *bytes)
{
	struct timeval tv = {0, 0};
	fd_set fds;
	
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, &tv) != 1) return -1;
	if (!FD_ISSET(fd, &fds)) return -1;
	
	if (ioctl(fd, FIONREAD, bytes) != 0) return -1;
	return 0;
}

static int wait_for_data(int fd)
{
	fd_set fds;
	
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) return -1;
	if (!FD_ISSET(fd, &fds)) return -1;
	return 0;
}

static ssize_t read_and_verify_full_buffer(int fd, uint8_t *buf, size_t size, uint32_t expected_seq)
{
	ssize_t len = read(fd, buf, size);
	if (len < PACKET_SIZE_THRESHOLD(size)) e(0);
	if (len > size) e(0);
	return test94_check(buf, len, expected_seq, 1, NULL, NULL);
}

static uint32_t read_and_verify_single_packet(int fd, uint8_t *buf, size_t size, uint32_t expected_seq)
{
	ssize_t len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= PACKET_SIZE_THRESHOLD(size)) e(0);
	return test94_check(buf, len, expected_seq, 1, NULL, NULL);
}

static uint32_t read_and_verify_multiple_packets(int fd, uint8_t *buf, size_t size, uint32_t expected_seq)
{
	ssize_t len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= PACKET_SIZE_THRESHOLD(size)) e(0);
	return test94_check(buf, len, expected_seq, 1, NULL, NULL);
}

static void child_add_packet(int fd2, uint8_t *buf, size_t size, uint32_t seq)
{
	errct = 0;
	usleep(SLEEP_TIME_USEC);
	test94_add_random(fd2, buf, size, seq);
	exit(errct);
}

static void wait_for_child(pid_t pid)
{
	int status;
	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);
}

static void test_suspended_read(int fd, int fd2, uint8_t *buf, size_t size, uint32_t seq)
{
	pid_t pid = fork();
	
	if (pid == 0) {
		child_add_packet(fd2, buf, size, seq);
	} else if (pid == -1) {
		e(0);
	} else {
		read_and_verify_single_packet(fd, buf, size, seq);
		wait_for_child(pid);
	}
}

static void test_suspended_select(int fd, int fd2, uint8_t *buf, size_t size, uint32_t seq)
{
	pid_t pid = fork();
	int bytes;
	
	if (pid == 0) {
		child_add_packet(fd2, buf, size, seq);
	} else if (pid == -1) {
		e(0);
	} else {
		if (wait_for_data(fd) != 0) e(0);
		if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);
		if (wait_for_data(fd) != 0) e(0);
		
		ssize_t len = read_and_verify_single_packet(fd, buf, size, seq);
		if (len != bytes) e(0);
		
		wait_for_child(pid);
	}
}

static void test_nonblocking_reads(int fd, int fd2, uint8_t *buf, size_t size)
{
	int fl;
	uint32_t seq;
	ssize_t len;
	
	if ((fl = fcntl(fd, F_GETFL)) == -1) e(0);
	if (fcntl(fd, F_SETFL, fl | O_NONBLOCK) != 0) e(0);
	
	if (read(fd, buf, size) != -1) e(0);
	if (errno != EAGAIN) e(0);
	
	test94_fill_random(fd2, buf, size);
	
	seq = read_and_verify_full_buffer(fd, buf, size, 1);
	
	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= PACKET_SIZE_THRESHOLD(size)) e(0);
	if (test94_check(buf, len, seq, 1, NULL, NULL) != seq + 1) e(0);
	
	if (fcntl(fd, F_SETFL, fl) != 0) e(0);
}

static void test94b(void)
{
	struct timeval tv;
	uint8_t *buf;
	size_t size;
	ssize_t len;
	uint32_t seq;
	int fd, fd2, fd3, bytes;
	
	subtest = 2;
	
	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);
	
	if (set_immediate_mode(fd) != 0) e(0);
	
	if (check_buffer_empty(fd) != 0) e(0);
	
	test94_fill_random(fd2, buf, size);
	
	if (check_buffer_ready(fd, &bytes) != 0) e(0);
	
	len = read(fd, buf, size);
	if (len < PACKET_SIZE_THRESHOLD(size)) e(0);
	if (len > size) e(0);
	seq = test94_check(buf, len, 1, 1, NULL, NULL);
	
	if (len != bytes) e(0);
	
	if (check_buffer_ready(fd, &bytes) != 0) e(0);
	
	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= PACKET_SIZE_THRESHOLD(size)) e(0);
	if (test94_check(buf, len, seq, 1, NULL, NULL) != seq + 1) e(0);
	
	if (len != bytes) e(0);
	
	if (check_buffer_empty(fd) != 0) e(0);
	
	test94_add_random(fd2, buf, size, seq + 1);
	test94_add_random(fd2, buf, size, seq + 2);
	
	if (check_buffer_ready(fd, &bytes) != 0) e(0);
	
	if (read_and_verify_multiple_packets(fd, buf, size, seq + 1) != seq + 3) e(0);
	
	if (len != bytes) e(0);
	
	test_suspended_read(fd, fd2, buf, size, seq + 3);
	
	test_suspended_select(fd, fd2, buf, size, seq + 4);
	
	test_nonblocking_reads(fd, fd2, buf, size);
	
	tv.tv_sec = 0;
	tv.tv_usec = SLEEP_TIME_USEC;
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
static void check_bpf_stats(int fd, uint32_t expected_capt, uint32_t expected_drop) {
	struct bpf_stat bs;
	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != expected_capt) e(0);
	if (bs.bs_recv < bs.bs_capt) e(0);
	if (bs.bs_drop != expected_drop) e(0);
}

static void check_fionread(int fd, int expected_bytes) {
	int bytes;
	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);
	if (bytes != expected_bytes) e(0);
}

static void verify_select_ready(int fd) {
	fd_set fds;
	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);
}

static void read_and_check(int fd, uint8_t *buf, size_t size, uint32_t seq, uint32_t expected_end) {
	if (read(fd, buf, size) != size) e(0);
	uint32_t result = test94_check(buf, size, seq, 1, NULL, NULL);
	if (expected_end != 0 && result != expected_end) e(0);
}

static void set_nonblocking(int fd) {
	int fl = fcntl(fd, F_GETFL);
	if (fl == -1) e(0);
	if (fcntl(fd, F_SETFL, fl | O_NONBLOCK) != 0) e(0);
}

static void verify_eagain(int fd, uint8_t *buf, size_t size) {
	if (read(fd, buf, size) != -1) e(0);
	if (errno != EAGAIN) e(0);
}

static pid_t fork_fill_exact(int fd2, uint8_t *buf, size_t size, uint32_t seq) {
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

static void wait_for_child(pid_t pid) {
	int status;
	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);
}

static void test94c(void) {
	struct bpf_stat bs;
	uint8_t *buf;
	size_t size;
	pid_t pid;
	uint32_t count, seq;
	int fd, fd2, fd3;

	subtest = 3;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != 0) e(0);
	if (bs.bs_drop != 0) e(0);

	count = test94_fill_exact(fd2, buf, size, 0);
	check_bpf_stats(fd, count, 0);
	check_fionread(fd, size);
	verify_select_ready(fd);
	read_and_check(fd, buf, size, 0, 0);

	seq = test94_fill_exact(fd2, buf, size, 1);
	test94_fill_exact(fd2, buf, size, seq);
	check_bpf_stats(fd, count * 3, 0);

	test94_add_random(fd2, buf, size, 0);
	check_bpf_stats(fd, count * 3 + 1, 1);

	test94_add_random(fd2, buf, size, 0);
	check_bpf_stats(fd, count * 3 + 2, 2);

	check_fionread(fd, size);
	read_and_check(fd, buf, size, 1, seq);
	read_and_check(fd, buf, size, seq, count * 2 + 1);

	pid = fork_fill_exact(fd2, buf, size, 1);
	read_and_check(fd, buf, size, 1, 0);
	wait_for_child(pid);

	pid = fork_fill_exact(fd2, buf, size, seq);
	verify_select_ready(fd);
	set_nonblocking(fd);
	read_and_check(fd, buf, size, seq, 0);
	verify_eagain(fd, buf, size);
	wait_for_child(pid);

	check_bpf_stats(fd, count * 5 + 2, 2);

	test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test receipt of large packets on BPF devices.  Large packets should be
 * truncated to the size of the buffer, but unless the filter specifies a
 * smaller capture size, no more than that.
 */
static void verify_bpf_header(const struct bpf_hdr *bh, size_t size, int datalen)
{
	if (bh->bh_hdrlen != BPF_WORDALIGN(sizeof(*bh))) e(0);
	if (bh->bh_caplen != size - BPF_WORDALIGN(sizeof(*bh))) e(0);
	if (bh->bh_datalen != sizeof(struct ip) + sizeof(struct udphdr) + datalen) e(0);
}

static void verify_packet_markers(const uint8_t *buf, size_t size)
{
	size_t data_offset = BPF_WORDALIGN(sizeof(struct bpf_hdr)) + 
	                     sizeof(struct ip) + sizeof(struct udphdr);
	
	if (buf[data_offset] != 'X') e(0);
	if (buf[size - 2] != 'Y') e(0);
	if (buf[size - 1] != 'Z') e(0);
}

static uint8_t* create_test_packet(size_t size, int datalen)
{
	uint8_t *buf2 = malloc(datalen);
	if (buf2 == NULL) e(0);
	
	memset(buf2, 'Y', datalen);
	buf2[0] = 'X';
	
	size_t marker_pos = size - sizeof(struct udphdr) - sizeof(struct ip) -
	                   BPF_WORDALIGN(sizeof(struct bpf_hdr)) - 1;
	buf2[marker_pos] = 'Z';
	
	return buf2;
}

static void write_and_verify_packet(int fd, int fd2, uint8_t *buf, uint8_t *buf2, 
                                   size_t size, int datalen)
{
	struct bpf_hdr bh;
	
	if (write(fd2, buf2, datalen) != datalen) e(0);
	if (read(fd, buf, size) != size) e(0);
	
	memcpy(&bh, buf, sizeof(bh));
	verify_bpf_header(&bh, size, datalen);
	verify_packet_markers(buf, size);
}

static void test94d(void)
{
	#define TEST_BUFFER_SIZE 32768
	#define TEST_DATA_LENGTH 65000
	#define THREE_QUARTERS_THRESHOLD 3/4
	
	struct bpf_hdr bh;
	uint8_t *buf, *buf2;
	size_t size;
	ssize_t len;
	int fd, fd2, fd3;
	
	subtest = 4;
	
	size = test94_setup(&fd, &fd2, &fd3, &buf, TEST_BUFFER_SIZE, 1);
	if (size != TEST_BUFFER_SIZE) e(0);
	
	int datalen = TEST_DATA_LENGTH;
	if (setsockopt(fd2, SOL_SOCKET, SO_SNDBUF, &datalen, sizeof(datalen)) != 0) e(0);
	
	buf2 = create_test_packet(size, datalen);
	write_and_verify_packet(fd, fd2, buf, buf2, size, datalen);
	
	test94_add_random(fd2, buf, size, 1);
	
	if (write(fd2, buf2, datalen) != datalen) e(0);
	
	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= size * THREE_QUARTERS_THRESHOLD) e(0);
	if (test94_check(buf, len, 1, 1, NULL, NULL) != 2) e(0);
	
	if (read(fd, buf, size) != size) e(0);
	
	memcpy(&bh, buf, sizeof(bh));
	verify_bpf_header(&bh, size, datalen);
	verify_packet_markers(buf, size);
	
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
static void write_and_verify(int write_fd, int read_fd, char expected) {
    char c;
    if (write(write_fd, &expected, 1) != 1) e(0);
    if (read(read_fd, &c, 1) != 1) e(0);
    if (c != expected) e(0);
}

static void verify_stats_received(int fd) {
    struct bpf_stat bs;
    if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
    if (bs.bs_recv == 0) e(0);
}

static void verify_capture_stats(int fd, int filtered) {
    struct bpf_stat bs;
    if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
    
    if (filtered) {
        if (bs.bs_capt != 0) e(0);
        if (bs.bs_drop != 0) e(0);
    } else {
        if (bs.bs_capt == 0) e(0);
    }
}

static void flush_bpf(int fd) {
    if (ioctl(fd, BIOCFLUSH) != 0) e(0);
}

static void test94_comm(int fd, int fd2, int fd3, int filtered) {
    struct bpf_stat bs;
    
    write_and_verify(fd2, fd3, 'A');
    
    if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
    if (bs.bs_recv == 0) e(0);
    if (bs.bs_capt == 0) e(0);
    
    flush_bpf(fd);
    
    write_and_verify(fd3, fd2, 'B');
    
    verify_stats_received(fd);
    verify_capture_stats(fd, filtered);
    
    flush_bpf(fd);
}

/*
 * Test filter installation and mechanics.
 */
static int test94e_validate_filter(struct bpf_program *bf, int fd) {
	if (ioctl(fd, BIOCSETF, bf) != -1) {
		e(0);
		return 0;
	}
	if (errno != EINVAL) {
		e(0);
		return 0;
	}
	return 1;
}

static void test94e_setup_filter(struct bpf_program *bf, struct bpf_insn *insns, u_int len) {
	memset(bf, 0, sizeof(*bf));
	bf->bf_len = len;
	bf->bf_insns = insns;
}

static void test94e_clear_filter(int fd) {
	struct bpf_program bf;
	memset(&bf, 0, sizeof(bf));
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);
}

static void test94e_test_capture_size(int fd, int fd2, uint8_t *buf, size_t size, 
                                      uint32_t capture_limit, int seq_start, 
                                      uint32_t *caplen, uint32_t *datalen) {
	struct bpf_program bf;
	size_t plen = sizeof(struct ip) + sizeof(struct udphdr) + sizeof(uint32_t);
	size_t alen = BPF_WORDALIGN(plen + 1);
	
	test94_filter[__arraycount(test94_filter) - 1].k = capture_limit;
	test94e_setup_filter(&bf, test94_filter, __arraycount(test94_filter));
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);
	
	if (capture_limit == alen) {
		test94_add_specific(fd2, buf, alen + 1 - plen, seq_start);
		caplen[0] = alen;
		datalen[0] = alen + 1;
		
		test94_add_specific(fd2, buf, alen - plen, seq_start + 1);
		caplen[1] = alen;
		datalen[1] = alen;
		
		test94_add_specific(fd2, buf, alen + 3 - plen, seq_start + 2);
		caplen[2] = alen;
		datalen[2] = alen + 3;
		
		test94_add_specific(fd2, buf, alen - 1 - plen, seq_start + 3);
		caplen[3] = alen - 1;
		datalen[3] = alen - 1;
	} else {
		test94_add_specific(fd2, buf, alen + 2 - plen, seq_start);
		caplen[0] = alen + 1;
		datalen[0] = alen + 2;
		
		test94_add_specific(fd2, buf, alen + 1 - plen, seq_start + 1);
		caplen[1] = alen + 1;
		datalen[1] = alen + 1;
		
		test94_add_specific(fd2, buf, alen + 9 - plen, seq_start + 2);
		caplen[2] = alen + 1;
		datalen[2] = alen + 9;
		
		test94_add_specific(fd2, buf, alen - plen, seq_start + 3);
		caplen[3] = alen;
		datalen[3] = alen;
	}
	
	memset(buf, 0, size);
	size_t len = read(fd, buf, size);
	if (test94_check(buf, len, seq_start, 1, caplen, datalen) != seq_start + 4) e(0);
}

static void test94e_test_one_byte_capture(int fd, int fd2, uint8_t *buf, size_t size) {
	struct bpf_program bf;
	struct bpf_hdr bh;
	size_t plen = sizeof(struct ip) + sizeof(struct udphdr) + sizeof(uint32_t);
	size_t off = 0;
	int i;
	
	test94_filter[__arraycount(test94_filter) - 1].k = 1;
	test94e_setup_filter(&bf, test94_filter, __arraycount(test94_filter));
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);
	
	for (i = 9; i <= 11; i++) {
		test94_add_random(fd2, buf, size, i);
	}
	
	memset(buf, 0, size);
	size_t len = read(fd, buf, size);
	if (len <= 0) e(0);
	
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
}

static void test94e_test_zero_capture(int fd, int fd2, uint8_t *buf, size_t size) {
	struct bpf_program bf;
	struct bpf_stat bs;
	int i;
	
	test94_filter[__arraycount(test94_filter) - 1].k = 0;
	test94e_setup_filter(&bf, test94_filter, __arraycount(test94_filter));
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);
	
	for (i = 12; i <= 14; i++) {
		test94_add_random(fd2, buf, size, i);
	}
	
	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_recv < 3) e(0);
	if (bs.bs_capt != 0) e(0);
	if (bs.bs_drop != 0) e(0);
}

static void test94e(void) {
	struct bpf_program bf;
	uint8_t *buf;
	size_t size, plen, alen;
	uint32_t caplen[4], datalen[4];
	int fd, fd2, fd3, val;
	
	subtest = 5;
	
	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 0);
	
	val = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &val) != 0) e(0);
	
	test94e_setup_filter(&bf, NULL, BPF_MAXINSNS + 1);
	test94e_validate_filter(&bf, fd);
	
	test94e_setup_filter(&bf, test94_filter, __arraycount(test94_filter) - 1);
	test94e_validate_filter(&bf, fd);
	
	test94_comm(fd, fd2, fd3, 0);
	
	bf.bf_len++;
	if (ioctl(fd, BIOCSETF, &bf) != 0) e(0);
	test94_comm(fd, fd2, fd3, 1);
	
	test94e_clear_filter(fd);
	test94_comm(fd, fd2, fd3, 0);
	
	test94e_clear_filter(fd);
	test94_comm(fd, fd2, fd3, 0);
	
	plen = sizeof(struct ip) + sizeof(struct udphdr) + sizeof(uint32_t);
	if (BPF_WORDALIGN(plen) != plen) e(0);
	alen = BPF_WORDALIGN(plen + 1);
	if (alen - 2 <= plen + 1) e(0);
	
	test94e_test_capture_size(fd, fd2, buf, size, alen, 1, caplen, datalen);
	test94e_test_capture_size(fd, fd2, buf, size, alen + 1, 5, caplen, datalen);
	test94e_test_one_byte_capture(fd, fd2, buf, size);
	test94e_test_zero_capture(fd, fd2, buf, size);
	
	test94_filter[__arraycount(test94_filter) - 1].k = (uint32_t)-1;
	test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Compute an IP checksum.
 */
static uint16_t extract_word(uint8_t **buf, size_t *len)
{
    uint16_t word;
    
    if (*len > 1) {
        word = (*buf)[0] << 8 | (*buf)[1];
        *buf += 2;
        *len -= 2;
    } else {
        word = (*buf)[0] << 8;
        (*len)--;
    }
    
    return word;
}

static uint32_t fold_sum(uint32_t sum)
{
    while (sum > UINT16_MAX) {
        sum = (sum & UINT16_MAX) + (sum >> 16);
    }
    return sum;
}

static uint16_t test94_cksum(uint8_t *buf, size_t len)
{
    uint32_t sum = 0;
    
    while (len > 0) {
        sum += extract_word(&buf, &len);
    }
    
    sum = fold_sum(sum);
    
    return ~(uint16_t)sum;
}

/*
 * Set up UDP headers for a packet.  The packet uses IPv4 unless 'v6' is set,
 * in which case IPv6 is used.  The given buffer must be large enough to
 * contain the headers and the (to be appended) data.  The function returns the
 * offset into the buffer to the data portion of the packet.
 */
static void init_ipv4_header(struct ip *ip, size_t payload_len)
{
    memset(ip, 0, sizeof(*ip));
    ip->ip_v = IPVERSION;
    ip->ip_hl = sizeof(*ip) >> 2;
    ip->ip_len = htons(sizeof(*ip) + sizeof(struct udphdr) + payload_len);
    ip->ip_ttl = 255;
    ip->ip_p = IPPROTO_UDP;
    ip->ip_sum = 0;
    ip->ip_src.s_addr = htonl(INADDR_LOOPBACK);
    ip->ip_dst.s_addr = htonl(INADDR_LOOPBACK);
}

static void init_ipv6_header(struct ip6_hdr *ip6, size_t payload_len)
{
    memset(ip6, 0, sizeof(*ip6));
    ip6->ip6_vfc = IPV6_VERSION;
    ip6->ip6_plen = htons(sizeof(struct udphdr) + payload_len);
    ip6->ip6_nxt = IPPROTO_UDP;
    ip6->ip6_hlim = 255;
    memcpy(&ip6->ip6_src, &in6addr_loopback, sizeof(ip6->ip6_src));
    memcpy(&ip6->ip6_dst, &in6addr_loopback, sizeof(ip6->ip6_dst));
}

static void init_udp_header(struct udphdr *uh, size_t data_len)
{
    memset(uh, 0, sizeof(*uh));
    uh->uh_sport = htons(TEST_PORT_A);
    uh->uh_dport = htons(TEST_PORT_B);
    uh->uh_ulen = htons(sizeof(*uh) + data_len);
    uh->uh_sum = 0;
}

static size_t write_ipv4_packet(uint8_t *buf, size_t len)
{
    struct ip ip;
    
    init_ipv4_header(&ip, len);
    memcpy(buf, &ip, sizeof(ip));
    
    ip.ip_sum = htons(test94_cksum(buf, sizeof(ip)));
    memcpy(buf, &ip, sizeof(ip));
    
    if (test94_cksum(buf, sizeof(ip)) != 0) 
        e(0);
    
    return sizeof(ip);
}

static size_t write_ipv6_packet(uint8_t *buf, size_t len)
{
    struct ip6_hdr ip6;
    
    init_ipv6_header(&ip6, len);
    memcpy(buf, &ip6, sizeof(ip6));
    
    return sizeof(ip6);
}

static size_t
test94_make_pkt(uint8_t *buf, size_t len, int v6)
{
    struct udphdr uh;
    size_t off;
    
    if (!v6) {
        off = write_ipv4_packet(buf, len);
    } else {
        off = write_ipv6_packet(buf, len);
    }
    
    init_udp_header(&uh, len);
    memcpy(buf + off, &uh, sizeof(uh));
    
    return off + sizeof(uh);
}

/*
 * Test sending packets by writing to a BPF device.
 */
static void check_select_writable(int fd) {
    fd_set fds;
    FD_ZERO(&fds);
    FD_SET(fd, &fds);
    if (select(fd + 1, NULL, &fds, NULL, NULL) != 1) e(0);
    if (!FD_ISSET(fd, &fds)) e(0);
}

static unsigned int get_loopback_mtu(int fd2) {
    struct ifreq ifr;
    memset(&ifr, 0, sizeof(ifr));
    strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
    if (ioctl(fd2, SIOCGIFMTU, &ifr) != 0) e(0);
    return ifr.ifr_mtu;
}

static void test_oversized_packets(int fd, uint8_t *buf, unsigned int mtu) {
    unsigned int i;
    memset(buf, 0, UINT16_MAX + 1);
    for (i = UINT16_MAX + 1; i > mtu; i--) {
        if (write(fd, buf, i) != -1) e(0);
        if (errno != EMSGSIZE) e(0);
    }
    if (write(fd, buf, mtu) != mtu) e(0);
}

static void test_zero_write(int fd, uint8_t *buf) {
    if (write(fd, buf, 0) != 0) e(0);
}

static void send_hello_packet(int fd, uint8_t *buf) {
    size_t off = test94_make_pkt(buf, 6, 0);
    memcpy(buf + off, "Hello!", 6);
    if (write(fd, buf, off + 6) != off + 6) e(0);
}

static void receive_hello_packet(int fd3, uint8_t *buf, unsigned int mtu) {
    memset(buf, 0, mtu);
    if (read(fd3, buf, mtu) != 6) e(0);
    if (memcmp(buf, "Hello!", 6) != 0) e(0);
}

static void enable_feedback_mode(int fd) {
    unsigned int uval = 1;
    if (ioctl(fd, BIOCSFEEDBACK, &uval) != 0) e(0);
}

static void prepare_test_data(uint8_t *buf, size_t data_size) {
    unsigned int i;
    size_t off = test94_make_pkt(buf, data_size, 0);
    #define PRIME_MODULO 251
    for (i = 0; i < data_size; i++)
        buf[off + i] = 1 + (i % PRIME_MODULO);
}

static void verify_test_data(uint8_t *buf, size_t data_size) {
    unsigned int i;
    for (i = 0; i < data_size; i++)
        if (buf[i] != 1 + (i % PRIME_MODULO)) e(0);
}

static void receive_and_verify_packet(int fd3, uint8_t *buf, size_t expected_size) {
    memset(buf, 0, UINT16_MAX);
    if (recv(fd3, buf, UINT16_MAX, 0) != expected_size) e(0);
    verify_test_data(buf, expected_size);
}

static void receive_and_verify_packet_nonblocking(int fd3, uint8_t *buf, size_t expected_size) {
    memset(buf, 0, UINT16_MAX);
    if (recv(fd3, buf, UINT16_MAX, MSG_DONTWAIT) != expected_size) e(0);
    verify_test_data(buf, expected_size);
}

static void test_feedback_mode(int fd, int fd3, uint8_t *buf) {
    #define TEST_DATA_SIZE 12345
    size_t off;
    
    enable_feedback_mode(fd);
    prepare_test_data(buf, TEST_DATA_SIZE);
    
    off = test94_make_pkt(buf, TEST_DATA_SIZE, 0);
    if (write(fd, buf, off + TEST_DATA_SIZE) != off + TEST_DATA_SIZE) e(0);
    
    receive_and_verify_packet(fd3, buf, TEST_DATA_SIZE);
    receive_and_verify_packet_nonblocking(fd3, buf, TEST_DATA_SIZE);
    
    if (recv(fd3, buf, UINT16_MAX, MSG_DONTWAIT) != -1) e(0);
    if (errno != EWOULDBLOCK) e(0);
}

static void verify_capture_stats(int fd) {
    struct bpf_stat bs;
    if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
    if (bs.bs_capt != 2) e(0);
}

static void
test94f(void)
{
    uint8_t *buf;
    unsigned int mtu;
    int fd, fd2, fd3;

    subtest = 6;

    (void)test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);

    check_select_writable(fd);
    mtu = get_loopback_mtu(fd2);
    
    if ((buf = realloc(buf, UINT16_MAX + 1)) == NULL) e(0);
    
    test_oversized_packets(fd, buf, mtu);
    test_zero_write(fd, buf);
    send_hello_packet(fd, buf);
    receive_hello_packet(fd3, buf, mtu);
    test_feedback_mode(fd, fd3, buf);
    verify_capture_stats(fd);
    check_select_writable(fd);

    test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test read, write, and select operations on unconfigured devices.
 */
static void check_bpf_buffer_size(int fd, unsigned int *size)
{
	if (ioctl(fd, BIOCGBLEN, size) != 0) e(0);
	if (*size < 1024 || *size > BPF_MAXBUFSIZE) e(0);
}

static void verify_read_write_errors(int fd, uint8_t *buf, unsigned int size)
{
	if (read(fd, buf, size) != -1) e(0);
	if (errno != EINVAL) e(0);

	if (write(fd, buf, size) != -1) e(0);
	if (errno != EINVAL) e(0);
}

static void verify_select_readiness(int fd)
{
	fd_set rfds, wfds;

	FD_ZERO(&rfds);
	FD_SET(fd, &rfds);
	FD_ZERO(&wfds);
	FD_SET(fd, &wfds);

	if (select(fd + 1, &rfds, &wfds, NULL, NULL) != 2) e(0);

	if (!FD_ISSET(fd, &rfds)) e(0);
	if (!FD_ISSET(fd, &wfds)) e(0);
}

static void test94g(void)
{
	uint8_t *buf;
	unsigned int size;
	int fd;

	subtest = 7;

	if ((fd = open(_PATH_BPF, O_RDWR)) < 0) e(0);

	check_bpf_buffer_size(fd, &size);

	if ((buf = malloc(size)) == NULL) e(0);

	verify_read_write_errors(fd, buf, size);
	verify_select_readiness(fd);

	free(buf);

	if (close(fd) != 0) e(0);
}

/*
 * Test various IOCTL calls.  Several of these tests are rather superficial,
 * because we would need a real interface, rather than the loopback device, to
 * test their functionality properly.  Also note that we skip various checks
 * performed as part of the earlier subtests.
 */
static void test_biocsblen(int ufd) {
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
}

static void test_biocflush_stats(int cfd, int fd2, uint8_t *buf, size_t size) {
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
}

static void test_biocsetif(int ufd, int cfd) {
    struct ifreq ifr;
    
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

static void test_biocimmediate(int cfd, int fd2, uint8_t *buf, size_t size) {
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
}

static void verify_toggle_ioctl(int fd, int get_cmd, int set_cmd, int default_val) {
    unsigned int uval;
    
    uval = 1 - default_val;
    if (ioctl(fd, get_cmd, &uval) != 0) e(0);
    if (uval != default_val) e(0);
    
    uval = 2;
    if (ioctl(fd, set_cmd, &uval) != 0) e(0);
    
    if (ioctl(fd, get_cmd, &uval) != 0) e(0);
    if (uval != 1) e(0);
    
    uval = 0;
    if (ioctl(fd, set_cmd, &uval) != 0) e(0);
    
    uval = 1;
    if (ioctl(fd, get_cmd, &uval) != 0) e(0);
    if (uval != 0) e(0);
}

static void test_biocgdltlist(int cfd) {
    struct bpf_dltlist bfl;
    unsigned int list[2];
    
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
    memset(list, 0, sizeof(list));
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
    memset(list, 0, sizeof(list));
    bfl.bfl_len = 2;
    bfl.bfl_list = list;
    if (ioctl(cfd, BIOCGDLTLIST, &bfl) != 0) e(0);
    if (bfl.bfl_len != 1) e(0);
    if (bfl.bfl_list != list) e(0);
    if (list[0] != DLT_RAW) e(0);
    if (list[1] != 0) e(0);
}

static void test_biocsseesent(int cfd, int fd2, uint8_t *buf, size_t size) {
    struct bpf_stat bs;
    unsigned int uval;
    
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

static void test_biocsrtimeout(int ufd) {
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

static void
test94h(void)
{
    struct bpf_stat bs;
    struct bpf_version bv;
    struct ifreq ifr;
    uint8_t *buf;
    size_t size;
    unsigned int uval;
    int cfd, ufd, fd2, fd3;

    subtest = 8;

    size = test94_setup(&cfd, &fd2, &fd3, &buf, 0, 1);

    if ((ufd = open(_PATH_BPF, O_RDWR)) < 0) e(0);

    test_biocsblen(ufd);

    if (ioctl(cfd, BIOCSBLEN, &uval) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (ioctl(cfd, BIOCGBLEN, &uval) != 0) e(0);
    if (uval != size) e(0);

    test_biocflush_stats(cfd, fd2, buf, size);

    if (ioctl(ufd, BIOCFLUSH) != 0) e(0);

    if (ioctl(ufd, BIOCGSTATS, &bs) != 0) e(0);
    if (bs.bs_recv != 0) e(0);
    if (bs.bs_drop != 0) e(0);
    if (bs.bs_capt != 0) e(0);

    if (ioctl(ufd, BIOCPROMISC) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (ioctl(cfd, BIOCPROMISC) != 0) e(0);

    if (ioctl(ufd, BIOCGDLT, &uval) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (ioctl(ufd, BIOCGETIF, &ifr) != -1) e(0);
    if (errno != EINVAL) e(0);

    memset(&ifr, 'X', sizeof(ifr));
    if (ioctl(cfd, BIOCGETIF, &ifr) != 0) e(0);
    if (strcmp(ifr.ifr_name, LOOPBACK_IFNAME) != 0) e(0);

    test_biocsetif(ufd, cfd);

    test_biocimmediate(cfd, fd2, buf, size);

    uval = 1;
    if (ioctl(ufd, BIOCIMMEDIATE, &uval) != 0) e(0);

    uval = 0;
    if (ioctl(ufd, BIOCIMMEDIATE, &uval) != 0) e(0);

    if (ioctl(ufd, BIOCVERSION, &bv) != 0) e(0);
    if (bv.bv_major != BPF_MAJOR_VERSION) e(0);
    if (bv.bv_minor != BPF_MINOR_VERSION) e(0);

    verify_toggle_ioctl(ufd, BIOCGHDRCMPLT, BIOCSHDRCMPLT, 0);

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

    if (ioctl(ufd, BIOCGDLTLIST, &bfl) != -1) e(0);
    if (errno != EINVAL) e(0);

    test_biocgdltlist(cfd);

    verify_toggle_ioctl(ufd, BIOCGSEESENT, BIOCSSEESENT, 1);

    test_biocsseesent(cfd, fd2, buf, size);

    test_biocsrtimeout(ufd);

    verify_toggle_ioctl(ufd, BIOCGFEEDBACK, BIOCSFEEDBACK, 0);

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
static void setup_bpf_device(int *fd, uint8_t **buf, size_t *size) {
    struct bpf_program bf;
    struct ifreq ifr;
    unsigned int uval, dlt;
    
    if ((*fd = open(_PATH_BPF, O_RDWR)) < 0) e(0);
    
    if (ioctl(*fd, BIOCGBLEN, size) != 0) e(0);
    if (*size < 1024 || *size > BPF_MAXBUFSIZE) e(0);
    
    if ((*buf = malloc(*size)) == NULL) e(0);
    
    memset(&bf, 0, sizeof(bf));
    bf.bf_len = __arraycount(test94_filter6);
    bf.bf_insns = test94_filter6;
    if (ioctl(*fd, BIOCSETF, &bf) != 0) e(0);
    
    uval = 1;
    if (ioctl(*fd, BIOCIMMEDIATE, &uval) != 0) e(0);
    
    memset(&ifr, 0, sizeof(ifr));
    strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
    if (ioctl(*fd, BIOCSETIF, &ifr) != 0) e(0);
    
    if (ioctl(*fd, BIOCGDLT, &dlt) != 0) e(0);
    if (dlt != DLT_RAW) e(0);
}

static void setup_socket(int *fd, struct sockaddr_in6 *sin6, uint16_t port) {
    if ((*fd = socket(AF_INET6, SOCK_DGRAM, 0)) < 0) e(0);
    
    memset(sin6, 0, sizeof(*sin6));
    sin6->sin6_family = AF_INET6;
    sin6->sin6_port = htons(port);
    memcpy(&sin6->sin6_addr, &in6addr_loopback, sizeof(sin6->sin6_addr));
}

static void bind_and_connect_sockets(int fd2, int fd3, 
                                    struct sockaddr_in6 *sin6A, 
                                    struct sockaddr_in6 *sin6B) {
    if (bind(fd2, (struct sockaddr *)sin6A, sizeof(*sin6A)) != 0) e(0);
    if (connect(fd2, (struct sockaddr *)sin6B, sizeof(*sin6B)) != 0) e(0);
    if (bind(fd3, (struct sockaddr *)sin6B, sizeof(*sin6B)) != 0) e(0);
    if (connect(fd3, (struct sockaddr *)sin6A, sizeof(*sin6A)) != 0) e(0);
}

static void exchange_packets(int fd2, int fd3) {
    uint8_t c;
    
    if (write(fd2, "A", 1) != 1) e(0);
    if (read(fd3, &c, 1) != 1) e(0);
    if (c != 'A') e(0);
    
    if (write(fd3, "B", 1) != 1) e(0);
    if (read(fd2, &c, 1) != 1) e(0);
    if (c != 'B') e(0);
}

static void verify_bpf_stats(int fd) {
    struct bpf_stat bs;
    
    if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
    if (bs.bs_recv < 2) e(0);
    if (bs.bs_capt != 1) e(0);
    if (bs.bs_drop != 0) e(0);
}

static void verify_captured_packet(uint8_t *buf, size_t size, ssize_t len) {
    struct bpf_hdr bh;
    struct ip6_hdr ip6;
    struct udphdr uh;
    size_t expected_len;
    
    expected_len = BPF_WORDALIGN(sizeof(bh)) + 
                  BPF_WORDALIGN(sizeof(ip6) + sizeof(uh) + 1);
    if (len != expected_len) e(0);
    
    memcpy(&bh, buf, sizeof(bh));
    
    if (bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) e(0);
    if (bh.bh_caplen != sizeof(ip6) + sizeof(uh) + 1) e(0);
    if (bh.bh_datalen != bh.bh_caplen) e(0);
    if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh))) e(0);
    
    if (buf[bh.bh_hdrlen + sizeof(ip6) + sizeof(uh)] != 'A') e(0);
}

static void test_ipv6_packet_write(int fd, int fd3, uint8_t *buf, size_t size) {
    struct sockaddr_in6 sin6A;
    socklen_t socklen;
    size_t off;
    
    off = test94_make_pkt(buf, 6, 1);
    memcpy(buf + off, "Hello!", 6);
    
    if (write(fd, buf, off + 6) != off + 6) e(0);
    
    socklen = sizeof(sin6A);
    if (recvfrom(fd3, buf, size, 0, (struct sockaddr *)&sin6A,
        &socklen) != 6) e(0);
    
    if (memcmp(buf, "Hello!", 6) != 0) e(0);
    if (socklen != sizeof(sin6A)) e(0);
    if (sin6A.sin6_family != AF_INET6) e(0);
    if (sin6A.sin6_port != htons(TEST_PORT_A)) e(0);
    if (memcmp(&sin6A.sin6_addr, &in6addr_loopback,
        sizeof(sin6A.sin6_addr)) != 0) e(0);
}

static void test94i(void) {
    struct sockaddr_in6 sin6A, sin6B;
    uint8_t *buf;
    size_t size;
    ssize_t len;
    int fd, fd2, fd3;
    
    subtest = 9;
    
    setup_bpf_device(&fd, &buf, &size);
    
    setup_socket(&fd2, &sin6A, TEST_PORT_A);
    memcpy(&sin6B, &sin6A, sizeof(sin6B));
    sin6B.sin6_port = htons(TEST_PORT_B);
    
    setup_socket(&fd3, &sin6B, TEST_PORT_B);
    
    bind_and_connect_sockets(fd2, fd3, &sin6A, &sin6B);
    
    exchange_packets(fd2, fd3);
    
    verify_bpf_stats(fd);
    
    memset(buf, 0, size);
    len = read(fd, buf, size);
    
    verify_captured_packet(buf, size, len);
    
    test_ipv6_packet_write(fd, fd3, buf, size);
    
    free(buf);
    
    if (close(fd3) != 0) e(0);
    if (close(fd2) != 0) e(0);
    if (close(fd) != 0) e(0);
}

/*
 * Test the BPF sysctl(7) interface at a basic level.
 */
static void get_sysctl_mib(const char *name, int *mib, size_t *len, int expected_len)
{
	memset(mib, 0, *len * sizeof(int));
	if (sysctlnametomib(name, mib, len) != 0) e(0);
	if (*len != expected_len) e(0);
}

static void get_sysctl_value(int *mib, size_t len, void *data, size_t data_size)
{
	size_t oldlen = data_size;
	if (sysctl(mib, len, data, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen != data_size) e(0);
}

static void validate_maxbufsize(int *mib, size_t len)
{
	int val;
	get_sysctl_value(mib, len, &val, sizeof(val));
	if (val < 1024 || val > INT_MAX / 2) e(0);
	
	if (sysctl(mib, len, NULL, NULL, &val, sizeof(val)) != -1) e(0);
	if (errno != EPERM) e(0);
}

static void check_bpf_entry_configured(struct bpf_d_ext *bde, size_t size, unsigned int count)
{
	if (bde->bde_bufsize != size) e(0);
	if (bde->bde_promisc != 0) e(0);
	if (bde->bde_state != BPF_IDLE) e(0);
	if (bde->bde_immediate != 0) e(0);
	if (bde->bde_hdrcmplt != 0) e(0);
	if (bde->bde_seesent != 1) e(0);
	if (bde->bde_rcount < count * 3 + 1) e(0);
	if (bde->bde_dcount != count) e(0);
	if (bde->bde_ccount != count * 3) e(0);
	if (strcmp(bde->bde_ifname, LOOPBACK_IFNAME) != 0) e(0);
}

static void check_bpf_entry_unconfigured(struct bpf_d_ext *bde, size_t size)
{
	if (bde->bde_bufsize != size) e(0);
	if (bde->bde_promisc != 0) e(0);
	if (bde->bde_state != BPF_IDLE) e(0);
	if (bde->bde_immediate != 1) e(0);
	if (bde->bde_hdrcmplt != 1) e(0);
	if (bde->bde_seesent != 0) e(0);
	if (bde->bde_rcount != 0) e(0);
	if (bde->bde_dcount != 0) e(0);
	if (bde->bde_ccount != 0) e(0);
	if (bde->bde_ifname[0] != '\0') e(0);
}

static int find_bpf_entries(int *mib, size_t len, struct bpf_d_ext *bde, size_t bdesize, 
                            void (*check_func)(struct bpf_d_ext *, size_t, unsigned int),
                            size_t size, unsigned int count)
{
	size_t oldlen = bdesize;
	unsigned int slot;
	int found = 0;
	
	if (sysctl(mib, len, bde, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen % sizeof(*bde)) e(0);
	
	for (slot = 0; slot < oldlen / sizeof(*bde); slot++) {
		if (bde[slot].bde_pid != getpid())
			continue;
		
		if (check_func == check_bpf_entry_configured)
			check_func(&bde[slot], size, count);
		else
			check_bpf_entry_unconfigured(&bde[slot], size);
		
		found++;
	}
	
	return found;
}

static void generate_test_traffic(int fd2, int fd3, uint8_t *buf, size_t size, unsigned int *count)
{
	*count = test94_fill_exact(fd2, buf, size, 0);
	test94_fill_exact(fd2, buf, size, 0);
	test94_fill_exact(fd2, buf, size, 0);
	
	if (write(fd3, "X", 1) != 1) e(0);
}

static void toggle_bpf_flags(int fd)
{
	unsigned int uval = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &uval) != 0) e(0);
	if (ioctl(fd, BIOCSHDRCMPLT, &uval) != 0) e(0);
	
	uval = 0;
	if (ioctl(fd, BIOCSSEESENT, &uval) != 0) e(0);
}

static void verify_stats_change(int *smib, struct bpf_stat *bs1, unsigned int count)
{
	struct bpf_stat bs2;
	get_sysctl_value(smib, 3, &bs2, sizeof(bs2));
	
	if (bs2.bs_recv < bs1->bs_recv + count * 3 + 1) e(0);
	if (bs2.bs_drop != bs1->bs_drop + count) e(0);
	if (bs2.bs_capt != bs1->bs_capt + count * 3) e(0);
}

static void verify_no_entries_for_pid(int *mib, size_t len, struct bpf_d_ext *bde, size_t bdesize)
{
	size_t oldlen = bdesize;
	unsigned int slot;
	
	if (sysctl(mib, len, bde, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen % sizeof(*bde)) e(0);
	
	for (slot = 0; slot < oldlen / sizeof(*bde); slot++)
		if (bde[slot].bde_pid == getpid()) e(0);
}

static void test94j(void)
{
	struct bpf_stat bs1;
	struct bpf_d_ext *bde;
	uint8_t *buf;
	unsigned int count;
	size_t len, bdesize, size;
	int fd, fd2, fd3, mib[5], smib[3], found;

	subtest = 10;

	len = __arraycount(mib);
	get_sysctl_mib("net.bpf.maxbufsize", mib, &len, 3);
	validate_maxbufsize(mib, len);

	len = __arraycount(smib);
	get_sysctl_mib("net.bpf.stats", smib, &len, 3);
	get_sysctl_value(smib, len, &bs1, sizeof(bs1));

	len = __arraycount(mib);
	get_sysctl_mib("net.bpf.peers", mib, &len, 3);
	mib[len++] = sizeof(*bde);
	mib[len++] = INT_MAX;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);
	generate_test_traffic(fd2, fd3, buf, size, &count);

	size_t oldlen;
	if (sysctl(mib, len, NULL, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen == 0) e(0);

	bdesize = oldlen + sizeof(*bde) * 8;
	if ((bde = malloc(bdesize)) == NULL) e(0);

	found = find_bpf_entries(mib, len, bde, bdesize, check_bpf_entry_configured, size, count);
	if (found != 1) e(0);

	if (ioctl(fd, BIOCFLUSH) != 0) e(0);
	test94_cleanup(fd, fd2, fd3, buf);

	verify_stats_change(smib, &bs1, count);

	if ((fd = open(_PATH_BPF, O_RDWR)) < 0) e(0);
	toggle_bpf_flags(fd);

	found = find_bpf_entries(mib, len, bde, bdesize, check_bpf_entry_unconfigured, size, 0);
	if (found != 1) e(0);

	close(fd);

	verify_no_entries_for_pid(mib, len, bde, bdesize);
	free(bde);
}

/*
 * Test privileged operations as an unprivileged caller.
 */
static void test_open_bpf_as_nonroot(void)
{
    if (open(_PATH_BPF, O_RDWR) != -1) e(0);
    if (errno != EACCES) e(0);
}

static void test_sysctl_bpf_peers_as_nonroot(void)
{
    int mib[5];
    size_t len, oldlen;
    
    memset(mib, 0, sizeof(mib));
    len = __arraycount(mib);
    if (sysctlnametomib("net.bpf.peers", mib, &len) != 0) e(0);
    if (len != 3) e(0);
    mib[len++] = sizeof(struct bpf_d_ext);
    mib[len++] = INT_MAX;
    
    if (sysctl(mib, len, NULL, &oldlen, NULL, 0) != -1) e(0);
    if (errno != EPERM) e(0);
}

static void switch_to_nonroot_user(void)
{
    struct passwd *pw;
    
    if ((pw = getpwnam(NONROOT_USER)) == NULL) e(0);
    if (setuid(pw->pw_uid) != 0) e(0);
}

static void run_nonroot_tests(void)
{
    errct = 0;
    
    switch_to_nonroot_user();
    test_open_bpf_as_nonroot();
    test_sysctl_bpf_peers_as_nonroot();
    
    exit(errct);
}

static void test94k(void)
{
    pid_t pid;
    int status;
    
    subtest = 11;
    
    pid = fork();
    if (pid == 0) {
        run_nonroot_tests();
    } else if (pid == -1) {
        e(0);
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
static int find_ethernet_interface(struct ifreq *ifr, uint8_t *ether_dest)
{
	struct ifaddrs *ifa, *ifp;
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
			strlcpy(ifr->ifr_name, ifp->ifa_name,
			    sizeof(ifr->ifr_name));

			memcpy(&sdl, (struct sockaddr_dl *)ifp->ifa_addr,
			    offsetof(struct sockaddr_dl, sdl_data));
			if (sdl.sdl_alen != ETHER_ADDR_LEN) e(0);
			memcpy(ether_dest,
			    ((struct sockaddr_dl *)ifp->ifa_addr)->sdl_data +
			    sdl.sdl_nlen, sdl.sdl_alen);
			freeifaddrs(ifa);
			return 1;
		}
	}

	freeifaddrs(ifa);
	return 0;
}

static int setup_bpf_device(struct ifreq *ifr)
{
	unsigned int val;
	int bfd;

	if ((bfd = open(_PATH_BPF, O_RDWR)) < 0) e(0);
	if (ioctl(bfd, BIOCSETIF, ifr) != 0) e(0);
	if (ioctl(bfd, BIOCGDLT, &val) != 0) e(0);
	if (val != DLT_EN10MB) e(0);
	val = 1;
	if (ioctl(bfd, BIOCSFEEDBACK, &val) != 0) e(0);
	return bfd;
}

static void prepare_ether_header(struct ether_header *ether, const uint8_t *dest,
    const uint8_t *src, uint16_t type)
{
	memcpy(ether->ether_dhost, dest, ETHER_ADDR_LEN);
	memcpy(ether->ether_shost, src, ETHER_ADDR_LEN);
	ether->ether_type = htons(type);
}

static size_t build_packet(uint8_t *buf, struct ether_header *ether, int is_ipv6)
{
	size_t off;

	memcpy(buf, ether, sizeof(*ether));
	off = sizeof(*ether);
	off += test94_make_pkt(buf + off, 6, is_ipv6);
	memcpy(buf + off, "Hello!", 6);
	return off + 6;
}

static void verify_packet_not_received(int sfd, uint8_t *buf, size_t bufsize)
{
	if (recv(sfd, buf, bufsize, MSG_DONTWAIT) != -1) e(0);
	if (errno != EWOULDBLOCK) e(0);
}

static int create_udp_socket_v4(void)
{
	struct sockaddr_in sin;
	int sfd;

	if ((sfd = socket(AF_INET, SOCK_DGRAM, 0)) < 0) e(0);
	memset(&sin, 0, sizeof(sin));
	sin.sin_family = AF_INET;
	sin.sin_port = htons(TEST_PORT_B);
	sin.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	if (bind(sfd, (struct sockaddr *)&sin, sizeof(sin)) != 0) e(0);
	return sfd;
}

static int create_udp_socket_v6(void)
{
	struct sockaddr_in6 sin6;
	int sfd;

	if ((sfd = socket(AF_INET6, SOCK_DGRAM, 0)) < 0) e(0);
	memset(&sin6, 0, sizeof(sin6));
	sin6.sin6_family = AF_INET6;
	sin6.sin6_port = htons(TEST_PORT_B);
	memcpy(&sin6.sin6_addr, &in6addr_loopback, sizeof(sin6.sin6_addr));
	if (bind(sfd, (struct sockaddr *)&sin6, sizeof(sin6)) != 0) e(0);
	return sfd;
}

static void test_packet_injection(int bfd, struct ether_header *ether, int is_ipv6)
{
	uint8_t buf[sizeof(struct ether_header) + MAX(sizeof(struct ip),
	    sizeof(struct ip6_hdr)) + sizeof(struct udphdr) + 6];
	size_t pkt_size;
	int sfd;

	if (is_ipv6) {
		sfd = create_udp_socket_v6();
		ether->ether_type = htons(ETHERTYPE_IPV6);
	} else {
		sfd = create_udp_socket_v4();
		ether->ether_type = htons(ETHERTYPE_IP);
	}

	pkt_size = build_packet(buf, ether, is_ipv6);
	if (write(bfd, buf, pkt_size) != pkt_size) e(0);
	verify_packet_not_received(sfd, buf, sizeof(buf));
	if (close(sfd) != 0) e(0);
}

static void
test94l(void)
{
	const uint8_t ether_src[ETHER_ADDR_LEN] =
	    { 0x02, 0x00, 0x01, 0x12, 0x34, 0x56 };
	struct ether_header ether;
	struct ifreq ifr;
	uint8_t ether_dest[ETHER_ADDR_LEN];
	int bfd;

	subtest = 12;

	if (!get_setting_use_network())
		return;

	memset(&ifr, 0, sizeof(ifr));
	memset(&ether, 0, sizeof(ether));

	if (!find_ethernet_interface(&ifr, ether_dest))
		return;

	bfd = setup_bpf_device(&ifr);
	prepare_ether_header(&ether, ether_dest, ether_src, ETHERTYPE_IP);
	
	test_packet_injection(bfd, &ether, 0);
	test_packet_injection(bfd, &ether, 1);
	
	if (close(bfd) != 0) e(0);
}

/*
 * Test program for LWIP BPF.
 */
#define DEFAULT_TEST_MASK 0xFFF
#define TEST_94_NUMBER 94

typedef void (*test_function)(void);

static const struct {
    unsigned int mask;
    test_function func;
} test_cases[] = {
    {0x001, test94a},
    {0x002, test94b},
    {0x004, test94c},
    {0x008, test94d},
    {0x010, test94e},
    {0x020, test94f},
    {0x040, test94g},
    {0x080, test94h},
    {0x100, test94i},
    {0x200, test94j},
    {0x400, test94k},
    {0x800, test94l}
};

#define NUM_TEST_CASES (sizeof(test_cases) / sizeof(test_cases[0]))

static int get_test_mask(int argc, char **argv)
{
    if (argc == 2) {
        return atoi(argv[1]);
    }
    return DEFAULT_TEST_MASK;
}

static void run_selected_tests(int test_mask)
{
    int i;
    for (i = 0; i < NUM_TEST_CASES; i++) {
        if (test_mask & test_cases[i].mask) {
            test_cases[i].func();
        }
    }
}

static void run_all_iterations(int test_mask)
{
    int i;
    for (i = 0; i < ITERATIONS; i++) {
        run_selected_tests(test_mask);
    }
}

int main(int argc, char **argv)
{
    int test_mask;
    
    start(TEST_94_NUMBER);
    srand48(time(NULL));
    
    test_mask = get_test_mask(argc, argv);
    run_all_iterations(test_mask);
    
    quit();
}
