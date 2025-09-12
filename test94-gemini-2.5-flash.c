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
        /*
         * Original code called e(0). Assuming e(0) implies program termination
         * (e.g., similar to exit(0) or exit(1)).
         * In a signal handler, functions like exit() are not async-signal-safe
         * and can lead to deadlocks or corrupted state.
         *
         * _exit() is the async-signal-safe way to terminate a process.
         * It immediately terminates the calling process without calling atexit handlers
         * or flushing stream buffers, which is crucial for signal safety.
         * Using 0 as the exit status to match a common interpretation of e(0)
         * as a non-error or successful termination in test contexts.
         */
        _exit(0);
    }

    /*
     * The variable 'got_signal' should be declared as 'volatile sig_atomic_t'
     * in the global scope to ensure atomic updates and proper visibility
     * between the signal handler and other parts of the program,
     * preventing race conditions and compiler optimizations that could
     * make the update non-atomic or invisible.
     * This refactoring assumes 'got_signal' is appropriately declared elsewhere.
     */
    got_signal++;
}

/*
 * Send UDP packets on the given socket 'fd' so as to fill up a BPF store
 * buffer of size 'size' exactly.  The provided buffer 'buf' may be used for
 * packet generation and is at least of 'size' bytes.  Return the number of
 * packets sent.
 */
#include <stdlib.h> // For exit
#include <unistd.h> // For write
#include <string.h> // For memset, memcpy
#include <stdint.h> // For uint32_t, uint8_t

// Forward declarations for BPF-related structs and macro.
// These are assumed to be defined in an external header or within the project.
// Example placeholders (actual definitions would vary based on the specific BPF environment):
// #define BPF_WORDALIGN(x) (((x) + 7) & ~7) // Common 8-byte alignment
// struct bpf_hdr { char dummy[32]; };
// struct ip { char dummy[20]; };
// struct udphdr { char dummy[8]; };


static uint32_t
test94_fill_exact(int fd, uint8_t * buf, size_t buffer_capacity, uint32_t seq)
{
	// Descriptive variable names improve readability.
	size_t min_total_header_size;
	size_t effective_block_size;
	size_t aligned_payload_offset_overhead;
	size_t payload_data_size_per_block;
	ssize_t bytes_written;

	// Calculate the minimum space required for the combined header structures
	// (BPF, IP, UDP) plus the sequence number, with BPF word alignment.
	min_total_header_size = BPF_WORDALIGN(sizeof(struct bpf_hdr)) +
	                        sizeof(struct ip) +
	                        sizeof(struct udphdr) +
	                        sizeof(seq);

	// Determine the effective block size for each write operation.
	// This size must be a power of 2, at least 16, and large enough
	// to accommodate the `min_total_header_size`.
	effective_block_size = 16;
	while (effective_block_size < min_total_header_size) {
		// Defensive check against potential overflow if block size grows excessively large.
		// For typical BPF use cases, this condition is unlikely to be met.
		if (effective_block_size > SIZE_MAX / 2) {
			exit(EXIT_FAILURE);
		}
		effective_block_size <<= 1;
	}

	// Validate that the chosen `effective_block_size` does not exceed
	// the provided `buffer_capacity`. If it does, a single block cannot fit.
	if (effective_block_size > buffer_capacity) {
		exit(EXIT_FAILURE);
	}

	// Calculate the actual aligned overhead within each `effective_block_size`
	// for the header portion, specifically by re-aligning `min_total_header_size`
	// after conceptually removing `sizeof(seq)`. This pattern matches the original logic.
	aligned_payload_offset_overhead = BPF_WORDALIGN(min_total_header_size - sizeof(seq));

	// Determine the size of the actual payload data that will be written in each block.
	// This is the total block size minus the calculated header overhead.
	payload_data_size_per_block = effective_block_size - aligned_payload_offset_overhead;

	// Critical reliability and security check:
	// Ensure that the calculated `payload_data_size_per_block` is positive.
	// If it's zero or negative, subsequent buffer accesses (e.g., `buf[... - 1]`)
	// would result in out-of-bounds access (Undefined Behavior), and writing zero bytes
	// is likely not the intended functionality of a "fill_exact" function.
	if (payload_data_size_per_block <= 0) {
		exit(EXIT_FAILURE);
	}

	// Calculate the number of full blocks that can be processed given the `buffer_capacity`.
	// The original code implies that `buffer_capacity` acts as a total budget in units
	// of `effective_block_size`.
	size_t num_blocks_to_process = buffer_capacity / effective_block_size;

	// Loop to prepare and write data blocks.
	// Each iteration processes one block, updates the buffer, and increments the sequence number.
	for (size_t i = 0; i < num_blocks_to_process; ++i, ++seq) {
		// The following sequence of buffer manipulations replicates the original logic,
		// including potential overwrites, to maintain external functionality precisely.

		// 1. Fill the entire payload area of the buffer with 'Y' characters.
		memset(buf, 'Y', payload_data_size_per_block);

		// 2. If there's enough space in the payload *after* the `seq` would be copied,
		//    place an 'X' character at that specific offset. This will overwrite a 'Y'.
		if (payload_data_size_per_block > sizeof(seq)) {
			buf[sizeof(seq)] = 'X';
		}

		// 3. Place a 'Z' character at the very end of the payload data area.
		//    This will overwrite whatever character ('Y' or 'X') was previously there.
		buf[payload_data_size_per_block - 1] = 'Z';

		// 4. Copy the current sequence number to the very beginning of the buffer.
		//    This operation overwrites the initial 'Y' characters and potentially the 'X'
		//    if `sizeof(seq)` is large enough to reach its position.
		memcpy(buf, &seq, sizeof(seq));

		// Write the prepared block of data to the file descriptor.
		bytes_written = write(fd, buf, payload_data_size_per_block);

		// Robust error handling for the write operation.
		// If `write` fails (returns -1) or does not write the expected number of bytes,
		// terminate the program to match the original `e(0)` behavior.
		if (bytes_written == -1 || (size_t)bytes_written != payload_data_size_per_block) {
			exit(EXIT_FAILURE);
		}
	}

	// Return the final sequence number after all blocks have been processed.
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
	size_t hdrlen;
	uint32_t seq;
	size_t total_conceptual_processed_size;

	const char filler_byte = 'Y';
	const char marker_x_byte = 'X';
	const char marker_z_byte = 'Z';

	hdrlen = BPF_WORDALIGN(BPF_WORDALIGN(sizeof(struct bpf_hdr)) +
	    sizeof(struct ip) + sizeof(struct udphdr));

	for (total_conceptual_processed_size = 0, seq = 1;
	    total_conceptual_processed_size <= size;
	    seq++) {
		size_t max_rand_payload_part = (size / 10 > 0) ? (size / 10) : 1;
		size_t random_payload_addition = (size_t)(lrand48() % max_rand_payload_part);

		size_t current_payload_len = sizeof(seq) + random_payload_addition;
		size_t current_total_len = hdrlen + current_payload_len;

		memset(buf, filler_byte, current_payload_len);

		if (current_payload_len > sizeof(seq)) {
			buf[sizeof(seq)] = marker_x_byte;
		}

		buf[current_payload_len - 1] = marker_z_byte;
		memcpy(buf, &seq, sizeof(seq));

		ssize_t bytes_written = write(fd, buf, current_payload_len);
		if (bytes_written == -1 || (size_t)bytes_written != current_payload_len) {
			exit(EXIT_FAILURE);
		}

		total_conceptual_processed_size += BPF_WORDALIGN(current_total_len);
	}
}

/*
 * Send a UDP packet with a specific size of 'size' bytes and sequence number
 * 'seq' on socket 'fd', using 'buf' as scratch buffer.
 */
static void
test94_add_specific(int fd, uint8_t * buf, size_t size, uint32_t seq)
{
	const size_t original_payload_size = size;
	const size_t seq_size = sizeof(seq);
	const size_t total_data_size = original_payload_size + seq_size;

	memset(buf, 'Y', total_data_size);

	if (original_payload_size > 0)
	{
		buf[seq_size] = 'X';
	}

	buf[total_data_size - 1] = 'Z';
	memcpy(buf, &seq, seq_size);

	if (write(fd, buf, total_data_size) != total_data_size) e(0);
}

/*
 * Send a randomly sized, relatively small UDP packet on the given socket 'fd',
 * using sequence number 'seq'.  The buffer 'buf' may be used as scratch buffer
 * which is at most 'size' bytes--the same size as the total BPF buffer.
 */
#include <stdint.h>
#include <stdlib.h>

static void
test94_add_random(int fd, uint8_t * buf, size_t size, uint32_t seq)
{
    size_t length_to_add;
    size_t max_possible_len = size / 10;

    if (max_possible_len == 0) {
        length_to_add = 0;
    } else {
        if (max_possible_len > UINT32_MAX) {
            length_to_add = (size_t)arc4random_uniform(UINT32_MAX);
        } else {
            length_to_add = (size_t)arc4random_uniform((uint32_t)max_possible_len);
        }
    }

    test94_add_specific(fd, buf, length_to_add, seq);
}

/*
 * Check whether the packet in 'buf' of 'caplen' captured bytes out of
 * 'datalen' data bytes is one we sent.  If so, return an offset to the packet
 * data.  If not, return a negative value.
 */
#include <stddef.h>
#include <string.h>
#include <arpa/inet.h>
#include <netinet/ip.h>
#include <netinet/udp.h>

static ssize_t
test94_check_pkt(uint8_t *buf, ssize_t caplen, ssize_t datalen)
{
    struct ip ip_header;
    struct udphdr udp_header;
    const ssize_t standard_ip_header_len = (ssize_t)sizeof(struct ip);
    const ssize_t udp_header_len = (ssize_t)sizeof(struct udphdr);

    if (buf == NULL) {
        return -1;
    }

    if (caplen < standard_ip_header_len) {
        return -1;
    }

    memcpy(&ip_header, buf, standard_ip_header_len);

    if (ip_header.ip_v != IPVERSION) {
        return -1;
    }

    if (ip_header.ip_hl != (uint8_t)(standard_ip_header_len / 4)) {
        return -1;
    }

    if (ip_header.ip_p != IPPROTO_UDP) {
        return -1;
    }

    if ((caplen - standard_ip_header_len) < udp_header_len) {
        return -1;
    }

    memcpy(&udp_header, buf + standard_ip_header_len, udp_header_len);

    if (udp_header.uh_sport != htons(TEST_PORT_A)) {
        return -1;
    }

    if (udp_header.uh_dport != htons(TEST_PORT_B)) {
        return -1;
    }

    if ((datalen - standard_ip_header_len) != (ssize_t)ntohs(udp_header.uh_ulen)) {
        e(0);
    }

    return standard_ip_header_len + udp_header_len;
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
		if ((size_t)len < BPF_WORDALIGN(sizeof(bh))) {
            e(0);
        }

		memcpy(&bh, buf, sizeof(bh));

		if (bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) {
		     e(0);
        }
		if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh))) {
            e(0);
        }

        if (bh.bh_caplen == 0 || bh.bh_datalen == 0) {
            e(0);
        }
        if (bh.bh_caplen > (uint32_t)SSIZE_MAX || bh.bh_datalen > (uint32_t)SSIZE_MAX) {
            e(0);
        }

		if (caplen != NULL) {
			if (bh.bh_caplen != *caplen) {
                e(0);
            }
			if (bh.bh_datalen != *datalen) {
                e(0);
            }
			caplen++;
			datalen++;
		} else {
			if (bh.bh_datalen != bh.bh_caplen) {
                e(0);
            }
        }

        ssize_t packet_full_size = (ssize_t)bh.bh_hdrlen + (ssize_t)BPF_WORDALIGN(bh.bh_caplen);
        if (packet_full_size <= 0 || packet_full_size > len) {
            e(0);
        }

		buf += bh.bh_hdrlen;
		len -= bh.bh_hdrlen;

		off = test94_check_pkt(buf, bh.bh_caplen, bh.bh_datalen);
		if (off < 0) {
			if (filtered) {
                e(0);
            }
			buf += BPF_WORDALIGN(bh.bh_caplen);
			len -= BPF_WORDALIGN(bh.bh_caplen);
			continue;
		}

        if (off < 0 || off > (ssize_t)(bh.bh_caplen - sizeof(nseq))) {
            e(0);
        }

		memcpy(&nseq, &buf[off], sizeof(nseq));

		if (nseq != seq++) {
            e(0);
        }

		off += sizeof(nseq);

        ssize_t end_of_data_for_Z_idx = (ssize_t)(bh.bh_datalen - 1);

        if (off < (ssize_t)bh.bh_caplen) {
            if (off < end_of_data_for_Z_idx) {
                if (buf[off] != 'X') {
                    e(0);
                }
                off++;

                while (off < (ssize_t)bh.bh_caplen && off < end_of_data_for_Z_idx) {
                    if (buf[off] != 'Y') {
                        e(0);
                    }
                    off++;
                }
            }

            if (off < (ssize_t)bh.bh_caplen && off == end_of_data_for_Z_idx) {
                if (buf[off] != 'Z') {
                    e(0);
                }
            }
        }

		buf += BPF_WORDALIGN(bh.bh_caplen);
		len -= BPF_WORDALIGN(bh.bh_caplen);
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
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <sys/ioctl.h>
#include <net/if.h>
#include <net/bpf.h>

static size_t
test94_setup(int * fd, int * fd2, int * fd3, uint8_t ** buf, unsigned int size,
	int set_filter)
{
	struct sockaddr_in sinA, sinB;
	struct ifreq ifr;
	struct bpf_program bf;
	unsigned int dlt;
	size_t ret_size = 0;

	int l_fd = -1;
	int l_fd2 = -1;
	int l_fd3 = -1;
	uint8_t *l_buf = NULL;

	*fd = -1;
	*fd2 = -1;
	*fd3 = -1;
	*buf = NULL;

	if ((l_fd = open(_PATH_BPF, O_RDWR)) < 0) {
		goto cleanup;
	}

	if (size != 0) {
		if (ioctl(l_fd, BIOCSBLEN, &size) != 0) {
			goto cleanup;
		}
	}

	if (ioctl(l_fd, BIOCGBLEN, &size) != 0) {
		goto cleanup;
	}

	if (size < 1024 || size > BPF_MAXBUFSIZE) {
		goto cleanup;
	}

	if ((l_buf = malloc(size)) == NULL) {
		goto cleanup;
	}

	if (set_filter) {
		memset(&bf, 0, sizeof(bf));
		bf.bf_len = __arraycount(test94_filter);
		bf.bf_insns = test94_filter;
		if (ioctl(l_fd, BIOCSETF, &bf) != 0) {
			goto cleanup;
		}
	}

	memset(&ifr, 0, sizeof(ifr));
	if (strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name)) >= sizeof(ifr.ifr_name)) {
		goto cleanup;
	}
	if (ioctl(l_fd, BIOCSETIF, &ifr) != 0) {
		goto cleanup;
	}

	if (ioctl(l_fd, BIOCGDLT, &dlt) != 0) {
		goto cleanup;
	}
	if (dlt != DLT_RAW) {
		goto cleanup;
	}

	if ((l_fd2 = socket(AF_INET, SOCK_DGRAM, 0)) < 0) {
		goto cleanup;
	}

	memset(&sinA, 0, sizeof(sinA));
	sinA.sin_family = AF_INET;
	sinA.sin_port = htons(TEST_PORT_A);
	sinA.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	if (bind(l_fd2, (struct sockaddr *)&sinA, sizeof(sinA)) != 0) {
		goto cleanup;
	}

	memcpy(&sinB, &sinA, sizeof(sinB));
	sinB.sin_port = htons(TEST_PORT_B);
	if (connect(l_fd2, (struct sockaddr *)&sinB, sizeof(sinB)) != 0) {
		goto cleanup;
	}

	if ((l_fd3 = socket(AF_INET, SOCK_DGRAM, 0)) < 0) {
		goto cleanup;
	}

	if (bind(l_fd3, (struct sockaddr *)&sinB, sizeof(sinB)) != 0) {
		goto cleanup;
	}

	if (connect(l_fd3, (struct sockaddr *)&sinA, sizeof(sinA)) != 0) {
		goto cleanup;
	}

	*fd = l_fd;
	*fd2 = l_fd2;
	*fd3 = l_fd3;
	*buf = l_buf;
	ret_size = size;

cleanup:
	if (ret_size == 0) {
		if (l_fd != -1) close(l_fd);
		if (l_fd2 != -1) close(l_fd2);
		if (l_fd3 != -1) close(l_fd3);
		if (l_buf != NULL) free(l_buf);
	}
	return ret_size;
}

/*
 * Clean up resources allocated by test94_setup().
 */
static void _cleanup_close_fd(int fd_to_close)
{
    if (close(fd_to_close) != 0) {
        e(0);
    }
}

static void
test94_cleanup(int fd, int fd2, int fd3, uint8_t * buf)
{
    _cleanup_close_fd(fd3);
    _cleanup_close_fd(fd2);
    free(buf);
    _cleanup_close_fd(fd);
}

/*
 * Test reading packets from a BPF device, using regular mode.
 */
static void test94a(void);

#ifndef __arraycount
#define __arraycount(a) (sizeof(a) / sizeof((a)[0]))
#endif

// Forward declarations for external test functions and global variables
extern int errct;
extern int subtest;
extern volatile sig_atomic_t got_signal;
extern int e(int);
extern void test94_setup(int *fd, int *fd2, int *fd3, uint8_t **buf, size_t initial_size, int set_filter);
extern void test94_fill_random(int fd, uint8_t *buf, size_t size);
extern uint32_t test94_check(uint8_t *buf, ssize_t len, uint32_t seq_start, int filtered, size_t *caplen, size_t *datalen);
extern void test94_add_random(int fd, uint8_t *buf, size_t size, uint32_t seq);
extern void test94_cleanup(int fd, int fd2, int fd3, uint8_t *buf);
extern const struct bpf_insn test94_filter[];
extern long SLEEP_TIME;
extern void test94_signal(int sig);

// Constants for read length checks
#define MIN_READ_FRACTION_NUMERATOR 3
#define MIN_READ_FRACTION_DENOMINATOR 4

// Helper for nanosleep, replacing usleep
static void test94_nanosleep_us(long us) {
    struct timespec ts;
    ts.tv_sec = us / 1000000;
    ts.tv_nsec = (us % 1000000) * 1000;
    while (nanosleep(&ts, &ts) == -1 && errno == EINTR);
}

// Helper for generic syscall error checking
static void check_syscall_result(int result, const char *operation_name) {
    if (result == -1) {
        e(0);
    }
}

// Helper for value equality check
static void check_equal_value(long actual, long expected, const char *description) {
    if (actual != expected) {
        e(0);
    }
}

// Helper for errno specific checks
static void check_errno_value(int result, int expected_errno_val, const char *operation_name) {
    if (result != -1) {
        e(0);
    }
    if (errno != expected_errno_val) {
        e(0);
    }
}

// Helper for full buffer read length checks
static void check_read_len_full(ssize_t len, size_t size_param) {
    if ((size_t)len < size_param * MIN_READ_FRACTION_NUMERATOR / MIN_READ_FRACTION_DENOMINATOR) e(0);
    if ((size_t)len > size_param) e(0);
}

// Helper for partial buffer read length checks
static void check_read_len_partial(ssize_t len, size_t size_param) {
    if (len <= 0) e(0);
    if ((size_t)len >= size_param * MIN_READ_FRACTION_NUMERATOR / MIN_READ_FRACTION_DENOMINATOR) e(0);
}

// Type for child process functions
typedef void (*child_process_func)(int fd, int fd2, int fd3, uint8_t *buf, size_t size, uint32_t seq_start);

// Generic helper to run a child process and wait for its completion
static void run_child_and_wait(child_process_func child_task, int fd, int fd2, int fd3, uint8_t *buf, size_t size, uint32_t seq_start) {
    pid_t pid = fork();
    check_syscall_result(pid, "fork");

    if (pid == 0) { // Child process
        errct = 0;
        child_task(fd, fd2, fd3, buf, size, seq_start);
        exit(errct);
    } else { // Parent process
        int status;
        check_equal_value(wait(&status), pid, "wait for child");
        if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);
    }
}

// Child task: Fill random data after a sleep
static void child_task_fill_random_after_sleep(int fd, int fd2, int fd3, uint8_t *buf, size_t size, uint32_t seq_start) {
    (void)fd; (void)fd3; (void)seq_start; // Unused parameters
    test94_nanosleep_us(SLEEP_TIME);
    test94_fill_random(fd2, buf, size);
}

// Child task: Add random data after a sleep, then wait for signal, then check signal
static void child_task_add_random_signal_wait(int fd, int fd2, int fd3, uint8_t *buf, size_t size, uint32_t seq_start) {
    (void)fd; (void)fd3; // Unused parameters
    signal(SIGUSR1, test94_signal);
    test94_nanosleep_us(SLEEP_TIME);
    test94_add_random(fd2, buf, size, seq_start);
    test94_nanosleep_us(SLEEP_TIME);
    check_equal_value(got_signal, 0, "child_task_add_random_signal_wait: got_signal before pause");
    pause();
    check_equal_value(got_signal, 1, "child_task_add_random_signal_wait: got_signal after pause");
}

// Child task: Read and expect EINTR after signal
static void child_task_read_expect_eintr(int fd, int fd2, int fd3, uint8_t *buf, size_t size, uint32_t seq_start) {
    (void)fd2; (void)fd3; (void)seq_start; // Unused parameters
    signal(SIGUSR1, test94_signal);
    check_errno_value(read(fd, buf, size), EINTR, "child_task_read_expect_eintr: read");
    check_equal_value(got_signal, 1, "child_task_read_expect_eintr: got_signal");
}

// Child task: Add random data after sleep
static void child_task_add_random_after_sleep(int fd, int fd2, int fd3, uint8_t *buf, size_t size, uint32_t seq_start) {
    (void)fd; (void)fd3; // Unused parameters
    test94_nanosleep_us(SLEEP_TIME);
    test94_add_random(fd2, buf, size, seq_start);
}

// Helper to set BPF filter
static void set_bpf_filter(int fd) {
    struct bpf_program bf;
    memset(&bf, 0, sizeof(bf));
    bf.bf_len = __arraycount(test94_filter);
    bf.bf_insns = (struct bpf_insn *)test94_filter;
    check_syscall_result(ioctl(fd, BIOCSETF, &bf), "BIOCSETF");
}

// Helper to set BPF read timeout
static void set_bpf_read_timeout(int fd, long tv_sec, long tv_usec) {
    struct timeval tv = {.tv_sec = tv_sec, .tv_usec = tv_usec};
    check_syscall_result(ioctl(fd, BIOCSRTIMEOUT, &tv), "BIOCSRTIMEOUT");
}

// Helper to check select status
static void check_select_status(int fd, int expected_ready_fds, const struct timeval *timeout_val) {
    fd_set fds;
    FD_ZERO(&fds);
    FD_SET(fd, &fds);
    int select_result = select(fd + 1, &fds, NULL, NULL, (struct timeval *)timeout_val); // Cast to non-const as select can modify
    check_equal_value(select_result, expected_ready_fds, "select");
    if (expected_ready_fds > 0) {
        if (!FD_ISSET(fd, &fds)) e(0);
    } else {
        if (FD_ISSET(fd, &fds)) e(0);
    }
}

// Helper to get FIONREAD bytes
static int get_fionread_bytes(int fd) {
    int bytes;
    check_syscall_result(ioctl(fd, FIONREAD, &bytes), "FIONREAD");
    return bytes;
}

static void test94a(void) {
    int fd, fd2, fd3, status;
    uint8_t *buf;
    size_t size;
    ssize_t len;
    uint32_t seq;
    int bytes_avail;
    int original_fl;
    pid_t current_pid;

    subtest = 1;

    size = test94_setup(&fd, &fd2, &fd3, &buf, 0 /*size*/, 0 /*set_filter*/);

    // Test 1: Filled-up store buffer returned to pending read (no filter)
    run_child_and_wait(child_task_fill_random_after_sleep, fd, fd2, fd3, buf, size, 0);

    len = read(fd, buf, size);
    check_read_len_full(len, size);
    test94_check(buf, len, 1 /*seq*/, 0 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/);

    // Test 2: Read call size validation
    check_errno_value(read(fd, buf, size - 1), EINVAL, "read with size - 1");
    check_errno_value(read(fd, buf, size + 1), EINVAL, "read with size + 1");
    check_errno_value(read(fd, buf, sizeof(struct bpf_hdr)), EINVAL, "read with bpf_hdr size");

    // Install filter for remaining tests
    set_bpf_filter(fd);

    // Test 3: Already filled-up buffer returned immediately, select wakes up, FIONREAD check
    struct timeval tv_no_timeout = {.tv_sec = 0, .tv_usec = 0};
    check_select_status(fd, 0, &tv_no_timeout);
    check_equal_value(get_fionread_bytes(fd), 0, "FIONREAD initial empty");

    run_child_and_wait(child_task_fill_random_after_sleep, fd, fd2, fd3, buf, size, 0);

    check_select_status(fd, 1, NULL); // Blocking select, should be ready
    bytes_avail = get_fionread_bytes(fd);
    check_select_status(fd, 1, NULL); // Still ready

    len = read(fd, buf, size);
    check_read_len_full(len, size);
    seq = test94_check(buf, len, 1 /*seq*/, 1 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/);
    check_equal_value(len, bytes_avail, "read len vs FIONREAD bytes");

    // After read, check select and FIONREAD again
    check_select_status(fd, 0, &tv_no_timeout);
    check_equal_value(get_fionread_bytes(fd), 0, "FIONREAD post-read");

    // Test 4: Timed-out read returns any packets, signal interruption
    got_signal = 0;
    current_pid = fork();
    check_syscall_result(current_pid, "fork for signal test");
    if (current_pid == 0) { // Child process
        errct = 0;
        child_task_add_random_signal_wait(fd, fd2, fd3, buf, size, seq + 1);
        exit(errct);
    } else { // Parent process
        set_bpf_read_timeout(fd, 0, SLEEP_TIME * 3);

        len = read(fd, buf, size);
        check_read_len_partial(len, size); // Expecting < 3/4 of size (two packets)
        check_equal_value(test94_check(buf, len, seq, 1 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/), seq + 2, "read seq count");

        check_syscall_result(kill(current_pid, SIGUSR1), "kill SIGUSR1");

        check_equal_value(wait(&status), current_pid, "wait after kill");
        if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);
    }
    seq += 2; // Update seq for subsequent tests

    // Test 5: Timed-out read with empty buffer yields EAGAIN
    set_bpf_read_timeout(fd, 0, SLEEP_TIME);
    check_errno_value(read(fd, buf, size), EAGAIN, "read empty buffer with timeout");

    // Test 6: Reset timeout to zero, call blocks forever, then interrupted by signal
    set_bpf_read_timeout(fd, 0, 0);
    got_signal = 0;

    current_pid = fork();
    check_syscall_result(current_pid, "fork for EINTR test");
    if (current_pid == 0) { // Child process
        errct = 0;
        child_task_read_expect_eintr(fd, fd2, fd3, buf, size, 0);
        exit(errct);
    } else { // Parent process
        test94_nanosleep_us(SLEEP_TIME * 2); // Allow child to block on read
        check_syscall_result(kill(current_pid, SIGUSR1), "kill SIGUSR1");

        check_equal_value(wait(&status), current_pid, "wait after kill EINTR");
        if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);
    }

    // Test 7: Interrupted read with non-full, non-empty buffer does not return partial results
    got_signal = 0;
    current_pid = fork();
    check_syscall_result(current_pid, "fork for EINTR partial buffer test");
    if (current_pid == 0) { // Child process
        errct = 0;
        child_task_read_expect_eintr(fd, fd2, fd3, buf, size, 0);
        exit(errct);
    } else { // Parent process
        test94_nanosleep_us(SLEEP_TIME);
        test94_add_random(fd2, buf, size, 2); // Add one packet
        test94_nanosleep_us(SLEEP_TIME);

        check_syscall_result(kill(current_pid, SIGUSR1), "kill SIGUSR1");

        check_equal_value(wait(&status), current_pid, "wait after kill EINTR partial");
        if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);
    }

    // Test 8: Non-blocking reads with empty, full, and non-empty buffers
    check_syscall_result(original_fl = fcntl(fd, F_GETFL), "F_GETFL");
    check_syscall_result(fcntl(fd, F_SETFL, original_fl | O_NONBLOCK), "F_SETFL O_NONBLOCK");

    // Read remaining packet from previous test (if any, test94_add_random adds one)
    len = read(fd, buf, size);
    check_read_len_partial(len, size); // Expecting one packet < 3/4 of size
    seq = test94_check(buf, len, 2 /*seq*/, 1 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/);

    // Read empty buffer in non-blocking mode
    check_errno_value(read(fd, buf, size), EAGAIN, "non-blocking read empty");

    // Fill buffer and read full
    test94_fill_random(fd2, buf, size);
    len = read(fd, buf, size);
    check_read_len_full(len, size);
    seq = test94_check(buf, len, 1 /*seq*/, 1 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/);

    // Read remaining partial buffer from fill (one packet left by test94_fill_random or multiple if it fills up internal buffer and then some)
    len = read(fd, buf, size);
    check_read_len_partial(len, size); // Expecting one packet < 3/4 of size
    seq = test94_check(buf, len, seq, 1 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/);

    check_syscall_result(fcntl(fd, F_SETFL, original_fl), "F_SETFL restore");

    // Test 9: Select not waking up on single-packet arrivals, read timer has no effect on select
    set_bpf_read_timeout(fd, 0, SLEEP_TIME * 2);

    run_child_and_wait(child_task_add_random_after_sleep, fd, fd2, fd3, buf, size, 1);

    // Select with timeout, expecting no wakeup
    check_select_status(fd, 0, &(struct timeval){.tv_sec = 1, .tv_usec = 0});

    test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test reading packets from a BPF device, using immediate mode.
 */
#include <sys/types.h>
#include <sys/time.h>
#include <sys/ioctl.h>
#include <sys/select.h>
#include <unistd.h>
#include <stdint.h>
#include <stdlib.h>
#include <errno.h>
#include <sys/wait.h>
#include <fcntl.h>

#ifndef SLEEP_TIME
#define SLEEP_TIME 200000
#endif

static void
perform_select_check(int fd, fd_set *fds, struct timeval *timeout, int expected_retval, int check_fd_isset)
{
    FD_ZERO(fds);
    FD_SET(fd, fds);
    if (select(fd + 1, fds, NULL, NULL, timeout) != expected_retval) {
        e(0);
    }
    if (check_fd_isset && expected_retval > 0 && !FD_ISSET(fd, fds)) {
        e(0);
    }
}

static int
get_fionread_bytes_checked(int fd)
{
    int bytes;
    if (ioctl(fd, FIONREAD, &bytes) != 0) {
        e(0);
    }
    return bytes;
}

static void
test94b(void)
{
	struct timeval tv_zero = {0, 0};
	struct timeval tv_sleep_time = {0, SLEEP_TIME};
	fd_set fds;
	uint8_t *buf = NULL;
	unsigned int val;
	size_t size = 0;
	ssize_t len;
	uint32_t seq;
	pid_t pid;
	int fd = -1, fd2 = -1, fd3 = -1;
	int bytes, status;
	int original_flags;

	subtest = 2;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);

	val = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &val) != 0) e(0);

	perform_select_check(fd, &fds, &tv_zero, 0, 0);
	if (get_fionread_bytes_checked(fd) != 0) e(0);

	test94_fill_random(fd2, buf, size);

	perform_select_check(fd, &fds, &tv_zero, 1, 1);
	bytes = get_fionread_bytes_checked(fd);

	len = read(fd, buf, size);
	if (len < (ssize_t)(size * 3 / 4)) e(0);
	if (len > (ssize_t)size) e(0);
	seq = test94_check(buf, len, 1, 1, NULL, NULL);
	if (len != bytes) e(0);

	perform_select_check(fd, &fds, &tv_zero, 1, 1);
	bytes = get_fionread_bytes_checked(fd);

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)(size * 3 / 4)) e(0);
	if (test94_check(buf, len, seq, 1, NULL, NULL) != seq + 1) e(0);
	if (len != bytes) e(0);

	perform_select_check(fd, &fds, &tv_zero, 0, 0);
	if (get_fionread_bytes_checked(fd) != 0) e(0);

	test94_add_random(fd2, buf, size, seq + 1);
	test94_add_random(fd2, buf, size, seq + 2);

	perform_select_check(fd, &fds, &tv_zero, 1, 1);
	bytes = get_fionread_bytes_checked(fd);

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)(size * 3 / 4)) e(0);
	if (test94_check(buf, len, seq + 1, 1, NULL, NULL) != seq + 3) e(0);
	if (len != bytes) e(0);

	pid = fork();
	if (pid == -1) {
		e(0);
	} else if (pid == 0) {
		errct = 0;
		usleep(SLEEP_TIME);
		test94_add_random(fd2, buf, size, seq + 3);
		exit(errct);
	}

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)(size * 3 / 4)) e(0);
	if (test94_check(buf, len, seq + 3, 1, NULL, NULL) != seq + 4) e(0);

	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	pid = fork();
	if (pid == -1) {
		e(0);
	} else if (pid == 0) {
		errct = 0;
		usleep(SLEEP_TIME);
		test94_add_random(fd2, buf, size, seq + 4);
		exit(errct);
	}

	perform_select_check(fd, &fds, NULL, 1, 1);

	bytes = get_fionread_bytes_checked(fd);
	perform_select_check(fd, &fds, NULL, 1, 1);

	len = read(fd, buf, size);
	if (len <= 0) e(0);
	if (len >= (ssize_t)(size * 3 / 4)) e(0);
	if (test94_check(buf, len, seq + 4, 1, NULL, NULL) != seq + 5) e(0);
	if (len != bytes) e(0);

	if (wait(&status) != pid) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	original_flags = fcntl(fd, F_GETFL);
	if (original_flags == -1) e(0);
	if (fcntl(fd, F_SETFL, original_flags | O_NONBLOCK) != 0) e(0);

	len = read(fd, buf, size);
	if (len != -1) e(0);
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

	if (fcntl(fd, F_SETFL, original_flags) != 0) e(0);

	if (ioctl(fd, BIOCSRTIMEOUT, &tv_sleep_time) != 0) e(0);

	len = read(fd, buf, size);
	if (len != -1) e(0);
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
	uint32_t count, seq_val;
	int fd, fd2, fd3, bytes, status, fl;
	uint32_t expected_capt = 0;
	uint32_t expected_drop = 0;

	subtest = 3;

	size = test94_setup(&fd, &fd2, &fd3, &buf, 0, 1);
	if (size == 0) e(0);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != expected_capt) e(0);
	if (bs.bs_drop != expected_drop) e(0);

	count = test94_fill_exact(fd2, buf, size, 0);
	expected_capt += count;

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != expected_capt) e(0);
	if (bs.bs_recv < bs.bs_capt) e(0);
	if (bs.bs_drop != expected_drop) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);
	if ((size_t)bytes != size) e(0);

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);

	if (read(fd, buf, size) != (ssize_t)size) e(0);
	test94_check(buf, size, 0, 1, NULL, NULL);

	seq_val = test94_fill_exact(fd2, buf, size, 1);
	expected_capt += count;
	test94_fill_exact(fd2, buf, size, seq_val);
	expected_capt += count;

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != expected_capt) e(0);
	if (bs.bs_recv < bs.bs_capt) e(0);
	if (bs.bs_drop != expected_drop) e(0);

	test94_add_random(fd2, buf, size, 0);
	expected_capt++;
	expected_drop++;

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != expected_capt) e(0);
	if (bs.bs_recv < bs.bs_capt) e(0);
	if (bs.bs_drop != expected_drop) e(0);

	test94_add_random(fd2, buf, size, 0);
	expected_capt++;
	expected_drop++;

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != expected_capt) e(0);
	if (bs.bs_recv < bs.bs_capt) e(0);
	if (bs.bs_drop != expected_drop) e(0);

	if (ioctl(fd, FIONREAD, &bytes) != 0) e(0);
	if ((size_t)bytes != size) e(0);

	if (read(fd, buf, size) != (ssize_t)size) e(0);
	if (test94_check(buf, size, 1, 1, NULL, NULL) != seq_val) e(0);

	if (read(fd, buf, size) != (ssize_t)size) e(0);
	if (test94_check(buf, size, seq_val, 1, NULL, NULL) != count * 2 + 1) e(0);

	pid = fork();
	if (pid == -1) {
		e(0);
	} else if (pid == 0) {
		errct = 0;
		usleep(SLEEP_TIME);
		test94_fill_exact(fd2, buf, size, 1);
		exit(errct);
	}
	expected_capt += count;

	if (read(fd, buf, size) != (ssize_t)size) e(0);
	test94_check(buf, size, 1, 1, NULL, NULL);

	if (waitpid(pid, &status, 0) == -1) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	pid = fork();
	if (pid == -1) {
		e(0);
	} else if (pid == 0) {
		errct = 0;
		usleep(SLEEP_TIME);
		test94_fill_exact(fd2, buf, size, seq_val);
		exit(errct);
	}
	expected_capt += count;

	FD_ZERO(&fds);
	FD_SET(fd, &fds);
	if (select(fd + 1, &fds, NULL, NULL, NULL) != 1) e(0);
	if (!FD_ISSET(fd, &fds)) e(0);

	if ((fl = fcntl(fd, F_GETFL)) == -1) e(0);
	if (fcntl(fd, F_SETFL, fl | O_NONBLOCK) == -1) e(0);

	if (read(fd, buf, size) != (ssize_t)size) e(0);
	test94_check(buf, size, seq_val, 1, NULL, NULL);

	if (read(fd, buf, size) != -1) e(0);
	if (errno != EAGAIN) e(0);

	if (waitpid(pid, &status, 0) == -1) e(0);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) e(0);
	if (bs.bs_capt != expected_capt) e(0);
	if (bs.bs_recv < bs.bs_capt) e(0);
	if (bs.bs_drop != expected_drop) e(0);

	test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Test receipt of large packets on BPF devices.  Large packets should be
 * truncated to the size of the buffer, but unless the filter specifies a
 * smaller capture size, no more than that.
 */
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/ip.h>
#include <netinet/udp.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdint.h>

extern void e(int);
extern int subtest;
extern size_t test94_setup(int *fd, int *fd2, int *fd3, uint8_t **buf, size_t size, int set_filter);
extern void test94_add_random(int fd2, uint8_t *buf, size_t size, int seq);
extern int test94_check(const uint8_t *buf, ssize_t len, int seq, int filtered, size_t *caplen, size_t *datalen);
extern void test94_cleanup(int fd, int fd2, int fd3, uint8_t *buf);

struct bpf_timeval {
	uint32_t tv_sec;
	uint32_t tv_usec;
};

struct bpf_hdr {
	struct bpf_timeval bh_tstamp;
	uint32_t bh_caplen;
	uint32_t bh_datalen;
	uint16_t bh_hdrlen;
	uint16_t bh_padding;
};

#ifndef BPF_WORDALIGN
#define BPF_WORDALIGN(x) (((x) + 3) & ~3)
#endif

#define TEST94_BUFFER_SIZE 32768
#define TEST94_DATALEN_TO_SEND 65000

static int
check_bpf_packet_integrity(const uint8_t *buf, size_t expected_buf_size, int expected_datalen)
{
	struct bpf_hdr bh_local;

	if (buf == NULL) {
		return -1;
	}

	memcpy(&bh_local, buf, sizeof(bh_local));

	if (bh_local.bh_hdrlen != BPF_WORDALIGN(sizeof(bh_local))) {
		return -1;
	}
	if (bh_local.bh_caplen != expected_buf_size - BPF_WORDALIGN(sizeof(bh_local))) {
		return -1;
	}
	if (bh_local.bh_datalen != (uint32_t)sizeof(struct ip) + sizeof(struct udphdr) + expected_datalen) {
		return -1;
	}

	if (buf[BPF_WORDALIGN(sizeof(bh_local)) + sizeof(struct ip) + sizeof(struct udphdr)] != 'X') {
		return -1;
	}
	if (buf[expected_buf_size - 2] != 'Y') {
		return -1;
	}
	if (buf[expected_buf_size - 1] != 'Z') {
		return -1;
	}

	return 0;
}

static void
test94d(void)
{
	uint8_t *buf = NULL, *buf2 = NULL;
	size_t current_capture_size;
	ssize_t bytes_read;
	int fd = -1, fd2 = -1, fd3 = -1;
	int datalen_to_send;

	subtest = 4;

	current_capture_size = test94_setup(&fd, &fd2, &fd3, &buf, TEST94_BUFFER_SIZE, 1 /*set_filter*/);
	if (current_capture_size != TEST94_BUFFER_SIZE) {
		e(0);
	}

	datalen_to_send = TEST94_DATALEN_TO_SEND;
	if (setsockopt(fd2, SOL_SOCKET, SO_SNDBUF, &datalen_to_send, sizeof(datalen_to_send)) != 0) {
		goto fail_cleanup_fds_buf;
	}

	if ((buf2 = malloc(datalen_to_send)) == NULL) {
		goto fail_cleanup_fds_buf;
	}

	memset(buf2, 'Y', datalen_to_send);
	buf2[0] = 'X';
	buf2[current_capture_size - sizeof(struct udphdr) - sizeof(struct ip) - BPF_WORDALIGN(sizeof(struct bpf_hdr)) - 1] = 'Z';

	if (write(fd2, buf2, datalen_to_send) != datalen_to_send) {
		goto fail_cleanup_all;
	}

	bytes_read = read(fd, buf, current_capture_size);
	if (bytes_read != (ssize_t)current_capture_size) {
		goto fail_cleanup_all;
	}

	if (check_bpf_packet_integrity(buf, current_capture_size, datalen_to_send) != 0) {
		goto fail_cleanup_all;
	}

	test94_add_random(fd2, buf, current_capture_size, 1 /*seq*/);

	if (write(fd2, buf2, datalen_to_send) != datalen_to_send) {
		goto fail_cleanup_all;
	}

	bytes_read = read(fd, buf, current_capture_size);
	if (bytes_read <= 0 || bytes_read >= (ssize_t)(current_capture_size * 3 / 4)) {
		goto fail_cleanup_all;
	}
	if (test94_check(buf, bytes_read, 1 /*seq*/, 1 /*filtered*/, NULL /*caplen*/, NULL /*datalen*/) != 2) {
		goto fail_cleanup_all;
	}

	bytes_read = read(fd, buf, current_capture_size);
	if (bytes_read != (ssize_t)current_capture_size) {
		goto fail_cleanup_all;
	}

	if (check_bpf_packet_integrity(buf, current_capture_size, datalen_to_send) != 0) {
		goto fail_cleanup_all;
	}

	free(buf2);
	test94_cleanup(fd, fd2, fd3, buf);
	return;

fail_cleanup_all:
	free(buf2);

fail_cleanup_fds_buf:
	test94_cleanup(fd, fd2, fd3, buf);
	e(0);
}

/*
 * Test whether our filter is active through two-way communication and a
 * subsequent check on the BPF statistics.  We do not actually look through the
 * captured packets, because who knows what else is active on the loopback
 * device (e.g., X11) and the extra code specifically to extract our packets in
 * the other direction is simply not worth it.
 */
static inline void safe_write_char(int fd, char val)
{
    if (write(fd, &val, 1) != 1) {
        e(0);
    }
}

static inline char safe_read_char(int fd)
{
    char c;
    if (read(fd, &c, 1) != 1) {
        e(0);
    }
    return c;
}

static inline void safe_ioctl_call(int fd, unsigned long request, void *arg)
{
    if (ioctl(fd, request, arg) != 0) {
        e(0);
    }
}

static void
test94_comm(int fd, int fd2, int fd3, int filtered)
{
    struct bpf_stat bs;
    char c_read;

    safe_write_char(fd2, 'A');

    c_read = safe_read_char(fd3);
    if (c_read != 'A') {
        e(0);
    }

    safe_ioctl_call(fd, BIOCGSTATS, &bs);
    if (bs.bs_recv == 0) {
        e(0);
    }
    if (bs.bs_capt == 0) {
        e(0);
    }

    safe_ioctl_call(fd, BIOCFLUSH, (void*)0);

    safe_write_char(fd3, 'B');

    c_read = safe_read_char(fd2);
    if (c_read != 'B') {
        e(0);
    }

    safe_ioctl_call(fd, BIOCGSTATS, &bs);
    if (bs.bs_recv == 0) {
        e(0);
    }

    if (filtered) {
        if (bs.bs_capt != 0) {
            e(0);
        }
        if (bs.bs_drop != 0) {
            e(0);
        }
    } else {
        if (bs.bs_capt == 0) {
            e(0);
        }
    }

    safe_ioctl_call(fd, BIOCFLUSH, (void*)0);
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
	uint8_t *buf = NULL;
	size_t size = 0, len, off;
	uint32_t seq_val, caplen[4], datalen[4];
	int i, fd = -1, fd2 = -1, fd3 = -1, val;
	int original_errno;

	subtest = 5;

	/*
	 * We have already tested installing a filter both before and after
	 * attaching to an interface by now, so we do not repeat that here.
	 */
	size = test94_setup(&fd, &fd2, &fd3, &buf, 0 /*size*/, 0 /*set_filter*/);
	if (fd == -1 || fd2 == -1 || fd3 == -1 || buf == NULL) {
		e(0); /* Setup failed, likely indicates an unrecoverable error */
	}

	val = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &val) != 0) {
		e(0);
	}

	/*
	 * A filter that is too large is rejected.  Unfortunately, due to
	 * necessary IOCTL rewriting, this tests libc, not the service.
	 */
	memset(&bf, 0, sizeof(bf));
	bf.bf_len = BPF_MAXINSNS + 1;
	bf.bf_insns = NULL;
	if (ioctl(fd, BIOCSETF, &bf) != -1) {
		e(0);
	}
	original_errno = errno; /* Save errno immediately */
	if (original_errno != EINVAL) {
		e(0);
	}

	/*
	 * An invalid filter is rejected.  In this test case, the truncated
	 * filter has a jump target beyond the end of the filter program.
	 */
	memset(&bf, 0, sizeof(bf));
	bf.bf_len = __arraycount(test94_filter) - 1;
	bf.bf_insns = test94_filter;
	if (ioctl(fd, BIOCSETF, &bf) != -1) {
		e(0);
	}
	original_errno = errno;
	if (original_errno != EINVAL) {
		e(0);
	}

	test94_comm(fd, fd2, fd3, 0 /*filtered*/);

	bf.bf_len++;
	if (ioctl(fd, BIOCSETF, &bf) != 0) {
		e(0);
	}

	test94_comm(fd, fd2, fd3, 1 /*filtered*/);

	/*
	 * Installing a zero-length filter clears the current filter, if any.
	 */
	memset(&bf, 0, sizeof(bf));
	if (ioctl(fd, BIOCSETF, &bf) != 0) {
		e(0);
	}

	test94_comm(fd, fd2, fd3, 0 /*filtered*/);

	/* Test this twice to trip over unconditional filter deallocation. */
	memset(&bf, 0, sizeof(bf));
	if (ioctl(fd, BIOCSETF, &bf) != 0) {
		e(0);
	}

	test94_comm(fd, fd2, fd3, 0 /*filtered*/);

	/*
	 * Test both aligned and unaligned capture sizes.  For each, test
	 * sizes larger than, equal to, and smaller than the capture size.
	 * In both cases, aggregate the packets into a single buffer and only
	 * then go through them, to see whether alignment was done correctly.
	 * We cannot do everything in one go as BIOCSETF implies a BIOCFLUSH.
	 */
	size_t plen = sizeof(struct ip) + sizeof(struct udphdr) + sizeof(seq_val);
	if (BPF_WORDALIGN(plen) != plen) {
		e(0);
	}
	size_t alen = BPF_WORDALIGN(plen + 1);
	if (alen <= plen + 1) { /* Changed from alen - 2 <= plen + 1 for clarity, same logic */
		e(0);
	}

	/* First the aligned cases. */
	test94_filter[__arraycount(test94_filter) - 1].k = (uint32_t)alen;

	memset(&bf, 0, sizeof(bf));
	bf.bf_len = __arraycount(test94_filter);
	bf.bf_insns = test94_filter;
	if (ioctl(fd, BIOCSETF, &bf) != 0) {
		e(0);
	}

	test94_comm(fd, fd2, fd3, 1 /*filtered*/);

	test94_add_specific(fd2, buf, alen + 1 - plen, 1);
	caplen[0] = (uint32_t)alen;
	datalen[0] = (uint32_t)alen + 1;

	test94_add_specific(fd2, buf, alen - plen, 2);
	caplen[1] = (uint32_t)alen;
	datalen[1] = (uint32_t)alen;

	test94_add_specific(fd2, buf, alen + 3 - plen, 3);
	caplen[2] = (uint32_t)alen;
	datalen[2] = (uint32_t)alen + 3;

	test94_add_specific(fd2, buf, alen - 1 - plen, 4);
	caplen[3] = (uint32_t)alen - 1;
	datalen[3] = (uint32_t)alen - 1;

	memset(buf, 0, size);

	len = read(fd, buf, size);
	if (len == (size_t)-1) {
		e(0); /* Read error */
	}

	if (test94_check(buf, len, 1 /*seq*/, 1 /*filtered*/, caplen, datalen) != 5) {
		e(0);
	}

	/* Then the unaligned cases. */
	test94_filter[__arraycount(test94_filter) - 1].k = (uint32_t)alen + 1;
	if (ioctl(fd, BIOCSETF, &bf) != 0) {
		e(0);
	}

	test94_add_specific(fd2, buf, alen + 2 - plen, 5);
	caplen[0] = (uint32_t)alen + 1;
	datalen[0] = (uint32_t)alen + 2;

	test94_add_specific(fd2, buf, alen + 1 - plen, 6);
	caplen[1] = (uint32_t)alen + 1;
	datalen[1] = (uint32_t)alen + 1;

	test94_add_specific(fd2, buf, alen + 9 - plen, 7);
	caplen[2] = (uint32_t)alen + 1;
	datalen[2] = (uint32_t)alen + 9;

	test94_add_specific(fd2, buf, alen - plen, 8);
	caplen[3] = (uint32_t)alen;
	datalen[3] = (uint32_t)alen;

	memset(buf, 0, size);

	len = read(fd, buf, size);
	if (len == (size_t)-1) {
		e(0); /* Read error */
	}

	if (test94_check(buf, len, 5 /*seq*/, 1 /*filtered*/, caplen, datalen) != 9) {
		e(0);
	}

	/*
	 * Check that capturing only one byte from packets is possible.  Not
	 * that that would be particularly useful.
	 */
	test94_filter[__arraycount(test94_filter) - 1].k = 1;
	if (ioctl(fd, BIOCSETF, &bf) != 0) {
		e(0);
	}

	test94_add_random(fd2, buf, size, 9);
	test94_add_random(fd2, buf, size, 10);
	test94_add_random(fd2, buf, size, 11);

	memset(buf, 0, size);

	len = read(fd, buf, size);
	if (len <= 0) {
		e(0);
	}

	off = 0;
	for (i = 0; i < 3; i++) {
		if (len - off < sizeof(bh)) {
			e(0);
		}
		memcpy(&bh, &buf[off], sizeof(bh));

		if (bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) {
			e(0);
		}
		if (bh.bh_caplen != 1) {
			e(0);
		}
		if (bh.bh_datalen < plen) {
			e(0);
		}
		if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh))) {
			e(0);
		}

		off += bh.bh_hdrlen;

		if (off >= len) { /* Ensure we don't read past the buffer */
			e(0);
		}
		if (buf[off] != 0x45) {
			e(0);
		}

		off += BPF_WORDALIGN(bh.bh_caplen);
		if (off > len && i < 2) { /* Should not exceed len until the very end */
			e(0);
		}
	}
	if (off != len) {
		e(0);
	}

	/*
	 * Finally, a zero capture size should result in rejected packets only.
	 */
	test94_filter[__arraycount(test94_filter) - 1].k = 0;
	if (ioctl(fd, BIOCSETF, &bf) != 0) {
		e(0);
	}

	test94_add_random(fd2, buf, size, 12);
	test94_add_random(fd2, buf, size, 13);
	test94_add_random(fd2, buf, size, 14);

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) {
		e(0);
	}
	if (bs.bs_recv < 3) {
		e(0);
	}
	if (bs.bs_capt != 0) {
		e(0);
	}
	if (bs.bs_drop != 0) {
		e(0);
	}

	/* Restore the capture limit of the filter to its original state. */
	test94_filter[__arraycount(test94_filter) - 1].k = (uint32_t)-1;

	test94_cleanup(fd, fd2, fd3, buf);
}

/*
 * Compute an IP checksum.
 */
#include <stdint.h>
#include <stddef.h>

static uint16_t
test94_cksum(uint8_t * buf, size_t len)
{
	uint32_t sum = 0;

	while (len >= 2) {
		sum += ((uint32_t)buf[0] << 8) | buf[1];
		buf += 2;
		len -= 2;
	}

	if (len == 1) {
		sum += (uint32_t)buf[0] << 8;
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
	struct ip ip;
	struct ip6_hdr ip6;
	struct udphdr uh;
	size_t off;

	if (!v6) {
		memset(&ip, 0, sizeof(ip));
		ip.ip_v = IPVERSION;
		ip.ip_hl = sizeof(ip) >> 2;
		ip.ip_len = htons(sizeof(ip) + sizeof(uh) + len);
		ip.ip_ttl = 255;
		ip.ip_p = IPPROTO_UDP;
		ip.ip_src.s_addr = htonl(INADDR_LOOPBACK);
		ip.ip_dst.s_addr = htonl(INADDR_LOOPBACK);
		ip.ip_sum = 0; // Initialize sum to zero for calculation

		memcpy(buf, &ip, sizeof(ip)); // Copy IP header (without checksum yet) to buffer

		// Calculate checksum on the buffer content and update it directly in the buffer
		((struct ip *)buf)->ip_sum = htons(test94_cksum(buf, sizeof(ip)));

		// Verify checksum
		if (test94_cksum(buf, sizeof(ip)) != 0) e(0);

		off = sizeof(ip);
	} else {
		memset(&ip6, 0, sizeof(ip6));
		ip6.ip6_vfc = IPV6_VERSION;
		ip6.ip6_plen = htons(sizeof(uh) + len);
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
	uh.uh_ulen = htons(sizeof(uh) + len);
	uh.uh_sum = 0; /* lazy but we also don't have the data yet */

	memcpy(buf + off, &uh, sizeof(uh));

	return off + sizeof(uh);
}

/*
 * Test sending packets by writing to a BPF device.
 */
#define LOOPBACK_IFNAME "lo0"
#define TEST94F_HELLO_WORLD_LEN 6
#define TEST94F_LARGE_PKT_DATA_LEN 12345
#define TEST94F_PRIME_MODULO 251
#define TEST94F_MAX_BUF_ALLOC_SIZE (UINT16_MAX + 1)

static int check_fd_writable(int fd) {
    fd_set fds;
    FD_ZERO(&fds);
    FD_SET(fd, &fds);
    if (select(fd + 1, NULL, &fds, NULL, NULL) != 1) {
        return -1;
    }
    if (!FD_ISSET(fd, &fds)) {
        return -1;
    }
    return 0;
}

static int verify_pattern_data(const uint8_t *buf, size_t data_len) {
    for (size_t i = 0; i < data_len; i++) {
        if (buf[i] != (uint8_t)(1 + (i % TEST94F_PRIME_MODULO))) {
            return -1;
        }
    }
    return 0;
}

static void
test94f(void)
{
	struct bpf_stat bs;
	struct ifreq ifr;
	uint8_t *buf = NULL;
	size_t off;
	unsigned int mtu = 0;
	int fd = -1, fd2 = -1, fd3 = -1;
    size_t current_buf_size = 0;

	subtest = 6;

	(void)test94_setup(&fd, &fd2, &fd3, &buf, 0 /*size*/, 1 /*set_filter*/);

	if (check_fd_writable(fd) != 0) {
        goto cleanup_and_error;
    }

	memset(&ifr, 0, sizeof(ifr));
	if (strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name)) >= sizeof(ifr.ifr_name)) {
        goto cleanup_and_error;
    }

	if (ioctl(fd2, SIOCGIFMTU, &ifr) != 0) {
        goto cleanup_and_error;
    }
	mtu = ifr.ifr_mtu;

	uint8_t *new_buf = realloc(buf, TEST94F_MAX_BUF_ALLOC_SIZE);
    if (new_buf == NULL) {
        goto cleanup_and_error;
    }
    buf = new_buf;
    current_buf_size = TEST94F_MAX_BUF_ALLOC_SIZE;
	memset(buf, 0, current_buf_size);

	for (size_t i = current_buf_size; i > mtu; i--) {
		if (write(fd, buf, i) != -1) goto cleanup_and_error;
		if (errno != EMSGSIZE) goto cleanup_and_error;
	}

	if (write(fd, buf, mtu) != (ssize_t)mtu) goto cleanup_and_error;

	if (write(fd, buf, 0) != 0) goto cleanup_and_error;

	off = test94_make_pkt(buf, TEST94F_HELLO_WORLD_LEN, 0 /*v6*/);
    if (off + TEST94F_HELLO_WORLD_LEN > current_buf_size) {
        goto cleanup_and_error;
    }
	memcpy(buf + off, "Hello!", TEST94F_HELLO_WORLD_LEN);

	if (write(fd, buf, off + TEST94F_HELLO_WORLD_LEN) != (ssize_t)(off + TEST94F_HELLO_WORLD_LEN)) goto cleanup_and_error;

	memset(buf, 0, current_buf_size);
	if (read(fd3, buf, current_buf_size) != (ssize_t)TEST94F_HELLO_WORLD_LEN) goto cleanup_and_error;
	if (memcmp(buf, "Hello!", TEST94F_HELLO_WORLD_LEN) != 0) goto cleanup_and_error;

	unsigned int uval = 1;
	if (ioctl(fd, BIOCSFEEDBACK, &uval) != 0) goto cleanup_and_error;

	off = test94_make_pkt(buf, TEST94F_LARGE_PKT_DATA_LEN, 0 /*v6*/);
    if (off + TEST94F_LARGE_PKT_DATA_LEN > current_buf_size) {
        goto cleanup_and_error;
    }
	for (size_t i = 0; i < TEST94F_LARGE_PKT_DATA_LEN; i++) {
		buf[off + i] = (uint8_t)(1 + (i % TEST94F_PRIME_MODULO));
    }

	if (write(fd, buf, off + TEST94F_LARGE_PKT_DATA_LEN) != (ssize_t)(off + TEST94F_LARGE_PKT_DATA_LEN)) goto cleanup_and_error;

	memset(buf, 0, current_buf_size);
	if (recv(fd3, buf, current_buf_size, 0) != (ssize_t)TEST94F_LARGE_PKT_DATA_LEN) goto cleanup_and_error;
	if (verify_pattern_data(buf, TEST94F_LARGE_PKT_DATA_LEN) != 0) goto cleanup_and_error;

	memset(buf, 0, current_buf_size);
	if (recv(fd3, buf, current_buf_size, MSG_DONTWAIT) != (ssize_t)TEST94F_LARGE_PKT_DATA_LEN) goto cleanup_and_error;
	if (verify_pattern_data(buf, TEST94F_LARGE_PKT_DATA_LEN) != 0) goto cleanup_and_error;

	if (recv(fd3, buf, current_buf_size, MSG_DONTWAIT) != -1) goto cleanup_and_error;
	if (errno != EWOULDBLOCK) goto cleanup_and_error;

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) goto cleanup_and_error;
	if (bs.bs_capt != 2) goto cleanup_and_error;

	if (check_fd_writable(fd) != 0) goto cleanup_and_error;

	test94_cleanup(fd, fd2, fd3, buf);
    return;

cleanup_and_error:
    test94_cleanup(fd, fd2, fd3, buf);
    e(0);
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
	int error_occurred = 0;

	subtest = 7;

	if ((fd = open(_PATH_BPF, O_RDWR)) < 0) {
		error_occurred = 1;
		goto cleanup;
	}

	if (ioctl(fd, BIOCGBLEN, &size) != 0) {
		error_occurred = 1;
		goto cleanup;
	}
	if (size < 1024 || size > BPF_MAXBUFSIZE) {
		error_occurred = 1;
		goto cleanup;
	}

	buf = malloc(size);
	if (buf == NULL) {
		error_occurred = 1;
		goto cleanup;
	}

	if (read(fd, buf, size) != -1) {
		error_occurred = 1;
		goto cleanup;
	}
	if (errno != EINVAL) {
		error_occurred = 1;
		goto cleanup;
	}

	if (write(fd, buf, size) != -1) {
		error_occurred = 1;
		goto cleanup;
	}
	if (errno != EINVAL) {
		error_occurred = 1;
		goto cleanup;
	}

	FD_ZERO(&rfds);
	FD_SET(fd, &rfds);
	FD_ZERO(&wfds);
	FD_SET(fd, &wfds);

	if (select(fd + 1, &rfds, &wfds, NULL, NULL) != 2) {
		error_occurred = 1;
		goto cleanup;
	}

	if (!FD_ISSET(fd, &rfds)) {
		error_occurred = 1;
		goto cleanup;
	}
	if (!FD_ISSET(fd, &wfds)) {
		error_occurred = 1;
		goto cleanup;
	}

cleanup:
	if (buf != NULL) {
		free(buf);
	}
	if (fd != -1) {
		if (close(fd) != 0) {
			/* If an error occurred earlier, preserve that error.
			 * Otherwise, a close error indicates the failure. */
			if (error_occurred == 0) {
				error_occurred = 1;
			}
		}
	}

	if (error_occurred) {
		e(0);
	}
}

/*
 * Test various IOCTL calls.  Several of these tests are rather superficial,
 * because we would need a real interface, rather than the loopback device, to
 * test their functionality properly.  Also note that we skip various checks
 * performed as part of the earlier subtests.
 */
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <net/if.h>
#include <net/bpf.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>
#include <limits.h>

extern int subtest;
extern void e(int);
extern size_t test94_setup(int *cfd, int *fd2, int *fd3, uint8_t **buf, size_t initial_size, int set_filter);
extern void test94_fill_exact(int fd, uint8_t *buf, size_t size, int seq);
extern void test94_add_random(int fd, uint8_t *buf, size_t size, int seq);
extern void test94_cleanup(int cfd, int fd2, int fd3, uint8_t *buf);

#ifndef _PATH_BPF
#define _PATH_BPF "/dev/bpf"
#endif
#ifndef LOOPBACK_IFNAME
#define LOOPBACK_IFNAME "lo0"
#endif

static void checked_ioctl_success(int fd, unsigned long request, void *arg) {
    if (ioctl(fd, request, arg) != 0) {
        e(0);
    }
}

static void checked_ioctl_expect_failure(int fd, unsigned long request, void *arg, int expected_errno) {
    if (ioctl(fd, request, arg) != -1) {
        e(0);
    }
    if (errno != expected_errno) {
        e(0);
    }
}

static int checked_open_fd(const char *path, int flags) {
    int fd = open(path, flags);
    if (fd < 0) {
        e(0);
    }
    return fd;
}

static void checked_close_fd(int fd) {
    if (close(fd) != 0) {
        e(0);
    }
}

static void test_bpf_buffer_length_setting(int fd, unsigned int test_val, int expect_equal) {
    unsigned int uval = test_val;
    checked_ioctl_success(fd, BIOCSBLEN, &uval);

    checked_ioctl_success(fd, BIOCGBLEN, &uval);
    if (uval < sizeof(struct bpf_hdr) || uval > BPF_MAXBUFSIZE) {
        e(0);
    }
    if (expect_equal && uval != test_val) {
        e(0);
    }
}

static void test_bpf_option_toggle(int fd, unsigned long get_request, unsigned long set_request, unsigned int initial_expect, unsigned int toggle_val, unsigned int toggled_expect) {
    unsigned int uval;

    uval = initial_expect + 1;
    checked_ioctl_success(fd, get_request, &uval);
    if (uval != initial_expect) {
        e(0);
    }

    uval = toggle_val;
    checked_ioctl_success(fd, set_request, &uval);

    uval = initial_expect + 1;
    checked_ioctl_success(fd, get_request, &uval);
    if (uval != toggled_expect) {
        e(0);
    }

    uval = initial_expect;
    checked_ioctl_success(fd, set_request, &uval);

    uval = toggled_expect + 1;
    checked_ioctl_success(fd, get_request, &uval);
    if (uval != initial_expect) {
        e(0);
    }
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
    int cfd = -1, ufd = -1, fd2 = -1, fd3 = -1, val;

    subtest = 8;

    size = test94_setup(&cfd, &fd2, &fd3, &buf, 0 /*size*/, 1 /*set_filter*/);
    ufd = checked_open_fd(_PATH_BPF, O_RDWR);

    test_bpf_buffer_length_setting(ufd, 1, 0);
    test_bpf_buffer_length_setting(ufd, (unsigned int)-1, 0);
    test_bpf_buffer_length_setting(ufd, 0, 0);

    uval = 1024;
    checked_ioctl_success(ufd, BIOCSBLEN, &uval);
    checked_ioctl_success(ufd, BIOCGBLEN, &uval);
    if (uval != 1024) e(0);

    checked_ioctl_expect_failure(cfd, BIOCSBLEN, &uval, EINVAL);

    checked_ioctl_success(cfd, BIOCGBLEN, &uval);
    if (uval != size) e(0);

    uval = 1;
    checked_ioctl_success(cfd, BIOCIMMEDIATE, &uval);

    test94_fill_exact(fd2, buf, size, 1 /*seq*/);
    test94_fill_exact(fd2, buf, size, 1 /*seq*/);
    test94_fill_exact(fd2, buf, size, 1 /*seq*/);

    checked_ioctl_success(cfd, BIOCGSTATS, &bs);
    if (bs.bs_recv == 0 || bs.bs_drop == 0 || bs.bs_capt == 0) e(0);

    checked_ioctl_success(cfd, BIOCGSTATS, &bs);
    if (bs.bs_recv == 0 || bs.bs_drop == 0 || bs.bs_capt == 0) e(0);

    checked_ioctl_success(cfd, FIONREAD, &val);
    if (val == 0) e(0);

    checked_ioctl_success(cfd, BIOCFLUSH, NULL);

    checked_ioctl_success(cfd, BIOCGSTATS, &bs);
    if (bs.bs_drop != 0 || bs.bs_capt != 0) e(0);

    checked_ioctl_success(cfd, FIONREAD, &val);
    if (val != 0) e(0);

    checked_ioctl_success(ufd, BIOCFLUSH, NULL);

    checked_ioctl_success(ufd, BIOCGSTATS, &bs);
    if (bs.bs_recv != 0 || bs.bs_drop != 0 || bs.bs_capt != 0) e(0);

    checked_ioctl_expect_failure(ufd, BIOCPROMISC, NULL, EINVAL);
    checked_ioctl_success(cfd, BIOCPROMISC, NULL);

    checked_ioctl_expect_failure(ufd, BIOCGDLT, &uval, EINVAL);

    checked_ioctl_expect_failure(ufd, BIOCGETIF, &ifr, EINVAL);

    memset(&ifr, 0, sizeof(ifr));
    checked_ioctl_success(cfd, BIOCGETIF, &ifr);
    if (strcmp(ifr.ifr_name, LOOPBACK_IFNAME) != 0) e(0);

    memset(&ifr, 0, sizeof(ifr));
    strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
    checked_ioctl_expect_failure(cfd, BIOCSETIF, &ifr, EINVAL);

    memset(&ifr, 0, sizeof(ifr));
    memset(ifr.ifr_name, 'x', sizeof(ifr.ifr_name));
    checked_ioctl_expect_failure(ufd, BIOCSETIF, &ifr, ENXIO);

    memset(&ifr, 0, sizeof(ifr));
    strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
    ifr.ifr_name[strlen(ifr.ifr_name) - 1] += 9;
    checked_ioctl_expect_failure(ufd, BIOCSETIF, &ifr, ENXIO);

    test94_add_random(fd2, buf, size, 1 /*seq*/);

    checked_ioctl_success(cfd, FIONREAD, &val);
    if (val == 0) e(0);

    uval = 0;
    checked_ioctl_success(cfd, BIOCIMMEDIATE, &uval);

    checked_ioctl_success(cfd, FIONREAD, &val);
    if (val != 0) e(0);

    uval = 1;
    checked_ioctl_success(cfd, BIOCIMMEDIATE, &uval);

    checked_ioctl_success(cfd, FIONREAD, &val);
    if (val == 0) e(0);

    checked_ioctl_success(cfd, BIOCFLUSH, NULL);

    uval = 1;
    checked_ioctl_success(ufd, BIOCIMMEDIATE, &uval);

    uval = 0;
    checked_ioctl_success(ufd, BIOCIMMEDIATE, &uval);

    memset(&bv, 0, sizeof(bv));
    checked_ioctl_success(ufd, BIOCVERSION, &bv);
    if (bv.bv_major != BPF_MAJOR_VERSION || bv.bv_minor != BPF_MINOR_VERSION) e(0);

    test_bpf_option_toggle(ufd, BIOCGHDRCMPLT, BIOCSHDRCMPLT, 0, 2, 1);

    uval = DLT_RAW;
    checked_ioctl_expect_failure(ufd, BIOCSDLT, &uval, EINVAL);

    uval = DLT_RAW;
    checked_ioctl_success(cfd, BIOCSDLT, &uval);

    uval = DLT_NULL;
    checked_ioctl_expect_failure(cfd, BIOCSDLT, &uval, EINVAL);

    checked_ioctl_success(cfd, BIOCGDLT, &uval);
    if (uval != DLT_RAW) e(0);

    memset(&bfl, 0, sizeof(bfl));
    checked_ioctl_expect_failure(ufd, BIOCGDLTLIST, &bfl, EINVAL);

    memset(&bfl, 0, sizeof(bfl));
    checked_ioctl_success(cfd, BIOCGDLTLIST, &bfl);
    if (bfl.bfl_len != 1 || bfl.bfl_list != NULL) e(0);

    memset(&bfl, 0, sizeof(bfl));
    bfl.bfl_len = 2;
    checked_ioctl_success(cfd, BIOCGDLTLIST, &bfl);
    if (bfl.bfl_len != 1 || bfl.bfl_list != NULL) e(0);

    memset(&bfl, 0, sizeof(bfl));
    memset(list, 0, sizeof(list));
    bfl.bfl_list = list;
    checked_ioctl_expect_failure(cfd, BIOCGDLTLIST, &bfl, ENOMEM);
    if (list[0] != 0) e(0);

    memset(&bfl, 0, sizeof(bfl));
    bfl.bfl_len = 1;
    bfl.bfl_list = list;
    checked_ioctl_success(cfd, BIOCGDLTLIST, &bfl);
    if (bfl.bfl_len != 1 || bfl.bfl_list != list || list[0] != DLT_RAW || list[1] != 0) e(0);

    memset(&bfl, 0, sizeof(bfl));
    memset(list, 0, sizeof(list));
    bfl.bfl_len = 2;
    bfl.bfl_list = list;
    checked_ioctl_success(cfd, BIOCGDLTLIST, &bfl);
    if (bfl.bfl_len != 1 || bfl.bfl_list != list || list[0] != DLT_RAW || list[1] != 0) e(0);

    test_bpf_option_toggle(ufd, BIOCGSEESENT, BIOCSSEESENT, 1, 0, 0);

    uval = 1;
    checked_ioctl_success(cfd, BIOCGSEESENT, &uval);
    if (uval != 1) e(0);

    uval = 0;
    checked_ioctl_success(cfd, BIOCSSEESENT, &uval);

    checked_ioctl_success(cfd, BIOCFLUSH, NULL);

    test94_add_random(fd2, buf, size, 1 /*seq*/);

    checked_ioctl_success(cfd, BIOCGSTATS, &bs);
    if (bs.bs_recv != 0) e(0);

    uval = 1;
    checked_ioctl_success(cfd, BIOCSSEESENT, &uval);

    checked_ioctl_success(cfd, BIOCFLUSH, NULL);

    test94_add_random(fd2, buf, size, 1 /*seq*/);

    checked_ioctl_success(cfd, BIOCGSTATS, &bs);
    if (bs.bs_recv == 0) e(0);

    tv.tv_sec = 99; tv.tv_usec = 99;
    checked_ioctl_success(ufd, BIOCGRTIMEOUT, &tv);
    if (tv.tv_sec != 0 || tv.tv_usec != 0) e(0);

    tv.tv_sec = 0; tv.tv_usec = 1000000;
    checked_ioctl_expect_failure(ufd, BIOCSRTIMEOUT, &tv, EINVAL);

    tv.tv_sec = 0; tv.tv_usec = (unsigned int)-1;
    checked_ioctl_expect_failure(ufd, BIOCSRTIMEOUT, &tv, EINVAL);

    tv.tv_sec = (unsigned int)-1; tv.tv_usec = 0;
    checked_ioctl_expect_failure(ufd, BIOCSRTIMEOUT, &tv, EINVAL);

    tv.tv_sec = INT_MAX; tv.tv_usec = 0;
    checked_ioctl_expect_failure(ufd, BIOCSRTIMEOUT, &tv, EDOM);

    checked_ioctl_success(ufd, BIOCGRTIMEOUT, &tv);
    if (tv.tv_sec != 0 || tv.tv_usec != 0) e(0);

    tv.tv_sec = 123; tv.tv_usec = 1;
    checked_ioctl_success(ufd, BIOCSRTIMEOUT, &tv);

    checked_ioctl_success(ufd, BIOCGRTIMEOUT, &tv);
    if (tv.tv_sec != 123 || tv.tv_usec == 0) e(0);

    tv.tv_sec = 0; tv.tv_usec = 0;
    checked_ioctl_success(ufd, BIOCSRTIMEOUT, &tv);

    checked_ioctl_success(ufd, BIOCGRTIMEOUT, &tv);
    if (tv.tv_sec != 0 || tv.tv_usec != 0) e(0);

    test_bpf_option_toggle(ufd, BIOCGFEEDBACK, BIOCSFEEDBACK, 0, 2, 1);

    checked_close_fd(ufd);

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
	struct sockaddr_in6 sin6A = {0};
	struct sockaddr_in6 sin6B = {0};
	struct bpf_program bf = {0};
	struct bpf_stat bs = {0};
	struct bpf_hdr bh = {0};
	struct ifreq ifr = {0};
	struct ip6_hdr ip6;
	struct udphdr uh;
	uint8_t *buf = NULL;
	char c;
	socklen_t socklen;
	ssize_t len;
	size_t off;
	unsigned int uval, size, dlt;
	int fd = -1;
	int fd2 = -1;
	int fd3 = -1;
	int error_occurred = 0;

	subtest = 9;

	if ((fd = open(_PATH_BPF, O_RDWR)) < 0) {
		error_occurred = 1;
		goto cleanup;
	}

	if (ioctl(fd, BIOCGBLEN, &size) != 0) {
		error_occurred = 1;
		goto cleanup;
	}
	if (size < 1024 || size > BPF_MAXBUFSIZE) {
		error_occurred = 1;
		goto cleanup;
	}

	if ((buf = malloc(size)) == NULL) {
		error_occurred = 1;
		goto cleanup;
	}

	bf.bf_len = __arraycount(test94_filter6);
	bf.bf_insns = (struct bpf_insn *)test94_filter6;
	if (ioctl(fd, BIOCSETF, &bf) != 0) {
		error_occurred = 1;
		goto cleanup;
	}

	uval = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &uval) != 0) {
		error_occurred = 1;
		goto cleanup;
	}

	strlcpy(ifr.ifr_name, LOOPBACK_IFNAME, sizeof(ifr.ifr_name));
	if (ioctl(fd, BIOCSETIF, &ifr) != 0) {
		error_occurred = 1;
		goto cleanup;
	}

	if (ioctl(fd, BIOCGDLT, &dlt) != 0) {
		error_occurred = 1;
		goto cleanup;
	}
	if (dlt != DLT_RAW) {
		error_occurred = 1;
		goto cleanup;
	}

	if ((fd2 = socket(AF_INET6, SOCK_DGRAM, 0)) < 0) {
		error_occurred = 1;
		goto cleanup;
	}

	sin6A.sin6_family = AF_INET6;
	sin6A.sin6_port = htons(TEST_PORT_A);
	memcpy(&sin6A.sin6_addr, &in6addr_loopback, sizeof(sin6A.sin6_addr));
	if (bind(fd2, (struct sockaddr *)&sin6A, sizeof(sin6A)) != 0) {
		error_occurred = 1;
		goto cleanup;
	}

	memcpy(&sin6B, &sin6A, sizeof(sin6B));
	sin6B.sin6_port = htons(TEST_PORT_B);
	if (connect(fd2, (struct sockaddr *)&sin6B, sizeof(sin6B)) != 0) {
		error_occurred = 1;
		goto cleanup;
	}

	if ((fd3 = socket(AF_INET6, SOCK_DGRAM, 0)) < 0) {
		error_occurred = 1;
		goto cleanup;
	}

	if (bind(fd3, (struct sockaddr *)&sin6B, sizeof(sin6B)) != 0) {
		error_occurred = 1;
		goto cleanup;
	}

	if (connect(fd3, (struct sockaddr *)&sin6A, sizeof(sin6A)) != 0) {
		error_occurred = 1;
		goto cleanup;
	}

	if (write(fd2, "A", 1) != 1) {
		error_occurred = 1;
		goto cleanup;
	}

	if (read(fd3, &c, 1) != 1) {
		error_occurred = 1;
		goto cleanup;
	}
	if (c != 'A') {
		error_occurred = 1;
		goto cleanup;
	}

	if (write(fd3, "B", 1) != 1) {
		error_occurred = 1;
		goto cleanup;
	}

	if (read(fd2, &c, 1) != 1) {
		error_occurred = 1;
		goto cleanup;
	}
	if (c != 'B') {
		error_occurred = 1;
		goto cleanup;
	}

	if (ioctl(fd, BIOCGSTATS, &bs) != 0) {
		error_occurred = 1;
		goto cleanup;
	}
	if (bs.bs_recv < 2) {
		error_occurred = 1;
		goto cleanup;
	}
	if (bs.bs_capt != 1) {
		error_occurred = 1;
		goto cleanup;
	}
	if (bs.bs_drop != 0) {
		error_occurred = 1;
		goto cleanup;
	}

	memset(buf, 0, size);

	len = read(fd, buf, size);

	if (len != (ssize_t)(BPF_WORDALIGN(sizeof(bh)) +
	    BPF_WORDALIGN(sizeof(ip6) + sizeof(uh) + 1))) {
		error_occurred = 1;
		goto cleanup;
	}

	memcpy(&bh, buf, sizeof(bh));

	if (bh.bh_tstamp.tv_sec == 0 && bh.bh_tstamp.tv_usec == 0) {
		error_occurred = 1;
		goto cleanup;
	}
	if (bh.bh_caplen != sizeof(ip6) + sizeof(uh) + 1) {
		error_occurred = 1;
		goto cleanup;
	}
	if (bh.bh_datalen != bh.bh_caplen) {
		error_occurred = 1;
		goto cleanup;
	}
	if (bh.bh_hdrlen != BPF_WORDALIGN(sizeof(bh))) {
		error_occurred = 1;
		goto cleanup;
	}

	if (buf[bh.bh_hdrlen + sizeof(ip6) + sizeof(uh)] != 'A') {
		error_occurred = 1;
		goto cleanup;
	}

	off = test94_make_pkt(buf, 6, 1);
	memcpy(buf + off, "Hello!", 6);

	if (write(fd, buf, off + 6) != (ssize_t)(off + 6)) {
		error_occurred = 1;
		goto cleanup;
	}

	socklen = sizeof(sin6A);
	if (recvfrom(fd3, buf, size, 0, (struct sockaddr *)&sin6A,
	    &socklen) != 6) {
		error_occurred = 1;
		goto cleanup;
	}

	if (memcmp(buf, "Hello!", 6) != 0) {
		error_occurred = 1;
		goto cleanup;
	}
	if (socklen != sizeof(sin6A)) {
		error_occurred = 1;
		goto cleanup;
	}
	if (sin6A.sin6_family != AF_INET6) {
		error_occurred = 1;
		goto cleanup;
	}
	if (sin6A.sin6_port != htons(TEST_PORT_A)) {
		error_occurred = 1;
		goto cleanup;
	}
	if (memcmp(&sin6A.sin6_addr, &in6addr_loopback,
	    sizeof(sin6A.sin6_addr)) != 0) {
		error_occurred = 1;
		goto cleanup;
	}

cleanup:
	if (buf != NULL) {
		free(buf);
	}

	if (fd3 != -1) {
		if (close(fd3) != 0 && !error_occurred) {
			error_occurred = 1;
		}
	}

	if (fd2 != -1) {
		if (close(fd2) != 0 && !error_occurred) {
			error_occurred = 1;
		}
	}

	if (fd != -1) {
		if (close(fd) != 0 && !error_occurred) {
			error_occurred = 1;
		}
	}

	if (error_occurred) {
		e(0);
	}
}

/*
 * Test the BPF sysctl(7) interface at a basic level.
 */
static int
get_sysctl_int(const char *mib_name, int *val)
{
	int mib[CTL_MAXID];
	size_t len = __arraycount(mib);
	size_t oldlen = sizeof(*val);

	if (sysctlnametomib(mib_name, mib, &len) != 0) e(0);
	if (len != 3) e(0); // Expected MIB length for this type of sysctl

	if (sysctl(mib, len, val, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen != sizeof(*val)) e(0);

	return 0;
}

static int
get_sysctl_struct(const char *mib_name, void *s, size_t size, unsigned int mib_len_expected)
{
	int mib[CTL_MAXID];
	size_t len = __arraycount(mib);
	size_t oldlen = size;

	if (sysctlnametomib(mib_name, mib, &len) != 0) e(0);
	if (len != mib_len_expected) e(0);

	if (sysctl(mib, len, s, &oldlen, NULL, 0) != 0) e(0);
	if (oldlen != size) e(0);

	return 0;
}

static int
construct_bpf_peers_mib(int *mib, size_t *mib_len)
{
	*mib_len = __arraycount(mib);
	if (sysctlnametomib("net.bpf.peers", mib, mib_len) != 0) e(0);
	if (*mib_len != 3) e(0);

	mib[(*mib_len)++] = sizeof(struct bpf_d_ext); /* size of each element */
	mib[(*mib_len)++] = INT_MAX;		   /* limit on elements to return */
	return 0;
}

static int
get_bpf_peers(const int *mib, size_t mib_len, struct bpf_d_ext **bde_buf_ptr,
    unsigned int *bde_count_ptr)
{
	size_t oldlen = 0;
	size_t bdesize;
	struct bpf_d_ext *bde;

	if (sysctl(mib, mib_len, NULL, &oldlen, NULL, 0) != 0) e(0);

	if (oldlen == 0) {
		*bde_buf_ptr = NULL;
		*bde_count_ptr = 0;
		return 0;
	}

	bdesize = oldlen + sizeof(*bde) * 8;
	if ((bde = malloc(bdesize)) == NULL) e(0);

	oldlen = bdesize;
	if (sysctl(mib, mib_len, bde, &oldlen, NULL, 0) != 0) {
		free(bde);
		e(0);
	}
	if (oldlen % sizeof(*bde)) {
		free(bde);
		e(0);
	}

	*bde_buf_ptr = bde;
	*bde_count_ptr = oldlen / sizeof(*bde);
	return 0;
}

static void
validate_configured_bpf_peer(const struct bpf_d_ext *entry, size_t expected_size,
    unsigned int expected_count_unit)
{
	if (entry->bde_pid != getpid()) e(0);
	if (entry->bde_bufsize != expected_size) e(0);
	if (entry->bde_promisc != 0) e(0);
	if (entry->bde_state != BPF_IDLE) e(0);
	if (entry->bde_immediate != 0) e(0);
	if (entry->bde_hdrcmplt != 0) e(0);
	if (entry->bde_seesent != 1) e(0);
	if (entry->bde_rcount < expected_count_unit * 3 + 1) e(0);
	if (entry->bde_dcount != expected_count_unit) e(0);
	if (entry->bde_ccount != expected_count_unit * 3) e(0);
	if (strcmp(entry->bde_ifname, LOOPBACK_IFNAME) != 0) e(0);
}

static void
validate_unconfigured_bpf_peer(const struct bpf_d_ext *entry, size_t expected_size)
{
	if (entry->bde_pid != getpid()) e(0);
	if (entry->bde_bufsize != expected_size) e(0);
	if (entry->bde_promisc != 0) e(0);
	if (entry->bde_state != BPF_IDLE) e(0);
	if (entry->bde_immediate != 1) e(0);
	if (entry->bde_hdrcmplt != 1) e(0);
	if (entry->bde_seesent != 0) e(0);
	if (entry->bde_rcount != 0) e(0);
	if (entry->bde_dcount != 0) e(0);
	if (entry->bde_ccount != 0) e(0);
	if (entry->bde_ifname[0] != '\0') e(0);
}

static void
test94j(void)
{
	struct bpf_stat bs1, bs2;
	struct bpf_d_ext *bde = NULL;
	uint8_t *buf = NULL;
	unsigned int slot, count_unit, uval;
	size_t len_mib_peers;
	int fd = -1, fd2 = -1, fd3 = -1, max_buf_val;
	int mib_peers[CTL_MAXID];

	subtest = 10;

	/*
	 * Obtain and validate the maximum buffer size.
	 */
	if (get_sysctl_int("net.bpf.maxbufsize", &max_buf_val) != 0) e(0);
	if (max_buf_val < 1024 || max_buf_val > INT_MAX / 2) e(0);

	/*
	 * Attempt to set the maximum buffer size (expect EPERM).
	 */
	int mib_maxbuf[CTL_MAXID];
	size_t len_mib_maxbuf = __arraycount(mib_maxbuf);
	if (sysctlnametomib("net.bpf.maxbufsize", mib_maxbuf, &len_mib_maxbuf) != 0) e(0);
	if (len_mib_maxbuf != 3) e(0);
	int set_val = max_buf_val;
	if (sysctl(mib_maxbuf, len_mib_maxbuf, NULL, NULL, &set_val, sizeof(set_val)) != -1) e(0);
	if (errno != EPERM) e(0);

	/*
	 * Obtain initial global BPF statistics.
	 */
	if (get_sysctl_struct("net.bpf.stats", &bs1, sizeof(bs1), 3) != 0) e(0);

	/*
	 * Set up a BPF descriptor, generate traffic, and obtain BPF peer info.
	 */
	if (construct_bpf_peers_mib(mib_peers, &len_mib_peers) != 0) e(0);

	size_t buffer_size_setup = test94_setup(&fd, &fd2, &fd3, &buf, 0 /*size*/, 1 /*set_filter*/);
	if (fd < 0 || fd2 < 0 || fd3 < 0 || buf == NULL) e(0);

	count_unit = test94_fill_exact(fd2, buf, buffer_size_setup, 0);
	test94_fill_exact(fd2, buf, buffer_size_setup, 0);
	test94_fill_exact(fd2, buf, buffer_size_setup, 0);

	if (write(fd3, "X", 1) != 1) e(0);

	/*
	 * Retrieve and validate the BPF peer list for the configured descriptor.
	 */
	unsigned int bde_count = 0;
	if (get_bpf_peers(mib_peers, len_mib_peers, &bde, &bde_count) != 0) e(0);

	int found_peer_configured = 0;
	for (slot = 0; slot < bde_count; slot++) {
		if (bde[slot].bde_pid != getpid()) continue;

		validate_configured_bpf_peer(&bde[slot], buffer_size_setup, count_unit);
		found_peer_configured++;
	}
	if (found_peer_configured != 1) e(0);

	/*
	 * Flush the BPF device and cleanup resources.
	 */
	if (ioctl(fd, BIOCFLUSH) != 0) e(0);
	test94_cleanup(fd, fd2, fd3, buf);
	fd = fd2 = fd3 = -1;
	buf = NULL;

	/*
	 * Validate global statistics after traffic generation and cleanup.
	 */
	if (get_sysctl_struct("net.bpf.stats", &bs2, sizeof(bs2), 3) != 0) e(0);

	if (bs2.bs_recv < bs1.bs_recv + count_unit * 3 + 1) e(0);
	if (bs2.bs_drop != bs1.bs_drop + count_unit) e(0);
	if (bs2.bs_capt != bs1.bs_capt + count_unit * 3) e(0);

	/*
	 * Check an unconfigured BPF device and toggle its flags.
	 */
	if ((fd = open(_PATH_BPF, O_RDWR)) < 0) e(0);

	uval = 1;
	if (ioctl(fd, BIOCIMMEDIATE, &uval) != 0) e(0);
	if (ioctl(fd, BIOCSHDRCMPLT, &uval) != 0) e(0);

	uval = 0;
	if (ioctl(fd, BIOCSSEESENT, &uval) != 0) e(0);

	/*
	 * Retrieve and validate the BPF peer list for the unconfigured descriptor.
	 */
	free(bde); bde = NULL; bde_count = 0; // Ensure fresh buffer allocation for this call
	if (get_bpf_peers(mib_peers, len_mib_peers, &bde, &bde_count) != 0) e(0);

	int found_peer_unconfigured = 0;
	for (slot = 0; slot < bde_count; slot++) {
		if (bde[slot].bde_pid != getpid()) continue;

		validate_unconfigured_bpf_peer(&bde[slot], buffer_size_setup);
		found_peer_unconfigured++;
	}
	if (found_peer_unconfigured != 1) e(0);

	if (close(fd) != 0) e(0);
	fd = -1;

	/*
	 * Verify that no BPF device is left for our PID after closing the device.
	 */
	free(bde); bde = NULL; bde_count = 0; // Ensure fresh buffer allocation for this call
	if (get_bpf_peers(mib_peers, len_mib_peers, &bde, &bde_count) != 0) e(0);

	for (slot = 0; slot < bde_count; slot++) {
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
	struct passwd *pw;
	pid_t pid;
	size_t len, oldlen;
	int mib[5], status;

	subtest = 11;

	pid = fork();
	if (pid == -1) {
		e(0);
	} else if (pid == 0) {
		errct = 0;

		if ((pw = getpwnam(NONROOT_USER)) == NULL) e(0);

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
	} else {
		if (wait(&status) != pid) e(0);
		if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) e(0);
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
static int
send_bpf_packet_and_verify(int bfd, const struct ether_header *base_ether_hdr,
    sa_family_t family, in_port_t port, const void *bind_addr_base, socklen_t bind_addr_len,
    int is_ipv6)
{
	uint8_t buf[sizeof(struct ether_header) + MAX(sizeof(struct ip),
	    sizeof(struct ip6_hdr)) + sizeof(struct udphdr) + 6];
	struct ether_header ether_copy;
	struct sockaddr_storage ss;
	int sfd = -1;
	size_t off;
	int ret = -1;

	memcpy(&ether_copy, base_ether_hdr, sizeof(ether_copy));
	ether_copy.ether_type = htons(is_ipv6 ? ETHERTYPE_IPV6 : ETHERTYPE_IP);

	if ((sfd = socket(family, SOCK_DGRAM, 0)) < 0) {
		goto fail;
	}

	if (bind_addr_len > sizeof(ss)) {
		goto fail;
	}
	memcpy(&ss, bind_addr_base, bind_addr_len);

	if (family == AF_INET) {
		((struct sockaddr_in *)&ss)->sin_port = port;
	} else {
		((struct sockaddr_in6 *)&ss)->sin6_port = port;
	}

	if (bind(sfd, (struct sockaddr *)&ss, bind_addr_len) != 0) {
		goto fail;
	}

	memcpy(buf, &ether_copy, sizeof(ether_copy));
	off = sizeof(ether_copy);
	off += test94_make_pkt(buf + off, 6, is_ipv6);
	if (off + 6 > sizeof(buf)) {
		goto fail;
	}
	memcpy(buf + off, "Hello!", 6);

	if (write(bfd, buf, off + 6) != (ssize_t)(off + 6)) {
		goto fail;
	}

	if (recv(sfd, buf, sizeof(buf), MSG_DONTWAIT) != -1) {
		goto fail;
	}
	if (errno != EWOULDBLOCK) {
		goto fail;
	}

	ret = 0;
fail:
	if (sfd != -1) {
		if (close(sfd) != 0 && ret == 0) {
			ret = -1;
		}
	}
	return ret;
}

static void
test94l(void)
{
	struct ifreq ifr;
	struct ifaddrs *ifa = NULL;
	struct ether_header ether;
	const uint8_t ether_src[ETHER_ADDR_LEN] =
	    { 0x02, 0x00, 0x01, 0x12, 0x34, 0x56 };
	int bfd = -1;
	int test_failed = 0;

	subtest = 12;

	if (!get_setting_use_network())
		return;

	memset(&ifr, 0, sizeof(ifr));
	memset(&ether, 0, sizeof(ether));

	if (getifaddrs(&ifa) != 0) {
		test_failed = 1;
		goto fail;
	}

	struct ifaddrs *ifp_found = NULL;
	for (struct ifaddrs *ifp = ifa; ifp != NULL; ifp = ifp->ifa_next) {
		if (!(ifp->ifa_flags & IFF_UP) || ifp->ifa_addr == NULL ||
		    ifp->ifa_addr->sa_family != AF_LINK)
			continue;

		struct if_data *ifdata = (struct if_data *)ifp->ifa_data;
		if (ifdata != NULL && ifdata->ifi_type == IFT_ETHER &&
		    ifdata->ifi_link_state != LINK_STATE_DOWN) {
			strlcpy(ifr.ifr_name, ifp->ifa_name,
			    sizeof(ifr.ifr_name));

			struct sockaddr_dl *link_addr = (struct sockaddr_dl *)ifp->ifa_addr;
			if (link_addr->sdl_alen != sizeof(ether.ether_dhost)) {
				test_failed = 1;
				goto fail;
			}
			memcpy(ether.ether_dhost,
			    link_addr->sdl_data + link_addr->sdl_nlen,
			    link_addr->sdl_alen);
			ifp_found = ifp;
			break;
		}
	}

	if (ifp_found == NULL) {
		goto fail;
	}

	if ((bfd = open(_PATH_BPF, O_RDWR)) < 0) {
		test_failed = 1;
		goto fail;
	}

	if (ioctl(bfd, BIOCSETIF, &ifr) != 0) {
		test_failed = 1;
		goto fail;
	}

	unsigned int val;
	if (ioctl(bfd, BIOCGDLT, &val) != 0) {
		test_failed = 1;
		goto fail;
	}
	if (val != DLT_EN10MB) {
		test_failed = 1;
		goto fail;
	}

	val = 1;
	if (ioctl(bfd, BIOCSFEEDBACK, &val) != 0) {
		test_failed = 1;
		goto fail;
	}

	memcpy(ether.ether_shost, ether_src, sizeof(ether.ether_shost));

	struct sockaddr_in sin_bind;
	memset(&sin_bind, 0, sizeof(sin_bind));
	sin_bind.sin_family = AF_INET;
	sin_bind.sin_addr.s_addr = htonl(INADDR_LOOPBACK);

	if (send_bpf_packet_and_verify(bfd, &ether, AF_INET,
	    htons(TEST_PORT_B), &sin_bind, sizeof(sin_bind), 0) != 0) {
		test_failed = 1;
		goto fail;
	}

	struct sockaddr_in6 sin6_bind;
	memset(&sin6_bind, 0, sizeof(sin6_bind));
	sin6_bind.sin6_family = AF_INET6;
	memcpy(&sin6_bind.sin6_addr, &in6addr_loopback,
	    sizeof(sin6_bind.sin6_addr));

	if (send_bpf_packet_and_verify(bfd, &ether, AF_INET6,
	    htons(TEST_PORT_B), &sin6_bind, sizeof(sin6_bind), 1) != 0) {
		test_failed = 1;
		goto fail;
	}

fail:
	if (bfd != -1) {
		if (close(bfd) != 0 && test_failed == 0) {
			test_failed = 1;
		}
	}
	if (ifa != NULL) {
		freeifaddrs(ifa);
	}
	if (test_failed) e(0);
}

/*
 * Test program for LWIP BPF.
 */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

void start(int);
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

#define DEFAULT_TEST_MASK 0xFFF
#define MAX_TEST_FUNCTIONS 12

typedef void (*test_func_ptr)(void);

static const test_func_ptr test_functions[MAX_TEST_FUNCTIONS] = {
    test94a, test94b, test94c, test94d, test94e, test94f,
    test94g, test94h, test94i, test94j, test94k, test94l
};

int
main(int argc, char ** argv)
{
    long m;
    int i;
    char *endptr;

    start(94);

    srand48((long)time(NULL));

    if (argc > 2) {
        fprintf(stderr, "Usage: %s [mask_value]\n", argv[0]);
        exit(EXIT_FAILURE);
    } else if (argc == 2) {
        m = strtol(argv[1], &endptr, 0);

        if (endptr == argv[1] || *endptr != '\0') {
            fprintf(stderr, "Error: Invalid mask value '%s'.\n", argv[1]);
            exit(EXIT_FAILURE);
        }
        if (m < 0) {
            fprintf(stderr, "Error: Mask value must be non-negative.\n");
            exit(EXIT_FAILURE);
        }
    } else {
        m = DEFAULT_TEST_MASK;
    }

    for (i = 0; i < ITERATIONS; i++) {
        for (int j = 0; j < MAX_TEST_FUNCTIONS; j++) {
            if (((unsigned long)m >> j) & 1) {
                test_functions[j]();
            }
        }
    }

    quit();
    return 0;
}
