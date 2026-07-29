/*
 * yulc.h - C interface to the verified Yul -> EVM compiler.
 *
 * Compiles a complete Yul source program (block- or object-rooted, the same
 * input the `yulc` CLI accepts) to executable EVM bytecode. Object-rooted
 * programs produce the recursively laid-out creation bytecode with child
 * objects and data segments resolved, so solc's --ir output can be fed in
 * directly in place of solc's own Yul backend.
 *
 * Thread model: yulc_init() is idempotent and thread-safe. Each
 * yulc_compile() call runs the compiler on a dedicated worker thread with a
 * large stack (compiling large real-world contracts recurses deeply; the
 * in-repo native tools run under `ulimit -s unlimited` for the same reason).
 * The default worker stack is 1 GiB of reserved (lazily committed) address
 * space; set the YULC_STACK_BYTES environment variable to override.
 * Concurrent yulc_compile() calls from different threads are safe.
 */
#ifndef YULC_H
#define YULC_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Status codes, matching the yulc CLI exit codes. */
#define YULC_OK 0
/* The source is not a valid Yul program. */
#define YULC_ERROR_PARSE 1
/* The source parsed, but uses features outside the verified compiler's
 * supported fragment (compilation is Option-valued by design; unsupported
 * or unproved behavior is rejected rather than miscompiled). */
#define YULC_ERROR_UNSUPPORTED 2
/* Lean runtime initialization or worker-thread creation failed, or an
 * argument was NULL / not valid UTF-8. */
#define YULC_ERROR_INTERNAL 3

/*
 * Initialize the Lean runtime and the compiler modules. Safe to call from
 * any thread, any number of times; only the first call does work. Returns
 * YULC_OK or YULC_ERROR_INTERNAL. Calling this explicitly is optional:
 * yulc_compile() initializes on first use.
 */
int yulc_init(void);

/*
 * Compile the NUL-terminated UTF-8 Yul source `source` to EVM bytecode.
 *
 * On success returns YULC_OK and stores a malloc'd buffer of `*bytecode_len`
 * bytes in `*bytecode`; the caller releases it with yulc_free(). On failure
 * returns one of the YULC_ERROR_* codes and leaves `*bytecode` NULL and
 * `*bytecode_len` 0. An empty (zero-length) bytecode result is legal and
 * still yields a non-NULL buffer.
 */
int yulc_compile(const char *source, uint8_t **bytecode, size_t *bytecode_len);

/* Release a buffer returned by yulc_compile(). NULL is a no-op. */
void yulc_free(uint8_t *bytecode);

/* Human-readable description of a yulc status code (static storage). */
const char *yulc_status_string(int status);

#ifdef __cplusplus
}
#endif

#endif /* YULC_H */
