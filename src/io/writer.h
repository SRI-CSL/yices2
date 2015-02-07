/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Writer: wrapper that provides functions to write either to a FILE or to a string buffer.
 * We currently support only putc, puts, and flush
 */

#ifndef __WRITER_H
#define __WRITER_H

#include <stdio.h>
#include <stdbool.h>

#include "utils/string_buffers.h"

/*
 * Data structure:
 * - output = either a FILE or a string buffer
 * - is_stream: true for FILE/false for string buffers
 * - print_failed: true after an error
 * - print_errno = errno when the error was detected
 */
typedef struct writer_s {
  union {
    FILE *stream;
    string_buffer_t buffer;
  } output;
  bool is_stream;
  bool print_failed;
  int print_errno;
} writer_t;



/*
 * Initialize for the given filename
 * - tries to open the file with mode "w"
 * - returns -1 if the file can't be opened.
 *   set print_failed to true and store the errno
 * - returns 0 otherwise (print_failed is false and errno is 0)
 */
extern int32_t init_file_writer(writer_t *writer, const char *filename);

/*
 * Initialize with an open stream f
 * - f must be open and writable
 */
extern void init_stream_writer(writer_t *writer, FILE *f);

/*
 * Initialize for standard output or standard error
 */
static inline void init_stdout_writer(writer_t *writer) {
  init_stream_writer(writer, stdout);
}

static inline void init_stderr_writer(writer_t *writer) {
  init_stream_writer(writer, stderr);
}

/*
 * Initialize for a string buffer
 */
extern void init_string_writer(writer_t *writer);


/*
 * Close:
 * - for a stream writer: close the stream
 * - for a string writer: append '\0' to the buffer
 * return code = EOF if fclose fails, 0 otherwise
 */
extern int close_writer(writer_t *writer);


/*
 * Check the type of writer
 */
static inline bool is_stream_writer(writer_t *writer) {
  return writer->is_stream;
}

static inline bool is_string_writer(writer_t *writer) {
  return !writer->is_stream;
}

/*
 * Extract the string constructed by writer
 * - this must be a string writer
 * - the returned string is  '\0'-terminated
 * - its length is returned in *len
 *
 * The returned string must be freed when no-longer needed (by a call
 * to safe_free in utils/memalloc.h).
 */
extern char *writer_get_string(writer_t *writer, uint32_t *len);


/*
 * Delete:
 * - delete the buffer (do nothing if this is a stream writer)
 */
extern void delete_writer(writer_t *writer);



/*
 * Print a character, a string, flush
 * - if writer->print_failed is true, these functions do nothing and exit
 * - otherwise, they perform the IO operation. If this fails, writer->print_failed
 *   is set to true and errno is stored in writer->print_errno.
 */
extern void writer_putc(writer_t *writer, char c);
extern void writer_puts(writer_t *writer, const char *s);
extern void writer_flush(writer_t *writer);


/*
 * Check error flag + errno
 */
static inline bool writer_failed(writer_t *writer) {
  return writer->print_failed;
}

static inline int writer_errno(writer_t *writer) {
  return writer->print_errno;
}


#endif /* __WRITER_H */
