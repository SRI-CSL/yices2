/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>
#include <errno.h>

#include "writer.h"

/*
 * Initialize for the given filename
 * - tries to open the file with mode "w"
 * - returns -1 if the file can't be opened.
 *   set print_failed to true and store the errno
 * - returns 0 otherwise (print_failed is false and errno is 0)
 */
int32_t init_file_writer(writer_t *writer, const char *filename) {
  FILE *f;
  int32_t code;

  f = fopen(filename, "w");
  writer->output.stream = f;
  writer->is_stream = true;  
  if (f == NULL) {
    writer->print_failed = true;    
    writer->print_errno = errno;
    code = -1;
  } else {
    writer->print_failed = false;
    writer->print_errno = 0;
    code = 0;
  }

  return code;
}


/*
 * Initialize with an open stream f
 * - f must be open and writable
 */
void init_stream_writer(writer_t *writer, FILE *f) {
  writer->output.stream = f;
  writer->is_stream = true;
  writer->print_failed = false;
  writer->print_errno = 0;
}


/*
 * Initialize for a string buffer
 */
void init_string_writer(writer_t *writer) {
  init_string_buffer(&writer->output.buffer, 1024);
  writer->is_stream = false;
  writer->print_failed = false;
  writer->print_errno = 0;
}



/*
 * Close:
 * - for a stream writer: close the stream
 * - for a string writer: add a '\0' at the end of the string buffer
 * return code = EOF if fclose fails, 0 otherwise
 */
int close_writer(writer_t *writer) {
  int code;

  if (writer->is_stream) {
    // try to close even if writer->print_failed is true
    // update the flags if  fclose fails
    code = fclose(writer->output.stream);
    if (code == EOF && !writer->print_failed) {
      writer->print_failed = true;
      writer->print_errno = errno;
    }
  } else {
    string_buffer_close(&writer->output.buffer);
    code = 0;
  }

  return code;
}


/*
 * Extract the string constructed by writer
 * - this must be a string writer
 * - function close_writer must be called first
 * - the returned string is  '\0' terminated
 * - the length of the string is returned in *len
 *
 * The returned string must be freed when no-longer needed (by a call
 * to safe_free in utils/memalloc.h).
 */
char *writer_get_string(writer_t *writer, uint32_t *len) {
  assert(!writer->is_stream);
  return string_buffer_export(&writer->output.buffer, len);
}



/*
 * Delete: free the buffer if any otherwise do nothing
 */
void delete_writer(writer_t *writer) {
  if (!writer->is_stream) {
    delete_string_buffer(&writer->output.buffer);
  }
}

/*
 * Print a character, a string, flush
 * - if writer->print_failed is true, these functions do nothing and exit
 * - otherwise, they perform the IO operation. If this fails, writer->print_failed
 *   is set to true and errno is stored in writer->print_errno.
 */
void writer_putc(writer_t *writer, char c) {
  int x;

  if (writer->is_stream) {
    if (!writer->print_failed) {
      x = fputc(c, writer->output.stream);
      if (x == EOF) {
	writer->print_failed = true;
	writer->print_errno = errno;
      }
    }
  } else {
    string_buffer_append_char(&writer->output.buffer, c);
  }
}

void writer_puts(writer_t *writer, const char *s) {
  int x;

  if (writer->is_stream) {
    if (!writer->print_failed) {
      x = fputs(s, writer->output.stream);
      if (x == EOF) {
	writer->print_failed = true;
	writer->print_errno = errno;      
      }
    }
  } else {
    string_buffer_append_string(&writer->output.buffer, s);
  }
}

void writer_flush(writer_t *writer) {
  int x;

  if (writer->is_stream) {
    if (!writer->print_failed) {
      x = fflush(writer->output.stream);
      if (x == EOF) {
	writer->print_failed = true;
	writer->print_errno = errno;
      }
    }
  }
}


