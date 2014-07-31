/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * File reader: keeps track of filename, position, and current character.
 * String reader: same thing but read from a null-terminated string.
 */

#ifndef __FILE_READER_H
#define __FILE_READER_H

#include <stdint.h>
#include <stdio.h>


/*
 * - current = current character
 * - pos, line, column = position in input stream
 * - for file reader, stream = input
 *   for string reader, data = null terminated string.
 * - name = filename or whatever else is given at initialization.
 * - read = read function: get next character
 *   return EOF on last character
 */
typedef struct reader_s reader_t;

typedef int (*read_fun_t)(reader_t *reader);

struct reader_s {
  int current;
  uint64_t pos;
  uint32_t line;
  uint32_t column;
  read_fun_t read;
  int32_t is_stream; // true for stream, false for string readers
  union {
    FILE *stream;
    const char *data;
  } input;
  const char *name;
};


/*
 * Initializations:
 * - before anything is read,
 *    current_char is set to '\n' (or to EOF if fopen fails)
 *    pos is 0
 *    line is 0
 *    column is 1
 *
 * - first real character read has
 *    pos = 1
 *    line = 1
 *    column = 1
 *
 * - line, column, and position stop being updated
 *   when EOF is reached.
 */

/*
 * Initialize reader for file of the given name
 * - return -1 if the file could not be open
 *   or 0 otherwise
 * - if the file was not open, any subsequent attempt
 *   to read will return EOF
 */
extern int32_t init_file_reader(reader_t *reader, const char *filename);

/*
 * Initialize reader for an already opened stream
 * - set filename to whatever is given as name
 */
extern void init_stream_reader(reader_t *reader, FILE *f, const char *name);

/*
 * Initialize reader for standard input
 */
static inline void init_stdin_reader(reader_t *reader) {
  init_stream_reader(reader, stdin, "stdin");
}

/*
 * Initialize reader for string data
 */
extern void init_string_reader(reader_t *reader, const char *data, const char *name);


#if 0
/*
 * Experimental hack: attempt to support UTF-8 input
 */
extern int32_t init_wide_file_reader(reader_t *reader, const char *filename);

extern void init_wide_stream_reader(reader_t *reader, FILE *f, const char *name);

static inline void init_wide_stdin_reader(reader_t *reader) {
  init_wide_stream_reader(reader, stdin, "stdin");
}

#endif


/*
 * Change the input string of reader
 * - reset position/line/col and current
 * - reader must be a string reader.
 */
extern void reset_string_reader(reader_t *reader, const char *data);


/*
 * Close file reader:
 * - return EOF on error, 0 otherwise
 * - no effect if reader is a string reader.
 */
extern int close_reader(reader_t *reader);


/*
 * Get current character, position, line or column numbers
 */
static inline int reader_current_char(reader_t *reader) {
  return reader->current;
}

static inline uint32_t reader_line(reader_t *reader) {
  return reader->line;
}

static inline uint32_t reader_column(reader_t *reader) {
  return reader->column;
}

static inline uint64_t reader_position(reader_t *reader) {
  return reader->pos;
}


/*
 * Read one character, update position data and return the new
 * character.
 */
static inline int reader_next_char(reader_t *reader) {
  return reader->read(reader);
}


#endif /* __FILE_READER_H */
