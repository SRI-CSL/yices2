/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * File reader: keeps track of filename, position, current character.
 * String reader: same thing but reads from a null-terminated string.
 */

#if 0
#define _GNU_SOURCE
#include <wchar.h>
#endif

#include <stdbool.h>
#include <assert.h>

#include "io/reader.h"



/*
 * It seems that we need an explicit declaration of getc_unlocked on
 * Solaris (to avoid a compilation warning). Not sure whether this
 * is required on all Solaris versions?
 */
#if defined(SOLARIS)
extern int getc_unlocked(FILE *);
#endif


/*
 * Read and return the next char from a stream reader
 * - update pos, line, column
 */
static int file_reader_next_char(reader_t *reader) {
  assert(reader->is_stream);

  if (reader->current == EOF) {
    return EOF;
  }

  if (reader->current == '\n') {
    reader->line ++;
    reader->column = 0;
  }

  // getc_unlocked is unsafe in multithreading applications
  // but it's much faster.
#if defined(MINGW)
  reader->current = getc(reader->input.stream);
#else
  reader->current = getc_unlocked(reader->input.stream);
#endif
  reader->pos ++;
  reader->column ++;

  return reader->current;
}



/*
 * Read and return the next char from a string reader
 * - update pos, line, column
 */
static int string_reader_next_char(reader_t *reader) {
  char c;

  assert(! reader->is_stream);

  if (reader->current == EOF) {
    return EOF;
  }

  if (reader->current == '\n') {
    reader->line ++;
    reader->column = 0;
  }

  c = reader->input.data[reader->pos];
  reader->current = c;
  if (c == '\0') {
    reader->current = EOF;
  }
  reader->pos ++;
  reader->column ++;

  return reader->current;
}





/*
 * Initialize reader for file of the given name
 * - return -1 if the file could not be open
 *   or 0 otherwise
 * - if the file can't be opened, current is set to EOF,
 *   any subsequent attempt to read will return EOF
 * - if the file can be opened, current is set to '\n'
 */
int32_t init_file_reader(reader_t *reader, const char *filename) {
  FILE *f;

  f = fopen(filename, "r");
  reader->input.stream = f; // keep it NULL if there's an error
  reader->pos = 0;
  reader->line = 0;
  reader->column = 1;
  reader->is_stream = true;
  reader->read = file_reader_next_char;
  reader->name = filename;

  if (f == NULL) {
    reader->current = EOF;
    return -1;
  }

  reader->current = '\n';
  return 0;
}

/*
 * Initialize reader for an already opened stream
 * - set filename to name
 */
void init_stream_reader(reader_t *reader, FILE *f, const char *name) {
  reader->current = '\n';
  reader->input.stream = f;
  reader->pos = 0;
  reader->line = 0;
  reader->column = 1;
  reader->is_stream = true;
  reader->read = file_reader_next_char;
  reader->name = name;
}


/*
 * Initialize reader for string data
 */
void init_string_reader(reader_t *reader, const char *data, const char *name) {
  reader->current = '\n';
  reader->input.data = data;
  reader->pos = 0;
  reader->line = 0;
  reader->column = 1;
  reader->is_stream = false;
  reader->read = string_reader_next_char;
  reader->name = name;
}


/*
 * Reset: change the input string
 */
void reset_string_reader(reader_t *reader, const char *data) {
  assert(! reader->is_stream);
  assert(reader->read == string_reader_next_char);

  reader->current = '\n';
  reader->input.data = data;
  reader->pos = 0;
  reader->line = 0;
  reader->column = 1;
}



/*
 * Close reader: return EOF on error, 0 otherwise
 */
int close_reader(reader_t *reader) {
  if (reader->is_stream) {
    return fclose(reader->input.stream);
  } else {
    return 0;
  }
}


#if 0
/*
 * Experimental variant: use wide characters
 * (we assume UTF-8 encoding)
 *
 * We assume that int is large enough to store any character.
 * To do this properly, we should use wint_t.
 */
static int file_reader_next_wchar(reader_t *reader) {
  wint_t c;

  assert(reader->is_stream);

  if (reader->current == EOF) {
    return EOF;
  }

  if (reader->current == '\n') { // this should works in UTF-8?
    reader->line ++;
    reader->column ++;
  }

#if defined(LINUX)
  c = fgetwc_unlocked(reader->input.stream);
#else
  c = fgetwc(reader->input.stream);
#endif

  if (c == WEOF) {
    reader->current = EOF;
  } else {
    reader->current = c;
    reader->pos ++;
    reader->column += wcwidth(c);
  }

  return c;
}


/*
 * Experimental: try to support wide chararcters (UTF-8)
 */
int32_t init_wide_file_reader(reader_t *reader, const char *filename) {
    FILE *f;

  f = fopen(filename, "r");
  reader->input.stream = f; // keep it NULL if there's an error
  reader->pos = 0;
  reader->line = 0;
  reader->column = 1;
  reader->is_stream = true;
  reader->read = file_reader_next_wchar;
  reader->name = filename;

  if (f == NULL) {
    reader->current = EOF;
    return -1;
  }

  reader->current = '\n';
  return 0;
}

void init_wide_stream_reader(reader_t *reader, FILE *f, const char *name) {
  reader->current = '\n';
  reader->input.stream = f;
  reader->pos = 0;
  reader->line = 0;
  reader->column = 1;
  reader->is_stream = true;
  reader->read = file_reader_next_wchar;
  reader->name = name;
}

#endif
