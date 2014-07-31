/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Generic lexer operations.
 *
 * The same data structure is used for both the SMT-LIB and Yices languages.
 *
 * To support nested (include "file"), lexers can be organized into a stack
 * (implemented as a list of lexer_t objects).
 */

#ifndef __LEXER_H
#define __LEXER_H

#include <stdint.h>
#include <stdio.h>

#include "io/reader.h"
#include "utils/string_buffers.h"


// token type
typedef int32_t token_t;


/*
 * The current token type is in lexer->token
 * For string, numbers, symbol tokens, etc.,
 * the value is in buffer (as a null-terminated string)
 *
 * The position of the start of the token is
 * stored as pos, line, column (same interpretation as in reader)
 * The reader is one-character ahead of the token so its position
 * is the last character of token + 1.
 *
 * String buffer is shared by all lexers in the stack.
 * Keywords is a hash table for storing the keywords. (Removed,
 * we now use a perfect hash table, generated using gperf).
 */
typedef struct lexer_s lexer_t;

struct lexer_s {
  token_t token;
  uint64_t tk_pos;
  uint32_t tk_line, tk_column;
  reader_t reader;
  string_buffer_t *buffer;
  lexer_t *next;  // next in list = predecessor on lexer stack
};


/*
 * Keyword table = table of pairs string, token_type
 * - must be terminated by a record with word = NULL
 */
typedef struct keyword_s {
  char *word;
  token_t tk;
} keyword_t;


/*
 * Initialize a lexer for the given filename
 *
 * Return -1 if the file can't be opened, 0 otherwise.
 * (lex cannot be used if the result is -1)
 *
 * If result = 0,
 * - string buffer is allocated,
 * - the reader is initialized
 * - token is set to -1
 */
extern int32_t init_file_lexer(lexer_t *lex, const char *filename);

/*
 * Variant: initialize from an open stream
 */
extern void init_stream_lexer(lexer_t *lex, FILE *f,  const char *name);

/*
 * Use stdin
 */
static inline void init_stdin_lexer(lexer_t *lex) {
  init_stream_lexer(lex, stdin, "stdin");
}


#if 0
/*
 * HACK/EXPERIMENT: use UTF-8 encoded input
 */
extern int32_t init_wide_file_lexer(lexer_t *lex, const char *filename);
extern void init_wide_stream_lexer(lexer_t *lex, FILE *f, const char *name);

#endif

/*
 * Read from a string
 */
extern void init_string_lexer(lexer_t *lex, const char *data, const char *name);


/*
 * Change input string of lex to data
 * - the current lexer name is kept
 * - lex must be a string lexer (initialized with init_string_lexer).
 */
extern void reset_string_lexer(lexer_t *lex, const char *data);


/*
 * Open a nested lexer for the given filename
 * - keywords and buffer are inherited form parent
 * - lex->next is set to parent.
 *
 * Return a negative number if the file can't be opened
 * Return 0 otherwise.
 */
extern int32_t init_nested_lexer(lexer_t *lex, const char *filename, lexer_t *parent);


/*
 * Open a nested lexer for the data string
 */
extern void init_nested_string_lexer(lexer_t *lex, const char *data, const char *name, lexer_t *parent);


/*
 * Close lex:
 * - if lex is attached to a file (or stream) then that file is closed
 * - if lex->next == NULL, delete the internal buffer.
 * return code: EOF if there's an error in closing the file, 0 otherwise.
 */
extern int close_lexer(lexer_t *lex);



/*
 * Variant: close lex but not the file/stream attached if any.
 * - this allows us to attach a lexer to stdin, then close it
 *   without closing stdin.
 * - if lex->next is NULL (toplevel lexer), delete the internal buffer.
 */
extern void close_lexer_only(lexer_t *lex);


/*
 * Flush the lexer (i.e., read until the end of the line or EOF)
 */
extern void flush_lexer(lexer_t *lex);


/*
 * Current token
 */
static inline token_t current_token(lexer_t *lex) {
  return lex->token;
}

static inline uint64_t current_token_pos(lexer_t *lex) {
  return lex->tk_pos;
}

static inline uint32_t current_token_line(lexer_t *lex) {
  return lex->tk_line;
}

static inline uint32_t current_token_column(lexer_t *lex) {
  return lex->tk_column;
}

/*
 * Null-terminated value of the token (provided the lexing
 * function works properly).
 *
 * Warning: lexer operations overwrite the value.
 */
static inline char *current_token_value(lexer_t *lex) {
  return lex->buffer->data;
}

static inline uint32_t current_token_length(lexer_t *lex) {
  return string_buffer_length(lex->buffer);
}


#endif /* __LEXER_H */
