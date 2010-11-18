/*
 * Generic lexer operations.
 *
 * The same data structure is used for both SMTLIB and the Yices language.
 * To support nested (include "file"), lexers can be organized into a stack
 * (implemented as a list of lexer_t objects).
 */

#include <assert.h>

#include "lexer.h"
#include "memalloc.h"


/*
 * Allocate and initialize buffer
 * set default values for token, tk_pos etc.
 */
static void init_lexer(lexer_t *lex) {
  lex->token = -1;
  lex->tk_pos = 0;
  lex->tk_line = 0;
  lex->tk_column = 0;
  lex->next = NULL;

  lex->buffer = (string_buffer_t *) safe_malloc(sizeof(string_buffer_t));
  init_string_buffer(lex->buffer, 128);
}

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
int32_t init_file_lexer(lexer_t *lex, char *filename) {
  int32_t code;
  
  code = init_file_reader(&lex->reader, filename);
  if (code >= 0) {
    init_lexer(lex);
  }
  return code;
}


/*
 * Same thing, starting from an already open stream f
 */
void init_stream_lexer(lexer_t *lex, FILE *f, char *name) {
  init_stream_reader(&lex->reader, f, name);
  init_lexer(lex);
}


/*
 * Initilize lexer for a string data
 */
void init_string_lexer(lexer_t *lex, char *data, char *name) {
  init_string_reader(&lex->reader, data, name);
  init_lexer(lex);
}


/*
 * Change the input string for lex to data
 */
void reset_string_lexer(lexer_t *lex, char *data) {
  reset_string_reader(&lex->reader, data);
  // reset token and location
  lex->token = -1;
  lex->tk_pos = 0;
  lex->tk_line = 0;
  lex->tk_column = 0;  
  string_buffer_reset(lex->buffer);
}



/*
 * Nested lexer: get buffer from parent
 * the reader is initialzed for filename.
 * TODO: report an error if there's a circular nesting
 * (i.e., same file is already open in an enclosing lexer)
 */
int32_t init_nested_lexer(lexer_t *lex, char *filename, lexer_t *parent) {
  int32_t code;

  lex->token = -1;
  lex->tk_pos = 0;
  lex->tk_line = 0;
  lex->tk_column = 0;

  code = init_file_reader(&lex->reader, filename);
  if (code < 0) {
    lex->buffer = NULL;
    lex->next = NULL;
    return code;
  } 

  string_buffer_reset(parent->buffer);
  lex->buffer = parent->buffer;
  lex->next = parent;
  return code;
}


/*
 * Nested lexer using a string data
 */
void init_nested_string_lexer(lexer_t *lex, char *data, char *name, lexer_t *parent) {
  lex->token = -1;
  lex->tk_pos = 0;
  lex->tk_line = 0;
  lex->tk_column = 0;

  init_string_reader(&lex->reader, data, name);
  lex->buffer = parent->buffer;
  lex->next = parent;
}

/*
 * Close lexer. If lex has no parent, delete the allocated
 * string buffer.
 */
int close_lexer(lexer_t *lex) {
  int code;

  code = close_reader(&lex->reader);
  if (lex->next == NULL) {
    if (lex->buffer != NULL) {
      delete_string_buffer(lex->buffer);
      safe_free(lex->buffer);
    }
  }
  return code;
}


/*
 * Variant: close lex but not the file/stream attached if any.
 * - this allows us to attach a lexer to stdin, then close it
 *   without closing stdin.
 * - if lex->next is NULL (toplevel lexer), delete the internal buffer
 */
void close_lexer_only(lexer_t *lex) {
  if (lex->next == NULL) {
    if (lex->buffer != NULL) {
      delete_string_buffer(lex->buffer);
      safe_free(lex->buffer);
    }
  }  
}



/*
 * Flush: read until the end of the line or EOF
 */
void flush_lexer(lexer_t *lex) {
  int c;
  c = reader_current_char(&lex->reader);
  while (c != '\n' && c != EOF) {
    c = reader_next_char(&lex->reader);
  }
  lex->token = -1;
  string_buffer_reset(lex->buffer);
}
