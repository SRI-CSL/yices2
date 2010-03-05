/*
 * Lexer for the SMT-LIB language (the benchmarks part)
 */

#include <ctype.h>
#include <assert.h>

/*
 * Provisional: set default visibility for functions used in test_smt_context
 */
#if defined(CYGWIN) || defined(MINGW)
#define EXPORTED __attribute__((dllexport))
#else
#define EXPORTED __attribute__((visibility("default")))
#endif


/*
 * smt_hash_keywords.h is generated using gperf
 * from input file smt_keywords.txt
 */

#include "smt_lexer.h"
#include "smt_hash_keywords.h"

/*
 * Keywords and attributes
 */
static keyword_t smt_keywords[] = {
  // keywords for formulas
  { "distinct",  SMT_TK_DISTINCT },
  { "ite", SMT_TK_ITE },
  { "=", SMT_TK_EQ },
  { "true", SMT_TK_TRUE },
  { "false", SMT_TK_FALSE },
  { "not", SMT_TK_NOT },
  { "implies", SMT_TK_IMPLIES },
  { "if_then_else", SMT_TK_IF_THEN_ELSE },
  { "and", SMT_TK_AND },
  { "or", SMT_TK_OR },
  { "xor", SMT_TK_XOR },
  { "iff", SMT_TK_IFF },
  { "exists", SMT_TK_EXISTS },
  { "forall", SMT_TK_FORALL },
  { "let", SMT_TK_LET },
  { "flet", SMT_TK_FLET },

  // pattern annotations
  { ":pat", SMT_TK_PAT },
  { ":nopat", SMT_TK_NOPAT },

  // benchmark keywords and attributes
  { "benchmark", SMT_TK_BENCHMARK },
  { "sat", SMT_TK_SAT },
  { "unsat", SMT_TK_UNSAT },
  { "unknown", SMT_TK_UNKNOWN },
  { ":logic", SMT_TK_LOGIC },
  { ":assumption", SMT_TK_ASSUMPTION },
  { ":formula", SMT_TK_FORMULA },
  { ":status", SMT_TK_STATUS },
  { ":extrasorts", SMT_TK_EXTRASORTS },
  { ":extrafuns", SMT_TK_EXTRAFUNS },
  { ":extrapreds", SMT_TK_EXTRAPREDS },
  { ":notes", SMT_TK_NOTES },

  // defined sorts 
  { "Array", SMT_TK_ARRAY },
  // { "U", SMT_TK_U }, // U cannot be used as a keyword. Some benchmarks use it as an identifier!
  { "Int", SMT_TK_INT },
  { "Real", SMT_TK_REAL },
  { "Array1", SMT_TK_ARRAY1 },
  { "Array2", SMT_TK_ARRAY2 },
  { "BitVec", SMT_TK_BITVEC },

  // function and predicate symbols
  { "+", SMT_TK_ADD },
  { "-", SMT_TK_SUB },
  { "*", SMT_TK_MUL },
  { "/", SMT_TK_DIV },
  { "~", SMT_TK_TILDE },
  { "<", SMT_TK_LT },
  { "<=", SMT_TK_LE },
  { ">", SMT_TK_GT },
  { ">=", SMT_TK_GE },
  { "select", SMT_TK_SELECT },
  { "store", SMT_TK_STORE },

  { "bvadd", SMT_TK_BVADD },
  { "bvsub", SMT_TK_BVSUB },
  { "bvmul", SMT_TK_BVMUL },
  { "bvneg", SMT_TK_BVNEG },
  { "bvor", SMT_TK_BVOR },
  { "bvand", SMT_TK_BVAND },
  { "bvxor", SMT_TK_BVXOR },
  { "bvnot", SMT_TK_BVNOT },
  { "bvlt", SMT_TK_BVLT },
  { "bvleq", SMT_TK_BVLEQ },
  { "bvgt", SMT_TK_BVGT },
  { "bvgeq", SMT_TK_BVGEQ },
  { "bvslt", SMT_TK_BVSLT },
  { "bvsleq", SMT_TK_BVSLEQ },
  { "bvsgt", SMT_TK_BVSGT },
  { "bvsgeq", SMT_TK_BVSGEQ },

  { "concat", SMT_TK_CONCAT },
  { "extract", SMT_TK_EXTRACT },
  { "sign_extend", SMT_TK_SIGN_EXTEND },
  { "shift_left0", SMT_TK_SHIFT_LEFT0 },
  { "shift_left1", SMT_TK_SHIFT_LEFT1 },
  { "shift_right0", SMT_TK_SHIFT_RIGHT0 },
  { "shift_right1", SMT_TK_SHIFT_RIGHT1 },
  { "bit0", SMT_TK_BIT0 },
  { "bit1", SMT_TK_BIT1 },

  // new bitvector keywords
  { "bvudiv", SMT_TK_BVUDIV },
  { "bvurem", SMT_TK_BVUREM },
  { "bvsdiv", SMT_TK_BVSDIV },
  { "bvsrem", SMT_TK_BVSREM },
  { "bvsmod", SMT_TK_BVSMOD },
  { "bvshl",  SMT_TK_BVSHL },
  { "bvlshr", SMT_TK_BVLSHR },
  { "bvashr", SMT_TK_BVASHR },
  { "bvnand", SMT_TK_BVNAND },
  { "bvnor",  SMT_TK_BVNOR },
  { "bvxnor", SMT_TK_BVXNOR },
  { "bvredor", SMT_TK_BVREDOR },
  { "bvredand", SMT_TK_BVREDAND },
  { "bvcomp", SMT_TK_BVCOMP },
  { "repeat", SMT_TK_REPEAT },
  { "zero_extend", SMT_TK_ZERO_EXTEND },
  { "rotate_left", SMT_TK_ROTATE_LEFT },
  { "rotate_right", SMT_TK_ROTATE_RIGHT },

  { "bvult", SMT_TK_BVULT },
  { "bvule", SMT_TK_BVULE },
  { "bvugt", SMT_TK_BVUGT },
  { "bvuge", SMT_TK_BVUGE },
  { "bvsle", SMT_TK_BVSLE }, 
  { "bvsge", SMT_TK_BVSGE },

  // end marker
  { NULL, 0 },
};



/*
 * Table for conversion from token to string
 */
static char *smt_token_string[NUM_SMT_TOKENS];


/*
 * Initialize the token-to-string table
 */
static void init_smttoken2string() {
  keyword_t *kw;

  // keywords
  kw = smt_keywords;
  while (kw->word != NULL) {
    smt_token_string[kw->tk] = kw->word;
    kw ++;
  }

  // other tokens
  smt_token_string[SMT_TK_LP] = "(";
  smt_token_string[SMT_TK_RP] = ")";
  smt_token_string[SMT_TK_LB] = "[";
  smt_token_string[SMT_TK_RB] = "]";
  smt_token_string[SMT_TK_COLON] = ":";
  smt_token_string[SMT_TK_EOS] = "<end-of-stream>";
  smt_token_string[SMT_TK_STRING] = "<string>";
  smt_token_string[SMT_TK_SYMBOL] = "<symbol>";
  smt_token_string[SMT_TK_VAR] = "<var>";
  smt_token_string[SMT_TK_FVAR] = "<fvar>";
  smt_token_string[SMT_TK_ATTRIBUTE] = "<attribute>";
  smt_token_string[SMT_TK_USER_VALUE] = "<user-value>";
  smt_token_string[SMT_TK_RATIONAL] = "<rational>";
  smt_token_string[SMT_TK_FLOAT] = "<float>";
  smt_token_string[SMT_TK_BV_CONSTANT] = "<bv-constant>";
  smt_token_string[SMT_TK_BV_BINCONSTANT] = "<bvbin-constant>";
  smt_token_string[SMT_TK_BV_HEXCONSTANT] = "<bvhex-constant>";

  // errors
  smt_token_string[SMT_TK_OPEN_STRING] = "<bad-string>";
  smt_token_string[SMT_TK_OPEN_USER_VAL] = "<bad-user-val>";
  smt_token_string[SMT_TK_ZERO_DIVISOR] = "<zero-divisor-in-rational>";
  smt_token_string[SMT_TK_INVALID_NUMBER] = "<bad-numeral>";
  smt_token_string[SMT_TK_ERROR] = "<error>";  
}



/*
 * Lexer initialization
 */
EXPORTED
int32_t init_smt_file_lexer(lexer_t *lex, char *filename) {
  init_smttoken2string();
  return init_file_lexer(lex, filename);
}

EXPORTED
void init_smt_stream_lexer(lexer_t *lex, FILE *f, char *name) {
  init_smttoken2string();
  init_stream_lexer(lex, f, name);
}

void init_smt_string_lexer(lexer_t *lex, char *data, char *name) {
  init_smttoken2string();
  init_string_lexer(lex, data, name);
}


/*
 * Get string for token tk
 */
char *smt_token_to_string(token_t tk) {
  assert(0 <= tk && tk < NUM_SMT_TOKENS);
  return smt_token_string[tk];
}


/*
 * Read a string literal:
 * - current char = "
 * - read all characters until either EOF or closing "
 * escape sequence \" can occur within the string
 *
 * Buffer contains the string literal without the doublequotes
 */
static token_t smt_read_string(lexer_t *lex) {  
  reader_t *rd;
  string_buffer_t *buffer;
  int c;
  token_t tk;

  rd = &lex->reader;
  buffer = lex->buffer;
  assert(reader_current_char(rd) == '"');

  for (;;) {
    c = reader_next_char(rd);
    if (c == '"') {
      tk = SMT_TK_STRING; break;
    }
    if (c == EOF) { // error
      tk = SMT_TK_OPEN_STRING; break;
    }
    if (c == '\\') {
      c = reader_next_char(rd);
      if (c != '"') { // keep backslash
	string_buffer_append_char(buffer, '\\');
      }
    }
    string_buffer_append_char(buffer, c);
  }

  string_buffer_close(buffer);
  return tk;
}

/*
 * Read a user value: 
 * - current char is '{'
 * - read until the terminating '}' or EOF
 * - escape sequences: \{ and \}
 *
 * On exit: buffer contains what was between '{' and '}'
 * as a null-terminated string.
 */
static token_t smt_read_user_val(lexer_t *lex) {  
  reader_t *rd;
  string_buffer_t *buffer;
  int c;
  token_t tk;

  rd = &lex->reader;
  buffer = lex->buffer;
  assert(reader_current_char(rd) == '{');

  for (;;) {
    c = reader_next_char(rd);
    if (c == '}') {
      tk = SMT_TK_USER_VALUE; break;
    }
    if (c == EOF) { // error
      tk = SMT_TK_OPEN_USER_VAL; break;
    }
    if (c == '\\') {
      c = reader_next_char(rd);
      if (c != '{' && c != '}') {
	string_buffer_append_char(buffer, '\\');
      }
    }
    string_buffer_append_char(buffer, c);
  }

  string_buffer_close(buffer);
  return tk;
}


/*
 * Read identifier and store it in the buffer, include the current char
 * (as first character of the identifier).
 *
 * Official SMT-LIB defines
 * simple identifier = sequence of letters, digits, dots, single quotes
 * and underscore, started by a letter.
 * arith symbol = nonempty sequence of the characters
 *     =, <, >, &, @, #, +, -, *, /, %, |, ~
 *
 * But we ignore that. 
 * We read until space, EOF, ", {, }, (, ), [, ], ; , :, ?, $, \ or ','
 */
static bool is_end_delimitor(int c) {
  switch(c) {
  case '"':
  case '{':
  case '}':
  case '(':
  case ')':
  case '[':
  case ']':
  case ';':
  case ':':
  case '?':
  case '$':
  case '\\':
  case ',':
  case EOF:
    return true;
  default:
    return isspace(c);
  }
}

static void smt_read_identifier(lexer_t *lex) {
  reader_t *rd;
  int c;
  string_buffer_t *buffer;

  rd = &lex->reader;
  buffer = lex->buffer;
  c = reader_current_char(rd);
  do {
    string_buffer_append_char(buffer, c);
    c = reader_next_char(rd);
  } while (! is_end_delimitor(c));

  string_buffer_close(buffer);
}


/*
 * Read an attribute, i.e., a symbol that start with ':', or a single ':'
 */
static token_t smt_read_attribute(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c, x;
  token_t tk;
  const keyword_t *kw;

  rd = &lex->reader;
  buffer = lex->buffer;
  c = reader_current_char(rd);
  assert(c == ':');
  x = reader_next_char(rd);

  if (isalpha(x)) {
    // attribute
    string_buffer_append_char(buffer, c);
    do {
      string_buffer_append_char(buffer, x);
      x = reader_next_char(rd);
    } while (! is_end_delimitor(x));

    string_buffer_close(buffer);
    tk = SMT_TK_ATTRIBUTE;
    kw = in_smt_kw(current_token_value(lex), current_token_length(lex));
    if (kw != NULL) {
      tk = kw->tk;
    }

  } else {
    // not an attribute
    tk = SMT_TK_COLON;
  }
  return tk;
}

/*
 * Read a number: formats are
 *    <digits>/<digits> or <digits>.<digits> or <digits>
 * current char is first digit
 */
static token_t smt_read_number(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c, all_zeros;
  token_t tk;

  rd = &lex->reader;
  buffer = lex->buffer;
  c = reader_current_char(rd);
  tk = SMT_TK_RATIONAL;
  assert(isdigit(c));  
  do {
    string_buffer_append_char(buffer, c);
    c = reader_next_char(rd);    
  } while (isdigit(c));

  if (c == '.') {
    string_buffer_append_char(buffer, c);
    c = reader_next_char(rd);
    if (! isdigit(c)) {
      tk = SMT_TK_INVALID_NUMBER;
      goto done;
    }
    do {
      string_buffer_append_char(buffer, c);
      c = reader_next_char(rd);    
    } while (isdigit(c));
    tk = SMT_TK_FLOAT;
    goto done;
  } 

  if (c == '/') {
    string_buffer_append_char(buffer, c);
    c = reader_next_char(rd);
    if (! isdigit(c)) {
      tk = SMT_TK_INVALID_NUMBER;
      goto done;
    }
    all_zeros = true;
    do {
      if (c != '0') all_zeros = false;
      string_buffer_append_char(buffer, c);
      c = reader_next_char(rd);    
    } while (isdigit(c));
    if (all_zeros) tk = SMT_TK_ZERO_DIVISOR;
    // else tk = SMT_TK_RATIONAL    
  }
    
 done:
  string_buffer_close(buffer);
  return tk;
}


/*
 * Read symbols, with special treatment for 
 *  bit vector constants "bv<digits>"
 *  or "bvbin<binary bits>"
 *  or "bvhex<hexadecimal digits>"
 */

// return the correct token type for the string in buffer
static token_t symbol_type(string_buffer_t *buffer) {
  uint32_t n, i;
  char *s;

  n = string_buffer_length(buffer);
  s = buffer->data;
  if (n > 2 && s[0] == 'b' && s[1] == 'v') {
    // bv prefix
    if (n > 5 && s[2] == 'b' && s[3] == 'i' && s[4] == 'n') {
      // bvbin prefix
      for (i=5; i<n; i++) {
	if (s[i] != '0' && s[i] != '1') {
	  return SMT_TK_SYMBOL;
	}
      }
      return SMT_TK_BV_BINCONSTANT;
      
    } else if (n > 5 && s[2] == 'h' && s[3] == 'e' && s[4] == 'x') {
      // bvhex prefix
      for (i=5; i<n; i++) {
	if (! isxdigit(s[i])) return SMT_TK_SYMBOL;
      }
      return SMT_TK_BV_HEXCONSTANT;

    } else {
      // bv prefix
      for (i=2; i<n; i++) {
	if (! isdigit(s[i])) return SMT_TK_SYMBOL;
      }
      // constant in decimal
      return SMT_TK_BV_CONSTANT;
    }
  }

  return SMT_TK_SYMBOL;
}

static token_t smt_read_symbol(lexer_t *lex) {
  token_t tk;
  string_buffer_t *buffer;
  const keyword_t *kw;
  
  smt_read_identifier(lex);
  buffer = lex->buffer;
  kw = in_smt_kw(buffer->data, buffer->index);
  if (kw == NULL) {
    tk = symbol_type(buffer);
  } else {
    tk = kw->tk;
  }

  return tk;
}

/*
 * Read next SMT token
 * - update lex->token, lex->tk_pos, lex->tk_line, lex->tk_column
 * - set token value in lex->buffer (as a null-terminated string).
 */
smt_token_t next_smt_token(lexer_t *lex) {
  token_t tk;
  reader_t *rd;
  int c;

  rd = &lex->reader;
  c = reader_current_char(rd);
  string_buffer_reset(lex->buffer);

  // skip spaces and comments
  // comments start with ';' and extend to the end of the line
  for (;;) {
    while (isspace(c)) c = reader_next_char(rd);
    if (c != ';') break;
    do {
      c = reader_next_char(rd);
    } while (c != '\n' && c != EOF);    
  }

  // record start of token
  lex->tk_pos = rd->pos;
  lex->tk_line = rd->line;
  lex->tk_column = rd->column;

  switch (c) {
  case '(':
    tk = SMT_TK_LP;
    goto next_then_return;
  case ')':
    tk = SMT_TK_RP;
    goto next_then_return;
  case '[':
    tk = SMT_TK_LB;
    goto next_then_return;
  case ']':
    tk = SMT_TK_RB;
    goto next_then_return;
  case EOF:
    tk = SMT_TK_EOS;
    goto done;
    // bad tokens
  case '}':
  case '\\':
  case '\'':
  case '_':
  case '.':
  case ',':
    // add the character to buffer for error reporting
    string_buffer_append_char(lex->buffer, c);
    string_buffer_close(lex->buffer);
    tk = SMT_TK_ERROR;
    goto next_then_return;

  case '"':
    // read until closing " or EOF
    tk = smt_read_string(lex);
    goto next_then_return;
  case '{':
    // read until closing '}' or EOF
    tk = smt_read_user_val(lex);
    goto next_then_return;

    // all other read_xxx read one character past the token.
  case ':':
    tk = smt_read_attribute(lex);
    goto done;
  case '?':
    tk = SMT_TK_VAR;
    smt_read_identifier(lex);
    goto done;
  case '$':
    tk = SMT_TK_FVAR;
    smt_read_identifier(lex);
    goto done;    
  case '0':
  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9':
    tk= smt_read_number(lex);
    goto done;
  default:
    tk = smt_read_symbol(lex);
    goto done;    
  }

  // advance to next input char then return
 next_then_return:
  reader_next_char(rd);
 done:
  lex->token = tk;  
  return tk;
}
