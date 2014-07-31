/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Lexer for the SMT-LIB language (the benchmarks part)
 */

#include <ctype.h>
#include <assert.h>

/*
 * smt_hash_keywords.h is generated using gperf
 * from input file smt_keywords.txt
 */

#include "frontend/smt1/smt_lexer.h"
#include "frontend/smt1/smt_hash_keywords.h"

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
static void init_smttoken2string(void) {
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
 * ACTIVE/INACTIVE TOKENS
 */

/*
 * Depending on the smt-lib logic, some keywords are interpreted as
 * built-in operators. If they are inactive, they are just interpreted
 * as ordinary symbols. We control which keywords are active using
 * array smt_token_active.
 *
 * As of 2011, the following logics/theories/type names are used:
 *
 *   AUFLIA         Int_ArraysEx                      Int Array
 *   AUFLIRA        Int_Int_Real_Array_ArraysEx       Int Real Array1 Array2
 *   AUFNIRA        Int_Int_Real_Array_ArraysEx       Int Real Array1 Array2
 *   LRA            Reals
 *   QF_AUFBV       BitVector_ArraysEx                Array BitVec
 *   QF_AUFLIA      Int_ArraysEx                      Int Array
 *   QF_AX          ArraysEx                          Array Index Element
 *   QF_BV          Fixed_Size_BitVectors             BitVec
 *   QF_IDL         Ints
 *   QF_LIA         Ints
 *   QF_LRA         Reals
 *   QF_NIA         Ints
 *   QF_NRA         Reals    (added July 2011)
 *   QF_RDL         Reals
 *   QF_UF          Empty
 *   QF_UFBV        Fixed_Size_BitVectors             BitVec
 *   QF_UFIDL       Ints
 *   QF_UFLIA       Ints
 *   QF_UFLRA       Reals
 *   QF_UFNRA       Reals
 *   UFLRA          Reals    (added July 2011)
 *   UFNIA          Ints
 *
 * More logics: added June 03 2014 (for SMTCOMP 2014)
 *
 *   ALIA:          Int_ArrayEx
 *   BV:            Fixed_Size_BitVectors
 *   LIA:           Ints
 *   NIA:           Ints
 *   NRA:           Reals
 *   QF_ABV:        BitVector_ArrayEx
 *   QF_ALIA:       Int_ArrayEx
 *   QF_LIRA:       Ints Reals
 *   QF_UFNIA:      Ints Reals
 *   UF:            Empty
 *   UFBV:          Fixed_Size_BitVectors
 *   UFIDL:         Ints
 *   UFLIA:         Ints
 *
 * More logics: added June 10 2014
 *
 *   QF_UFLIRA      Ints Reals
 */
static uint8_t smt_token_active[NUM_SMT_TOKENS];


/*
 * Default: activate all symbols that are not theory dependent
 */
static void activate_default_tokens(void) {
  uint32_t i;

  for (i=0; i<NUM_SMT_TOKENS; i++) {
    smt_token_active[i] = false;
  }

  smt_token_active[SMT_TK_DISTINCT] = true;
  smt_token_active[SMT_TK_ITE] = true;
  smt_token_active[SMT_TK_EQ] = true;
  smt_token_active[SMT_TK_TRUE] = true;
  smt_token_active[SMT_TK_FALSE] = true;
  smt_token_active[SMT_TK_NOT] = true;
  smt_token_active[SMT_TK_IMPLIES] = true;
  smt_token_active[SMT_TK_IF_THEN_ELSE] = true;
  smt_token_active[SMT_TK_AND] = true;
  smt_token_active[SMT_TK_OR] = true;
  smt_token_active[SMT_TK_XOR] = true;
  smt_token_active[SMT_TK_IFF] = true;
  smt_token_active[SMT_TK_EXISTS] = true;
  smt_token_active[SMT_TK_FORALL] = true;
  smt_token_active[SMT_TK_LET] = true;
  smt_token_active[SMT_TK_FLET] = true;

  smt_token_active[SMT_TK_BENCHMARK] = true;
  smt_token_active[SMT_TK_SAT] = true;
  smt_token_active[SMT_TK_UNSAT] = true;
  smt_token_active[SMT_TK_UNKNOWN] = true;
  smt_token_active[SMT_TK_LOGIC] = true;
  smt_token_active[SMT_TK_ASSUMPTION] = true;
  smt_token_active[SMT_TK_FORMULA] = true;
  smt_token_active[SMT_TK_STATUS] = true;
  smt_token_active[SMT_TK_EXTRASORTS] = true;
  smt_token_active[SMT_TK_EXTRAFUNS] = true;
  smt_token_active[SMT_TK_EXTRAPREDS] = true;
  smt_token_active[SMT_TK_NOTES] = true;
}


/*
 * Arithmetic symbols
 */
static void activate_arith_tokens(void) {
  smt_token_active[SMT_TK_ADD] = true;
  smt_token_active[SMT_TK_SUB] = true;
  smt_token_active[SMT_TK_MUL] = true;
  smt_token_active[SMT_TK_DIV] = true;
  smt_token_active[SMT_TK_TILDE] = true;
  smt_token_active[SMT_TK_LT] = true;
  smt_token_active[SMT_TK_LE] = true;
  smt_token_active[SMT_TK_GT] = true;
  smt_token_active[SMT_TK_GE] = true;
}

/*
 * Activate the array symbols
 */
static void activate_array_tokens(void) {
  smt_token_active[SMT_TK_SELECT] = true;
  smt_token_active[SMT_TK_STORE] = true;
  smt_token_active[SMT_TK_ARRAY] = true;
}


/*
 * Activate the bitvector symbols (old version): logic QF_UFBV[32]
 */
static void activate_old_bv_tokens(void) {
  smt_token_active[SMT_TK_BITVEC] = true;
  smt_token_active[SMT_TK_BVADD] = true;
  smt_token_active[SMT_TK_BVSUB] = true;
  smt_token_active[SMT_TK_BVMUL] = true;
  smt_token_active[SMT_TK_BVNEG] = true;
  smt_token_active[SMT_TK_BVOR] = true;
  smt_token_active[SMT_TK_BVAND] = true;
  smt_token_active[SMT_TK_BVXOR] = true;
  smt_token_active[SMT_TK_BVNOT] = true;
  smt_token_active[SMT_TK_BVLT] = true;
  smt_token_active[SMT_TK_BVLEQ] = true;
  smt_token_active[SMT_TK_BVGT] = true;
  smt_token_active[SMT_TK_BVGEQ] = true;
  smt_token_active[SMT_TK_BVSLT] = true;
  smt_token_active[SMT_TK_BVSLEQ] = true;
  smt_token_active[SMT_TK_BVSGT] = true;
  smt_token_active[SMT_TK_BVSGEQ] = true;
  smt_token_active[SMT_TK_CONCAT] = true;
  smt_token_active[SMT_TK_EXTRACT] = true;
  smt_token_active[SMT_TK_SIGN_EXTEND] = true;
  smt_token_active[SMT_TK_SHIFT_LEFT0] = true;
  smt_token_active[SMT_TK_SHIFT_LEFT1] = true;
  smt_token_active[SMT_TK_SHIFT_RIGHT0] = true;
  smt_token_active[SMT_TK_SHIFT_RIGHT1] = true;
  smt_token_active[SMT_TK_BIT0] = true;
  smt_token_active[SMT_TK_BIT1] = true;
}


/*
 * Activate the new bitvector symbols: logic QF_BV
 */
static void activate_new_bv_tokens(void) {
  smt_token_active[SMT_TK_BITVEC] = true;
  smt_token_active[SMT_TK_BVADD] = true;
  smt_token_active[SMT_TK_BVSUB] = true;
  smt_token_active[SMT_TK_BVMUL] = true;
  smt_token_active[SMT_TK_BVNEG] = true;
  smt_token_active[SMT_TK_BVOR] = true;
  smt_token_active[SMT_TK_BVAND] = true;
  smt_token_active[SMT_TK_BVXOR] = true;
  smt_token_active[SMT_TK_BVNOT] = true;
  smt_token_active[SMT_TK_BVUDIV] = true;
  smt_token_active[SMT_TK_BVUREM] = true;
  smt_token_active[SMT_TK_BVSDIV] = true;
  smt_token_active[SMT_TK_BVSREM] = true;
  smt_token_active[SMT_TK_BVSMOD] = true;
  smt_token_active[SMT_TK_BVSHL] = true;
  smt_token_active[SMT_TK_BVLSHR] = true;
  smt_token_active[SMT_TK_BVASHR] = true;
  smt_token_active[SMT_TK_BVNAND] = true;
  smt_token_active[SMT_TK_BVNOR] = true;
  smt_token_active[SMT_TK_BVXNOR] = true;
  smt_token_active[SMT_TK_BVREDOR] = true;
  smt_token_active[SMT_TK_BVREDAND] = true;
  smt_token_active[SMT_TK_BVCOMP] = true;
  smt_token_active[SMT_TK_REPEAT] = true;
  smt_token_active[SMT_TK_ZERO_EXTEND] = true;
  smt_token_active[SMT_TK_ROTATE_LEFT] = true;
  smt_token_active[SMT_TK_ROTATE_RIGHT] = true;

  smt_token_active[SMT_TK_CONCAT] = true;
  smt_token_active[SMT_TK_EXTRACT] = true;
  smt_token_active[SMT_TK_SIGN_EXTEND] = true;
  smt_token_active[SMT_TK_BIT0] = true;
  smt_token_active[SMT_TK_BIT1] = true;

  smt_token_active[SMT_TK_BVULT] = true;
  smt_token_active[SMT_TK_BVULE] = true;
  smt_token_active[SMT_TK_BVUGT] = true;
  smt_token_active[SMT_TK_BVUGE] = true;
  smt_token_active[SMT_TK_BVSLT] = true;
  smt_token_active[SMT_TK_BVSLE] = true;
  smt_token_active[SMT_TK_BVSGT] = true;
  smt_token_active[SMT_TK_BVSGE] = true;
}



/*
 * Support for integer/real/mixed arithmetic
 */
static void activate_arith_fragment(arith_fragment_t code) {
  switch (code) {
  case ARITH_IDL:
  case ARITH_LIA:
  case ARITH_NIA:
    activate_arith_tokens();
    smt_token_active[SMT_TK_INT] = true;
    break;

  case ARITH_RDL:
  case ARITH_LRA:
  case ARITH_NRA:
    activate_arith_tokens();
    smt_token_active[SMT_TK_REAL] = true;
    break;

  case ARITH_LIRA:
  case ARITH_NIRA:
    activate_arith_tokens();
    smt_token_active[SMT_TK_INT] = true;
    smt_token_active[SMT_TK_REAL] = true;
    break;

  case ARITH_NONE:
    break;
  }
}

/*
 * Configure the lexer for a given SMT-LIB Logic
 */
void smt_lexer_activate_logic(smt_logic_t code) {
  switch (code) {
  case AUFLIRA:
  case AUFNIRA:
  case QF_AUFLIRA:
  case QF_AUFNIRA:
    // Special cases: arrays + int + real
    // We must activate ARRAY1 and ARRAY2
    activate_arith_tokens();
    activate_array_tokens();
    smt_token_active[SMT_TK_ARRAY1] = true;
    smt_token_active[SMT_TK_ARRAY2] = true;
    smt_token_active[SMT_TK_REAL] = true;
    smt_token_active[SMT_TK_INT] = true;
    break;

  case QF_UFBV:
    activate_old_bv_tokens();
    break;

  default:
    activate_arith_fragment(arith_fragment(code));
    if (logic_has_arrays(code)) {
      activate_array_tokens();
    }
    if (logic_has_bv(code)) {
      activate_new_bv_tokens();
    }
    break;
  }
}



/*
 * Lexer initialization
 */
int32_t init_smt_file_lexer(lexer_t *lex, char *filename) {
  init_smttoken2string();
  activate_default_tokens();
  return init_file_lexer(lex, filename);
}

void init_smt_stream_lexer(lexer_t *lex, FILE *f, char *name) {
  init_smttoken2string();
  activate_default_tokens();
  init_stream_lexer(lex, f, name);
}

void init_smt_string_lexer(lexer_t *lex, char *data, char *name) {
  init_smttoken2string();
  activate_default_tokens();
  init_string_lexer(lex, data, name);
}


/*
 * Get string for token tk
 */
char *smt_token_to_string(smt_token_t tk) {
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
static smt_token_t smt_read_string(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c;
  smt_token_t tk;

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
static smt_token_t smt_read_user_val(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c;
  smt_token_t tk;

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
static smt_token_t smt_read_attribute(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c, x;
  smt_token_t tk;
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
static smt_token_t smt_read_number(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c, all_zeros;
  smt_token_t tk;

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
static smt_token_t symbol_type(string_buffer_t *buffer) {
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
        // need coercion here to stop a warning
        if (! isxdigit((int) s[i])) return SMT_TK_SYMBOL;
      }
      return SMT_TK_BV_HEXCONSTANT;

    } else {
      // bv prefix
      for (i=2; i<n; i++) {
        // need coercion here to stop a warning
        if (! isdigit((int) s[i])) return SMT_TK_SYMBOL;
      }
      // constant in decimal
      return SMT_TK_BV_CONSTANT;
    }
  }

  return SMT_TK_SYMBOL;
}

static smt_token_t smt_read_symbol(lexer_t *lex) {
  smt_token_t tk;
  string_buffer_t *buffer;
  const keyword_t *kw;

  smt_read_identifier(lex);
  buffer = lex->buffer;
  kw = in_smt_kw(buffer->data, buffer->index);
  if (kw == NULL || !smt_token_active[kw->tk]) {
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
  smt_token_t tk;
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
