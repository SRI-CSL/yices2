/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRETTY PRINTER FOR YICES OBJECTS
 */

#include <string.h>

#include "io/yices_pp.h"


/*
 * OPEN BLOCK DESCRIPTORS
 */

/*
 * For each open block id we need
 * - label = string label
 * - lsize = length of the label
 * - formats = preferred layouts
 * - flags = whether the block starts with '('
 *         + whether a space or line break is required after the label
 * - indent = indentation level (for M and V layouts)
 * - short_indent = indentation in T layout.
 */
typedef struct pp_open_desc_s {
  char *label;
  uint8_t formats;
  uint8_t flags;
  uint16_t label_size;
  uint16_t indent;
  uint16_t short_indent;
} pp_open_desc_t;

static pp_open_desc_t open_desc[NUM_PP_OPENS];


/*
 * Most blocks use the default settings:
 *   preferred format = HMT
 *   flags = parenthesis + separator
 *   indent = size of the label + 2
 *   short indent = 1
 * To initialize them, we need just id + label
 */
typedef struct pp_standard_block_s {
  pp_open_type_t id;
  char *label;
} pp_standard_block_t;


/*
 * For non-standard blocks, we need the full description
 * - label, formats, flags, indent, short_indent
 * - if indent is 0, then it's set during initialization
 *   (to label_size + 2)
 */
typedef struct pp_nonstandard_block_s {
  pp_open_type_t id;
  char *label;
  uint8_t formats;
  uint8_t flags;
  uint16_t indent;
  uint16_t short_indent;
} pp_nonstandard_block_t;



/*
 * Default flags: parenthesis + separator required
 */
#define PP_TOKEN_DEF_MASK (PP_TOKEN_PAR_MASK|PP_TOKEN_SEP_MASK)


/*
 * Default short indent
 */
#define PP_DEFAULT_SHORT_INDENT 1



/*
 * Table of standard blocks
 */
#define NUM_STANDARD_BLOCKS 40

static const pp_standard_block_t standard_block[NUM_STANDARD_BLOCKS] = {
  { PP_OPEN_FUN_TYPE, "->" },
  { PP_OPEN_TUPLE_TYPE, "tuple" },
  { PP_OPEN_ITE, "ite" },
  { PP_OPEN_UPDATE, "update" },
  { PP_OPEN_TUPLE, "mk-tuple" },
  { PP_OPEN_SELECT, "select" },
  { PP_OPEN_EQ, "=" },
  { PP_OPEN_NEQ, "/=" },
  { PP_OPEN_DISTINCT, "distinct" },
  { PP_OPEN_NOT, "not" },
  { PP_OPEN_OR, "or" },
  { PP_OPEN_AND, "and" },
  { PP_OPEN_XOR, "xor" },
  { PP_OPEN_IMPLIES, "=>" },
  { PP_OPEN_BIT, "bit" },
  { PP_OPEN_PROD, "*" },
  { PP_OPEN_POWER, "^" },
  { PP_OPEN_SUM, "+" },
  { PP_OPEN_DIV, "/" },
  { PP_OPEN_MINUS, "-" },
  { PP_OPEN_GE, ">=" },
  { PP_OPEN_LT, "<" },
  { PP_OPEN_BV_ARRAY, "bit-array" },
  { PP_OPEN_BV_SUM, "bv-add" },
  { PP_OPEN_BV_PROD, "bv-mul" },
  { PP_OPEN_BV_POWER, "bv-pow" },
  { PP_OPEN_BV_DIV, "bv-div" },
  { PP_OPEN_BV_REM, "bv-rem" },
  { PP_OPEN_BV_SDIV, "bv-sdiv" },
  { PP_OPEN_BV_SREM, "bv-srem" },
  { PP_OPEN_BV_SMOD, "bv-smod" },
  { PP_OPEN_BV_SHL, "bv-shl" },
  { PP_OPEN_BV_LSHR, "bv-lshr" },
  { PP_OPEN_BV_ASHR, "bv-ashr" },
  { PP_OPEN_BV_GE, "bv-ge" },
  { PP_OPEN_BV_LT, "bv-lt" },
  { PP_OPEN_BV_SGE, "bv-sge" },
  { PP_OPEN_BV_SLT, "bv-slt" },
  { PP_OPEN_TYPE, "type" },
  { PP_OPEN_DEFAULT, "default" },
};


/*
 * Table of non-standard blocks
 */
#define NUM_NONSTANDARD_BLOCKS 11

static const pp_nonstandard_block_t nonstandard_block[NUM_NONSTANDARD_BLOCKS] = {
  { PP_OPEN, "", PP_HMT_LAYOUT, 0, 1, 1 },
  { PP_OPEN_PAR, "", PP_HMT_LAYOUT, PP_TOKEN_PAR_MASK, 1, 1 },
  { PP_OPEN_VPAR, "", PP_V_LAYOUT, PP_TOKEN_PAR_MASK, 1, 1 },
  { PP_OPEN_BV_TYPE, "bitvector", PP_H_LAYOUT, PP_TOKEN_DEF_MASK, 0, 0 },
  { PP_OPEN_CONST_DEF, "constant", PP_H_LAYOUT, PP_TOKEN_DEF_MASK, 0, 0 },
  { PP_OPEN_UNINT_DEF, "unint", PP_H_LAYOUT, PP_TOKEN_DEF_MASK, 0, 0 },
  { PP_OPEN_VAR_DEF,   "var", PP_H_LAYOUT, PP_TOKEN_DEF_MASK, 0, 0 },
  { PP_OPEN_FORALL, "forall ", PP_HMT_LAYOUT,  0, 7, 7 },
  { PP_OPEN_EXISTS, "exits ", PP_HMT_LAYOUT, 0, 6, 6 },
  { PP_OPEN_LAMBDA, "lambda ", PP_HMT_LAYOUT, 0, 7, 7 },
  { PP_OPEN_FUNCTION, "function ", PP_V_LAYOUT, PP_TOKEN_PAR_MASK, 1, 1 },
};



/*
 * INITIALIZATION OF THE OPEN-BLOCK DESCRIPTORS
 */
void init_yices_pp_tables(void) {
  char *label;
  uint32_t i, n, d, s;
  pp_open_type_t id;

  for (i=0; i<NUM_STANDARD_BLOCKS; i++) {
    id = standard_block[i].id;
    label = standard_block[i].label;
    n = strlen(label);

    assert(0 <= id && id < NUM_PP_OPENS && n+2 <= UINT16_MAX);

    open_desc[id].label = label;
    open_desc[id].formats = PP_HMT_LAYOUT;
    open_desc[id].flags = PP_TOKEN_DEF_MASK;
    open_desc[id].label_size = n;
    open_desc[id].indent = n+2;
    open_desc[id].short_indent = PP_DEFAULT_SHORT_INDENT;
  }

  for (i=0; i<NUM_NONSTANDARD_BLOCKS; i++) {
    id = nonstandard_block[i].id;
    label = nonstandard_block[i].label;
    n = strlen(label);
    d = nonstandard_block[i].indent;
    if (d == 0) {
      s = nonstandard_block[i].flags;
      d = n + ((s & PP_TOKEN_PAR_MASK) != 0) + ((s & PP_TOKEN_SEP_MASK) != 0);
    }

    s = nonstandard_block[i].short_indent;
    if (s == 0) {
      s = PP_DEFAULT_SHORT_INDENT;
    }

    assert(0 <= id && id < NUM_PP_OPENS && n+2 <= UINT16_MAX);
    open_desc[id].label = label;
    open_desc[id].formats = nonstandard_block[i].formats;
    open_desc[id].flags = nonstandard_block[i].flags;
    open_desc[id].label_size = n;
    open_desc[id].indent = d;
    open_desc[id].short_indent = s;
  }
}


/*
 * ATOM STRING BUILDERS
 */

/*
 * Each function builds a string in a string buffer
 * for a specific atom type.
 * - s must be empty when the build function is called
 */
static void build_char(string_buffer_t *b, char c) {
  string_buffer_append_char(b, c);
  string_buffer_close(b);
}

static void build_id(string_buffer_t *b, const char *prefix, int32_t index) {
  string_buffer_append_string(b, prefix);
  string_buffer_append_int32(b, index);
  string_buffer_close(b);
}

static void build_varid(string_buffer_t *b, const char *prefix, int32_t index) {
  string_buffer_append_string(b, prefix);
  string_buffer_append_char(b, '!');
  string_buffer_append_int32(b, index);
  string_buffer_close(b);
}

static void build_int32(string_buffer_t *b, int32_t x) {
  string_buffer_append_int32(b, x);
  string_buffer_close(b);
}

static void build_uint32(string_buffer_t *b, uint32_t x) {
  string_buffer_append_uint32(b, x);
  string_buffer_close(b);
}

static void build_mpz(string_buffer_t *b, mpz_t z) {
  string_buffer_append_mpz(b, z);
  string_buffer_close(b);
}

static void build_mpq(string_buffer_t *b, mpq_t q) {
  string_buffer_append_mpq(b, q);
  string_buffer_close(b);
}

static void build_rational(string_buffer_t *b, rational_t *q) {
  string_buffer_append_rational(b, q);
  string_buffer_close(b);
}

// prefix = "0b"
static void build_bv(string_buffer_t *b, uint32_t *bv, uint32_t n) {
  assert(0 < n);
  string_buffer_append_char(b, '0');
  string_buffer_append_char(b, 'b');
  string_buffer_append_bvconst(b, bv, n);
  string_buffer_close(b);
}

static void build_bv64(string_buffer_t *b, uint64_t bv, uint32_t n) {
  uint32_t aux[2];

  assert(0 < n && n <= 64);
  aux[0] = (uint32_t) bv; // low order bits
  aux[1] = (uint32_t) (bv >> 32); // high order bits
  build_bv(b, aux, n);
}

static void build_qstring(string_buffer_t *b, char quote[2], const char *str) {
  if (quote[0] != '\0') {
    string_buffer_append_char(b, quote[0]);
  }
  string_buffer_append_string(b, str);
  if (quote[1] != '\0') {
    string_buffer_append_char(b, quote[1]);
  }
  string_buffer_close(b);
}

// smt2 variants of build_bv and build_bv64: the prefix is #b
static void build_smt2_bv(string_buffer_t *b, uint32_t *bv, uint32_t n) {
  assert(0 < n);
  string_buffer_append_char(b, '#');
  string_buffer_append_char(b, 'b');
  string_buffer_append_bvconst(b, bv, n);
  string_buffer_close(b);
}

static void build_smt2_bv64(string_buffer_t *b, uint64_t bv, uint32_t n) {
  uint32_t aux[2];

  assert(0 < n && n <= 64);
  aux[0] = (uint32_t) bv; // low order bits
  aux[1] = (uint32_t) (bv >> 32); // high order bits
  build_smt2_bv(b, aux, n);
}


/*
 * TOKEN CONVERSION
 */

/*
 * Label of an open block token
 */
static char *get_label(yices_pp_t *printer, pp_open_token_t *tk) {
  uint32_t id;

  id = tk->user_tag;
  assert(id < NUM_PP_OPENS);
  return open_desc[id].label;
}


/*
 * Content of an atomic token
 */
static const char *get_string(yices_pp_t *printer, pp_atomic_token_t *tk) {
  string_buffer_t *buffer;
  pp_atom_t *atm;
  const char *s;

  buffer = &printer->buffer;
  assert(string_buffer_length(buffer) == 0);

  atm = (pp_atom_t *) tk;
  switch (tk->user_tag) {
  case PP_CHAR_ATOM:
    build_char(buffer, atm->data.c);
    s = buffer->data;
    break;
  case PP_STRING_ATOM:
    s = atm->data.string;
    break;
  case PP_ID_ATOM:
    build_id(buffer, atm->data.id.prefix, atm->data.id.index);
    s = buffer->data;
    break;
  case PP_VARID_ATOM:
    build_varid(buffer, atm->data.id.prefix, atm->data.id.index);
    s = buffer->data;
    break;
  case PP_TRUE_ATOM:
    s = "true";
    break;
  case PP_FALSE_ATOM:
    s = "false";
    break;
  case PP_INT32_ATOM:
    build_int32(buffer, atm->data.i32);
    s = buffer->data;
    break;
  case PP_UINT32_ATOM:
    build_uint32(buffer, atm->data.u32);
    s = buffer->data;
    break;
  case PP_RATIONAL_ATOM:
    build_rational(buffer, &atm->data.rat);
    s = buffer->data;
    break;
  case PP_BV64_ATOM:
    build_bv64(buffer, atm->data.bv64.bv, atm->data.bv64.nbits);
    s = buffer->data;
    break;
  case PP_BV_ATOM:
    build_bv(buffer, atm->data.bv.bv, atm->data.bv.nbits);
    s = buffer->data;
    break;
  case PP_QSTRING_ATOM:
    build_qstring(buffer, atm->data.qstr.quote, atm->data.qstr.str);
    s = buffer->data;
    break;
  case PP_SMT2_BV64_ATOM:
    build_smt2_bv64(buffer, atm->data.bv64.bv, atm->data.bv64.nbits);
    s = buffer->data;
    break;
  case PP_SMT2_BV_ATOM:
    build_smt2_bv(buffer, atm->data.bv.bv, atm->data.bv.nbits);
    s = buffer->data;
    break;

  default:
    assert(false);
    s = NULL;
    break;
  }

  return s;
}


/*
 * Truncated content: just use the same thing as get_string
 */
static const char *get_truncated(yices_pp_t *printer, pp_atomic_token_t *tk, uint32_t n) {
  return get_string(printer, tk);
}


/*
 * FREE TOKEN
 */

/*
 * Free an open block token
 */
static void free_open_token(yices_pp_t *printer, pp_open_token_t *tk) {
  objstore_free(&printer->open_store, tk);
}


/*
 * Free an atomic token
 * - free the data if it's a rational
 * - also reset the string buffer
 */
static void free_atomic_token(yices_pp_t *printer, pp_atomic_token_t *tk) {
  pp_atom_t *atm;

  atm = (pp_atom_t *) tk;
  if (tk->user_tag == PP_RATIONAL_ATOM) {
    q_clear(&atm->data.rat);
  }
  objstore_free(&printer->atom_store, tk);
  string_buffer_reset(&printer->buffer);
}


/*
 * Free a close token: do nothing
 */
static void free_close_token(yices_pp_t *printer, pp_close_token_t *tk) {
}



/*
 * Initialization
 * - file = output file (must be open for write)
 * - area = display area (cf. pretty_printer.h)
 * - mode = initial print mode (cf. pretty printer.h)
 * - indent = initial indentation
 * If area is NULL, then the default is used (cf. pretty_printer.h)
 */
void init_yices_pp(yices_pp_t *printer, FILE *file, pp_area_t *area,
                   pp_print_mode_t mode, uint32_t indent) {
  pp_token_converter_t converter;

  /*
   * Initialize the stores, close tokens, and buffer first
   */
  init_objstore(&printer->open_store, sizeof(pp_open_token_t), 1000);
  init_objstore(&printer->atom_store, sizeof(pp_atom_t), 1000);
  printer->close[0] = init_close_token(&printer->close_nopar, false, PP_CLOSE);
  printer->close[1] = init_close_token(&printer->close_par, true, PP_CLOSE_PAR);
  init_string_buffer(&printer->buffer, 200);

  /*
   * initialize the converter structure
   * it's safe since init_pp makes a copy of that structure.
   */
  converter.user_ptr = printer;
  converter.get_label = (get_label_fun_t) get_label;
  converter.get_string = (get_string_fun_t) get_string;
  converter.get_truncated = (get_truncated_fun_t) get_truncated;
  converter.free_open_token = (free_open_token_fun_t) free_open_token;
  converter.free_atomic_token = (free_atomic_token_fun_t) free_atomic_token;
  converter.free_close_token = (free_close_token_fun_t) free_close_token;

  /*
   * Initialize the actual pretty printer
   */
  init_pp(&printer->pp, &converter, file, area, mode, indent);
}


/*
 * Flush: print everything pending + a newline
 * - then reset the line counter to 0
 */
void flush_yices_pp(yices_pp_t *printer) {
  flush_pp(&printer->pp);
}


/*
 * Flush then delete a pretty printer
 * - if flush is true, print everything pending + a newline
 * - then free all memory used
 */
void delete_yices_pp(yices_pp_t *printer, bool flush) {
  if (flush) {
    flush_pp(&printer->pp);
  }
  delete_pp(&printer->pp);
  delete_objstore(&printer->open_store);
  delete_objstore(&printer->atom_store);
  delete_string_buffer(&printer->buffer);
}




/*
 * PRINT ATOMS
 */


/*
 * Allocate an atom
 */
static inline pp_atom_t *new_atom(yices_pp_t *printer) {
  return (pp_atom_t *) objstore_alloc(&printer->atom_store);
}


/*
 * Single character c
 */
void pp_char(yices_pp_t *printer, char c) {
  pp_atom_t *atom;
  void *tk;

  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, 1, PP_CHAR_ATOM);
  atom->data.c = c;

  pp_push_token(&printer->pp, tk);
}

/*
 * String s: no copy is made
 */
void pp_string(yices_pp_t *printer, const char *s) {
  pp_atom_t *atom;
  void *tk;
  uint32_t n;

  n = strlen(s);
  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n, PP_STRING_ATOM);
  atom->data.string = s;

  pp_push_token(&printer->pp, tk);
}


/*
 * Identifier: as above, we don't copy the prefix
 */
void pp_id(yices_pp_t *printer, const char *prefix, int32_t index) {
  pp_atom_t *atom;
  void *tk;
  string_buffer_t *buffer;
  uint32_t n;

  // we use the buffer to get the token size
  buffer = &printer->buffer;
  assert(string_buffer_length(buffer) == 0);
  build_id(buffer, prefix, index);
  n = string_buffer_length(buffer);
  string_buffer_reset(buffer);

  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n, PP_ID_ATOM);
  atom->data.id.prefix = prefix;
  atom->data.id.index = index;

  pp_push_token(&printer->pp, tk);
}


void pp_varid(yices_pp_t *printer, const char *prefix, int32_t index) {
  pp_atom_t *atom;
  void *tk;
  string_buffer_t *buffer;
  uint32_t n;

  // we use the buffer to get the token size
  buffer = &printer->buffer;
  assert(string_buffer_length(buffer) == 0);
  build_varid(buffer, prefix, index);
  n = string_buffer_length(buffer);
  string_buffer_reset(buffer);

  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n, PP_VARID_ATOM);
  atom->data.id.prefix = prefix;
  atom->data.id.index = index;

  pp_push_token(&printer->pp, tk);
}

void pp_bool(yices_pp_t *printer, bool tt) {
  pp_atom_t *atom;
  void *tk;

  atom = new_atom(printer);
  if (tt) {
    tk = init_atomic_token(&atom->tk, 4, PP_TRUE_ATOM);
  } else {
    tk = init_atomic_token(&atom->tk, 5, PP_FALSE_ATOM);
  }

  pp_push_token(&printer->pp, tk);
}


void pp_int32(yices_pp_t *printer, int32_t x) {
  pp_atom_t *atom;
  void *tk;
  string_buffer_t *buffer;
  uint32_t n;

  // could do something better to compute the size?
  buffer = &printer->buffer;
  assert(string_buffer_length(buffer) == 0);
  build_int32(buffer, x);
  n = string_buffer_length(buffer);
  string_buffer_reset(buffer);

  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n, PP_INT32_ATOM);
  atom->data.i32 = x;

  pp_push_token(&printer->pp, tk);
}

void pp_uint32(yices_pp_t *printer, uint32_t x) {
  pp_atom_t *atom;
  void *tk;
  string_buffer_t *buffer;
  uint32_t n;

  // could do something better to compute the size?
  buffer = &printer->buffer;
  assert(string_buffer_length(buffer) == 0);
  build_uint32(buffer, x);
  n = string_buffer_length(buffer);
  string_buffer_reset(buffer);

  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n, PP_UINT32_ATOM);
  atom->data.u32 = x;

  pp_push_token(&printer->pp, tk);
}


/*
 * mpz and mpq are converted to rationals.
 */
void pp_mpz(yices_pp_t *printer, mpz_t z) {
  pp_atom_t *atom;
  void *tk;
  string_buffer_t *buffer;
  uint32_t n;

  buffer = &printer->buffer;
  assert(string_buffer_length(buffer) == 0);
  build_mpz(buffer, z);
  n = string_buffer_length(buffer);
  string_buffer_reset(buffer);

  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n, PP_RATIONAL_ATOM);
  q_init(&atom->data.rat);
  q_set_mpz(&atom->data.rat, z);

  pp_push_token(&printer->pp, tk);
}


void pp_mpq(yices_pp_t *printer, mpq_t q) {
  pp_atom_t *atom;
  void *tk;
  string_buffer_t *buffer;
  uint32_t n;

  buffer = &printer->buffer;
  assert(string_buffer_length(buffer) == 0);
  build_mpq(buffer, q);
  n = string_buffer_length(buffer);
  string_buffer_reset(buffer);

  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n, PP_RATIONAL_ATOM);
  q_init(&atom->data.rat);
  q_set_mpq(&atom->data.rat, q);

  pp_push_token(&printer->pp, tk);
}


void pp_rational(yices_pp_t *printer, rational_t *q) {
  pp_atom_t *atom;
  void *tk;
  string_buffer_t *buffer;
  uint32_t n;

  buffer = &printer->buffer;
  assert(string_buffer_length(buffer) == 0);
  build_rational(buffer, q);
  n = string_buffer_length(buffer);
  string_buffer_reset(buffer);

  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n, PP_RATIONAL_ATOM);
  q_init(&atom->data.rat);
  q_set(&atom->data.rat, q);

  pp_push_token(&printer->pp, tk);
}


void pp_bv64(yices_pp_t *printer, uint64_t bv, uint32_t n) {
  pp_atom_t *atom;
  void *tk;

  assert(0 < n && n <= 64);
  atom = new_atom(printer);
  // bitvector constants are printed as 0bxxx... so
  // the length is n+2
  tk = init_atomic_token(&atom->tk, n+2, PP_BV64_ATOM);
  atom->data.bv64.bv = bv;
  atom->data.bv64.nbits = n;

  pp_push_token(&printer->pp, tk);
}


/*
 * No copy of bv is made
 */
void pp_bv(yices_pp_t *printer, uint32_t *bv, uint32_t n) {
  pp_atom_t *atom;
  void *tk;

  assert(0 < n);
  atom = new_atom(printer);
  // bitvector constants are printed as 0bxxx... so
  // the length is n+2
  tk = init_atomic_token(&atom->tk, n+2, PP_BV_ATOM);
  atom->data.bv.bv = bv;
  atom->data.bv.nbits = n;

  pp_push_token(&printer->pp, tk);
}


/*
 * Separator s: no copy is made
 */
void pp_separator(yices_pp_t *printer, const char *s) {
  pp_atom_t *atom;
  void *tk;
  uint32_t n;

  n = strlen(s);
  atom = new_atom(printer);
  tk = init_separator_token(&atom->tk, n, PP_STRING_ATOM);
  atom->data.string = s;

  pp_push_token(&printer->pp, tk);
}


/*
 * Quoted string:
 * - open_quote = character before the string (or '\0' if nothing needed)
 * - close_quote = charcater after the string (or '\0' if nothing needed)
 *
 * Examples
 *   pp_qstring(printer, '"', '"', "abcde") will print "abcde" (quotes included)
 *   pp_qstring(printer, '\'', '\0', "abcde") will print 'abcde
 */
void pp_qstring(yices_pp_t *printer, char open_quote, char close_quote, const char *s) {
  pp_atom_t *atom;
  void *tk;
  uint32_t n;

  n = strlen(s) + (open_quote != '\0') + (close_quote != '\0');
  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n, PP_QSTRING_ATOM);
  atom->data.qstr.str = s;
  atom->data.qstr.quote[0] = open_quote;
  atom->data.qstr.quote[1] = close_quote;

  pp_push_token(&printer->pp, tk);
}


/*
 * Variants of pp_bv and pp_bv64 for the SMT2 notation
 */
void pp_smt2_bv64(yices_pp_t *printer, uint64_t bv, uint32_t n) {
  pp_atom_t *atom;
  void *tk;

  assert(0 < n && n <= 64);
  atom = new_atom(printer);
  // bitvector constants are printed as #bxxx... so
  // the length is n+2
  tk = init_atomic_token(&atom->tk, n+2, PP_SMT2_BV64_ATOM);
  atom->data.bv64.bv = bv;
  atom->data.bv64.nbits = n;

  pp_push_token(&printer->pp, tk);
}

void pp_smt2_bv(yices_pp_t *printer, uint32_t *bv, uint32_t n) {
  pp_atom_t *atom;
  void *tk;

  assert(0 < n);
  atom = new_atom(printer);
  // bitvector constants are printed as #bxxx... so
  // the length is n+2
  tk = init_atomic_token(&atom->tk, n+2, PP_SMT2_BV_ATOM);
  atom->data.bv.bv = bv;
  atom->data.bv.nbits = n;

  pp_push_token(&printer->pp, tk);
}




/*
 * OPEN AND CLOSE BLOCK
 */

/*
 * Allocate an open token
 */
static inline pp_open_token_t *new_open_token(yices_pp_t *printer) {
  return (pp_open_token_t *) objstore_alloc(&printer->open_store);
}

/*
 * Start an block given the open-block id
 */
void pp_open_block(yices_pp_t *printer, pp_open_type_t id) {
  pp_open_token_t *open;
  pp_open_desc_t *desc;
  void *tk;

  assert(0 <= id && id < NUM_PP_OPENS);
  desc = open_desc + id;
  open = new_open_token(printer);
  tk = init_open_token(open,
                       desc->formats, desc->flags, desc->label_size,
                       desc->indent, desc->short_indent, id);

  pp_push_token(&printer->pp, tk);
}


/*
 * Close a block
 * - par: true if a parenthesis is required
 *        false to close and print nothing
 */
void pp_close_block(yices_pp_t *printer, bool par) {
  pp_push_token(&printer->pp, printer->close[par]);
}

