/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * PRETTY PRINTER FOR YICES OBJECTS
 */

#include <string.h>
#ifdef HAVE_MCSAT
#include <poly/algebraic_number.h>
#endif
#include "io/yices_pp.h"
#include "io/type_printer.h"

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
#define NUM_STANDARD_BLOCKS 54

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
  { PP_OPEN_BV_ARRAY, "bool-to-bv" },
  { PP_OPEN_BV_SIGN_EXTEND, "bv-sign-extend" },
  { PP_OPEN_BV_ZERO_EXTEND, "bv-zero-extend" },
  { PP_OPEN_BV_EXTRACT, "bv-extract" },
  { PP_OPEN_BV_CONCAT, "bv-concat" },
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
  { PP_OPEN_IS_INT, "is-int" },
  { PP_OPEN_FLOOR, "floor" },
  { PP_OPEN_CEIL, "ceil" },
  { PP_OPEN_ABS, "abs" },
  { PP_OPEN_IDIV, "div" },
  { PP_OPEN_IMOD, "mod" },
  { PP_OPEN_DIVIDES, "divides" },
  { PP_OPEN_TYPE, "type" },
  { PP_OPEN_DEFAULT, "default" },
  { PP_OPEN_ROOT_ATOM, "arith-root-atom" },
  { PP_OPEN_SMT2_STORE, "store" },
  { PP_OPEN_SMT2_AS_CONST, "as const" },
};


/*
 * Table of non-standard blocks
 */
#define NUM_NONSTANDARD_BLOCKS 15

static const pp_nonstandard_block_t nonstandard_block[NUM_NONSTANDARD_BLOCKS] = {
  { PP_OPEN, "", PP_HMT_LAYOUT, 0, 1, 1 },
  { PP_OPEN_PAR, "", PP_HMT_LAYOUT, PP_TOKEN_PAR_MASK, 1, 1 },
  { PP_OPEN_VPAR, "", PP_V_LAYOUT, PP_TOKEN_PAR_MASK, 1, 1 },
  { PP_OPEN_BV_TYPE, "bitvector", PP_H_LAYOUT, PP_TOKEN_DEF_MASK, 0, 0 },
  { PP_OPEN_CONST_DEF, "constant", PP_H_LAYOUT, PP_TOKEN_DEF_MASK, 0, 0 },
  { PP_OPEN_UNINT_DEF, "unint", PP_H_LAYOUT, PP_TOKEN_DEF_MASK, 0, 0 },
  { PP_OPEN_VAR_DEF,   "var", PP_H_LAYOUT, PP_TOKEN_DEF_MASK, 0, 0 },
  { PP_OPEN_FORALL, "forall ", PP_HMT_LAYOUT, 0, 7, 7 },
  { PP_OPEN_EXISTS, "exists ", PP_HMT_LAYOUT, 0, 7, 7 },
  { PP_OPEN_LAMBDA, "lambda ", PP_HMT_LAYOUT, 0, 7, 7 },
  { PP_OPEN_FUNCTION, "function ", PP_V_LAYOUT, PP_TOKEN_PAR_MASK, 1, 1 },
  { PP_OPEN_SMT2_BV_DEC, "_ bv", PP_H_LAYOUT, PP_TOKEN_PAR_MASK, 0, 0 },
  { PP_OPEN_SMT2_BV_TYPE, "_ BitVec", PP_H_LAYOUT, PP_TOKEN_DEF_MASK, 0, 0},
  { PP_OPEN_SMT2_MODEL, "model", PP_T_LAYOUT, PP_TOKEN_DEF_MASK, 2, 2 },
  { PP_OPEN_SMT2_DEF, "define-fun", PP_HMT_LAYOUT, PP_TOKEN_DEF_MASK, 2, 2 },
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

static void build_double(string_buffer_t *b, double x) {
  string_buffer_append_double(b, x);
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

// bitvector constants 0, 1, and -1: n = number of bits
static void build_bv_zero(string_buffer_t *b, uint32_t n) {
  assert(0 < n);

  string_buffer_append_char(b, '0');
  string_buffer_append_char(b, 'b');
  do {
    string_buffer_append_char(b, '0');
    n --;
  } while (n > 0);
  string_buffer_close(b);
}

static void build_bv_one(string_buffer_t *b, uint32_t n) {
  assert(0 < n);

  string_buffer_append_char(b, '0');
  string_buffer_append_char(b, 'b');
  while (n > 1) {
    string_buffer_append_char(b, '0');
    n --;
  }
  string_buffer_append_char(b, '1');
  string_buffer_close(b);
}

static void build_bv_minus_one(string_buffer_t *b, uint32_t n) {
  assert(0 < n);

  string_buffer_append_char(b, '0');
  string_buffer_append_char(b, 'b');
  do {
    string_buffer_append_char(b, '1');
    n --;
  } while (n > 0);
  string_buffer_close(b);
}

// quoted string
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

// smt2 variant of build_rational for integers converted to real
static void build_smt2_integer_as_real(string_buffer_t *b, rational_t *q) {
  string_buffer_append_rational(b, q);
  string_buffer_append_char(b, '.');
  string_buffer_append_char(b, '0');
  string_buffer_close(b);
}

// quoted identifier
static void build_qid(string_buffer_t *b, const char *prefix, int32_t index, char quote[2]) {
  if (quote[0] != '\0') {
    string_buffer_append_char(b, quote[0]);
  }
  string_buffer_append_string(b, prefix);
  string_buffer_append_int32(b, index);
  if (quote[1] != '\0') {
    string_buffer_append_char(b, quote[1]);
  }
  string_buffer_close(b);
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
  case PP_DOUBLE_ATOM:
    build_double(buffer, atm->data.dbl);
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
  case PP_BV_ZERO_ATOM:
    build_bv_zero(buffer, atm->data.u32);
    s = buffer->data;
    break;
  case PP_BV_ONE_ATOM:
    build_bv_one(buffer, atm->data.u32);
    s = buffer->data;
    break;
  case PP_BV_NEGONE_ATOM:
    build_bv_minus_one(buffer, atm->data.u32);
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
  case PP_SMT2_INTEGER_AS_REAL:
    build_smt2_integer_as_real(buffer, &atm->data.rat);
    s = buffer->data;
    break;
  case PP_SMT2_QID_ATOM:
    build_qid(buffer, atm->data.qid.prefix, atm->data.qid.index, atm->data.qid.quote);
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
 * Flush: print everything pending
 * - if the printer is writing to file, print a newline
 * - reset the line counter to 0
 */
void flush_yices_pp(yices_pp_t *printer) {
  bool nl;

  nl = is_stream_pp(&printer->pp);
  flush_pp(&printer->pp, nl);
}

/*
 * Extract the string constructed by printer
 * - printer must be initialized for a string (i.e., with file = NULL)
 * - this must be called after flush
 * - the string length is stored in *len
 * - the returned string must be deleted when no-longer needed using free.
 */
char *yices_pp_get_string(yices_pp_t *printer, uint32_t *len) {
  return pp_get_string(&printer->pp, len);
}



/*
 * Flush then delete a pretty printer
 * - if flush is true, print everything pending 
 * - then free all memory used
 */
void delete_yices_pp(yices_pp_t *printer, bool flush) {
  if (flush) {
    flush_yices_pp(printer);
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

void pp_algebraic(yices_pp_t *printer, void *a) {
#ifdef HAVE_MCSAT
  pp_atom_t *atom;
  void *tk;
  string_buffer_t *buffer;
  uint32_t n;

  double a_value = lp_algebraic_number_to_double(a);

  buffer = &printer->buffer;
  assert(string_buffer_length(buffer) == 0);
  build_double(buffer, a_value);
  n = string_buffer_length(buffer);
  string_buffer_reset(buffer);

  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n, PP_DOUBLE_ATOM);
  atom->data.dbl = a_value;
  pp_push_token(&printer->pp, tk);
#endif
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
 * Bitvector constants: 0, 1, -1
 */
void pp_bv_zero(yices_pp_t *printer, uint32_t n) {
  pp_atom_t *atom;
  void *tk;

  assert(0 < n);
  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n+2, PP_BV_ZERO_ATOM);
  atom->data.u32 = n;

  pp_push_token(&printer->pp, tk);
}

void pp_bv_one(yices_pp_t *printer, uint32_t n) {
  pp_atom_t *atom;
  void *tk;

  assert(0 < n);
  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n+2, PP_BV_ONE_ATOM);
  atom->data.u32 = n;

  pp_push_token(&printer->pp, tk);
}

void pp_bv_minus_one(yices_pp_t *printer, uint32_t n) {
  pp_atom_t *atom;
  void *tk;

  assert(0 < n);
  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n+2, PP_BV_NEGONE_ATOM);
  atom->data.u32 = n;

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
 * - close_quote = character after the string (or '\0' if nothing needed)
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
 * Variant of pp_rational for SMT2.
 * - if X have value 10 in a model but X is real variable, then we have to
 *   print the value as 10.0 (because 10 would be confusing somehow!!!).
 */
void pp_smt2_integer_as_real(yices_pp_t *printer, rational_t *q) {
  pp_atom_t *atom;
  void *tk;
  string_buffer_t *buffer;
  uint32_t n;

  assert(q_is_integer(q));

  buffer = &printer->buffer;
  assert(string_buffer_length(buffer) == 0);
  build_rational(buffer, q);
  n = string_buffer_length(buffer) + 2;
  string_buffer_reset(buffer);

  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n, PP_SMT2_INTEGER_AS_REAL);
  q_init(&atom->data.rat);
  q_set(&atom->data.rat, q);

  pp_push_token(&printer->pp, tk);
}



/*
 * Quoted id:
 * - same as pp_id but with open and close quote
 *
 * Examples: pp_quoted_id(printer, "x!", 20, '|', '|') will print |x!20|
 */
void pp_quoted_id(yices_pp_t *printer, const char *prefix, int32_t id, char open_quote, char close_quote) {
  pp_atom_t *atom;
  void *tk;
  string_buffer_t *buffer;
  uint32_t n;

  // get the token size using buffer
  buffer = &printer->buffer;
  assert(string_buffer_length(buffer) == 0);
  build_id(buffer, prefix, id);
  n = string_buffer_length(buffer) + (open_quote != '\0') + (close_quote != '\0');
  string_buffer_reset(buffer);

  atom = new_atom(printer);
  tk = init_atomic_token(&atom->tk, n, PP_SMT2_QID_ATOM);
  atom->data.qid.prefix = prefix;
  atom->data.qid.index = id;
  atom->data.qid.quote[0] = open_quote;
  atom->data.qid.quote[1] = close_quote;

  pp_push_token(&printer->pp, tk);
}


/*
 * PRINT UTILITIES BORROWED FROM SMT2 PRINTER
 */

/*
 * Default printer for bitvector
 */
void pp_bitvector(yices_pp_t *printer, value_bv_t *b) {
  pp_smt2_bv(printer, b->data, b->nbits);
}

/*
 * For uninterpreted constants: always print an abstract name
 */
void pp_unint_name(yices_pp_t *printer, value_t c) {
  pp_id(printer, "@const_", c);
}

/*
 * Function: always use a default name, even if fun has a name
 */
void pp_fun_name(yices_pp_t *printer, value_t c) {
  pp_id(printer, "@fun_", c);
}

/*
 * Format to display a function:
 * (function <name>
 *   (type (-> tau_1 ... tau_n sigma))
 *   (= (<name> x_1 ... x_n) y_1)
 *    ...
 *   (default z))
 */
void pp_function_header(yices_pp_t *printer, value_table_t *table, value_t c, type_t tau) {
  pp_open_block(printer, PP_OPEN_FUNCTION);
  pp_id(printer, "@fun_", c);
  pp_open_block(printer, PP_OPEN_TYPE);
  pp_type(printer, table->type_table, tau);
  pp_close_block(printer, true);
}

/*
 * Print the function c
 * - if show_default is true, also print the default falue
 */
void pp_function(yices_pp_t *printer, value_table_t *table, value_t c, bool show_default) {
  value_fun_t *fun;
  value_map_t *mp;
  uint32_t i, n;
  uint32_t j, m;

  assert(0 <= c && c < table->nobjects && table->kind[c] == FUNCTION_VALUE);
  fun = table->desc[c].ptr;

  pp_function_header(printer, table, c, fun->type);

  m = fun->arity;
  n = fun->map_size;
  for (i=0; i<n; i++) {
    pp_open_block(printer, PP_OPEN_EQ);  // (=
    pp_open_block(printer, PP_OPEN_PAR); // (fun
    pp_fun_name(printer, c);

    mp = vtbl_map(table, fun->map[i]);
    assert(mp->arity == m);
    for (j=0; j<m; j++) {
      pp_object(printer, table, mp->arg[j]);
    }
    pp_close_block(printer, true); // close of (fun ...
    pp_object(printer, table, mp->val);
    pp_close_block(printer, true); // close (= ..
  }

  if (show_default && !is_unknown(table, fun->def)) {
    pp_open_block(printer, PP_OPEN_DEFAULT); // (default
    pp_object(printer, table, fun->def);
    pp_close_block(printer, true); // close (default ..
  }
  pp_close_block(printer, true); // close (function ...
}

/*
 * Expand update c and print it as a function
 * - the name "@fun_c"
 * - if show_default is true, also print the default value
 */
void normalize_and_pp_update(yices_pp_t *printer, value_table_t *table, value_t c, bool show_default) {
  map_hset_t *hset;
  value_map_t *mp;
  value_t def;
  type_t tau;
  uint32_t i, j, n, m;

  // build the mapping for c in hset1
  vtbl_expand_update(table, c, &def, &tau);
  hset = table->hset1;
  assert(hset != NULL);

  pp_function_header(printer, table, c, tau);

  /*
   * hset->data contains an array of mapping objects
   * hset->nelems = number of elements in hset->data
   */
  m = vtbl_update(table, c)->arity;
  n = hset->nelems;
  for (i=0; i<n; i++) {
    pp_open_block(printer, PP_OPEN_EQ);
    pp_open_block(printer, PP_OPEN_PAR);
    pp_fun_name(printer, c);

    mp = vtbl_map(table, hset->data[i]);
    assert(mp->arity == m);
    for (j=0; j<m; j++) {
      pp_object(printer, table, mp->arg[j]);
    }
    pp_close_block(printer, true); // close (name arg[0] ... arg[m-1])
    pp_object(printer, table, mp->val);
    pp_close_block(printer, true); // close (=
  }

  if (show_default && !is_unknown(table, def)) {
    pp_open_block(printer, PP_OPEN_DEFAULT);
    pp_object(printer, table, def);
    pp_close_block(printer, true);
  }
  pp_close_block(printer, true);  // close the (function ...
}

/*
 * Print object c on stream f
 *
 * There's no support for tuples or mappings in SMT2. They should never occur here.
 */
void pp_object(yices_pp_t *printer, value_table_t *table, value_t c) {
  assert(0 <= c && c < table->nobjects);

  switch (table->kind[c]) {
  case UNKNOWN_VALUE:
    pp_string(printer, "???");
    break;
  case BOOLEAN_VALUE:
    pp_bool(printer, table->desc[c].integer);
    break;
  case RATIONAL_VALUE:
    pp_rational(printer, &table->desc[c].rational);
    break;
  case ALGEBRAIC_VALUE:
    pp_algebraic(printer, table->desc[c].ptr);
    break;
  case BITVECTOR_VALUE:
    pp_bitvector(printer, table->desc[c].ptr);
    break;
  case UNINTERPRETED_VALUE:
    pp_unint_name(printer, c);
    break;
  case FUNCTION_VALUE:
    pp_fun_name(printer, c);
    pp_function(printer, table, c, true);
    break;
  case UPDATE_VALUE:   // updates are treated like functions
    pp_fun_name(printer, c);
    normalize_and_pp_update(printer, table, c, true);
    break;

  case MAP_VALUE:
  case TUPLE_VALUE:
  default:
    assert(false);
  }
}

/*
 * Print object c on FILE f
 *
 */
void pp_value(FILE *f, value_table_t *table, value_t c) {
  yices_pp_t printer;
  pp_area_t area = {  40, UINT32_MAX, 0, false, false,  };
  init_yices_pp(&printer, f, &area, PP_VMODE, 0);

  pp_object(&printer, table, c);

  delete_yices_pp(&printer, true);
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

