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
 * PRETTY PRINTER FOR YICES TYPES AND TERMS
 */

#ifndef __YICES_PP_H
#define __YICES_PP_H

#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>
#include <gmp.h>

#include "io/pretty_printer.h"
#include "terms/rationals.h"
#include "utils/object_stores.h"
#include "utils/string_buffers.h"
#include "model/concrete_values.h"


/*
 * ATOMIC OBJECTS
 */

/*
 * Each atomic tokens stores a basic object to be printed as
 * a single string. It consists of a pp_atomic_token prefix +
 * extra data that describes the actual object to be printed.
 * The user_tag field in the prefix stores the object type.
 */
typedef enum pp_atom_type {
  PP_CHAR_ATOM,       // content = a single char
  PP_STRING_ATOM,     // content = string terminated by '\0'
  PP_ID_ATOM,         // identifier = concatenation of a string and an index
  PP_VARID_ATOM,      // variant id = concatenation of a string, '!', and an index
  PP_TRUE_ATOM,       // true
  PP_FALSE_ATOM,      // false
  PP_INT32_ATOM,      // signed integer
  PP_UINT32_ATOM,     // unsigned integer
  PP_DOUBLE_ATOM,     // double number
  PP_RATIONAL_ATOM,   // rational
  PP_BV64_ATOM,       // bitvector constant stored in a 64bit unsigned integer
  PP_BV_ATOM,         // bitvector constant stored in an array of words
  PP_BV_ZERO_ATOM,    // bitvector constant 0b00...00
  PP_BV_ONE_ATOM,     // bitvector constant 0b00...01
  PP_BV_NEGONE_ATOM,  // bitvector constant 0b11...11
  PP_QSTRING_ATOM,    // content = string with open and close quotes
  PP_SMT2_BV64_ATOM,  // like PP_BV64_ATOM but with SMT2 #b prefix
  PP_SMT2_BV_ATOM,    // like PP_BV_ATOM but with SMT2 prefix
  PP_SMT2_INTEGER_AS_REAL,   // print <integer>.0
  PP_SMT2_QID_ATOM,   // like PP_ID_ATOM with quotes
} pp_atom_type_t;

#define NUM_PP_ATOMS ((uint32_t) (PP_QID_ATOM+1))


/*
 * Descriptors of STRING, ID, BV, BV64 atoms
 * - for all atoms that have a string component, we optionally
 *   make a clone of the string  when the atom is created.
 * - if so, we set cloned to true.
 * - if not, we set cloned to false.
 * - same convention for the integer array bv in pp_bv_s
 */
typedef struct pp_string_s  {
  const char *string;
  bool cloned;
} pp_string_t;

typedef struct pp_id_s {
  const char *prefix;
  int32_t index;
  bool cloned;
} pp_id_t;

typedef struct pp_bv64_s {
  uint64_t bv;
  uint32_t nbits;
} pp_bv64_t;

typedef struct pp_bv_s {
  uint32_t *bv;
  uint32_t nbits;
  bool cloned;
} pp_bv_t;


/*
 * Descriptor of quoted string atoms
 * - quote[0] = open quote
 * - quote[1] = close_quote
 * - str = what's between the quotes
 */
typedef struct pp_qstr_s {
  const char *str;
  char quote[2];
  bool cloned;
} pp_qstr_t;


/*
 * Descriptor of quoted id
 */
typedef struct pp_qid_s {
  const char *prefix;
  int32_t index;
  char quote[2];
  bool cloned;
} pp_qid_t;


/*
 * Full atomic token
 */
typedef struct pp_atom_s {
  pp_atomic_token_t tk; // prefix defined in pretty_printer.h
  union {
    char c;
    pp_string_t string;
    pp_id_t id;
    int32_t i32;
    uint32_t u32;
    double dbl;
    rational_t rat;
    pp_bv64_t bv64;
    pp_bv_t bv;
    pp_qstr_t qstr;
    pp_qid_t qid;
  } data;
} pp_atom_t;



/*
 * OPEN-BLOCK TOKENS
 */

/*
 * Each open-block token is defined by an identifier.
 * For each identifier, the module maintains the following
 * information in internal tables:
 * - string label
 * - label size
 * - preferred format for that block
 * - indentation and short indentation
 * - two boolean flags (sep allowed + parenthesis for that block)
 */

// list of open-block identifiers
typedef enum {
  PP_OPEN,               // empty label, no parenthesis, HMT layout
  PP_OPEN_PAR,           // empty label, open parenthesis, HMT layout
  PP_OPEN_VPAR,          // empty label, open parenthesis, V layout

  PP_OPEN_BV_TYPE,
  PP_OPEN_FF_TYPE,
  PP_OPEN_FUN_TYPE,
  PP_OPEN_TUPLE_TYPE,

  PP_OPEN_ITE,
  PP_OPEN_UPDATE,
  PP_OPEN_TUPLE,
  PP_OPEN_SELECT,
  PP_OPEN_EQ,
  PP_OPEN_NEQ,
  PP_OPEN_DISTINCT,
  PP_OPEN_FORALL,
  PP_OPEN_EXISTS,
  PP_OPEN_LAMBDA,
  PP_OPEN_NOT,
  PP_OPEN_OR,
  PP_OPEN_AND,
  PP_OPEN_XOR,
  PP_OPEN_IMPLIES,
  PP_OPEN_BIT,
  PP_OPEN_PROD,
  PP_OPEN_POWER,
  PP_OPEN_SUM,
  PP_OPEN_DIV,
  PP_OPEN_MINUS,
  PP_OPEN_GE,
  PP_OPEN_LT,
  PP_OPEN_ROOT_ATOM,

  PP_OPEN_BV_ARRAY,
  PP_OPEN_BV_SIGN_EXTEND,
  PP_OPEN_BV_ZERO_EXTEND,
  PP_OPEN_BV_EXTRACT,
  PP_OPEN_BV_CONCAT,
  PP_OPEN_BV_SUM,
  PP_OPEN_BV_PROD,
  PP_OPEN_BV_POWER,
  PP_OPEN_BV_DIV,
  PP_OPEN_BV_REM,
  PP_OPEN_BV_SDIV,
  PP_OPEN_BV_SREM,
  PP_OPEN_BV_SMOD,
  PP_OPEN_BV_SHL,
  PP_OPEN_BV_LSHR,
  PP_OPEN_BV_ASHR,
  PP_OPEN_BV_GE,
  PP_OPEN_BV_LT,
  PP_OPEN_BV_SGE,
  PP_OPEN_BV_SLT,

  // more arithmetic stuff
  PP_OPEN_IS_INT,
  PP_OPEN_FLOOR,
  PP_OPEN_CEIL,
  PP_OPEN_ABS,
  PP_OPEN_IDIV,
  PP_OPEN_IMOD,
  PP_OPEN_DIVIDES,

  // blocks used in pp_model
  PP_OPEN_FUNCTION,   // (function ...)
  PP_OPEN_TYPE,       // (type ..)
  PP_OPEN_DEFAULT,    // (default x)

  PP_OPEN_CONST_DEF,  // (constant i of <type>)
  PP_OPEN_UNINT_DEF,  // (unint i of <type>)
  PP_OPEN_VAR_DEF,    // (var i of <type>)

  // more for the SMT2 model syntax
  PP_OPEN_SMT2_BV_DEC, // (_ bv... ..)
  PP_OPEN_SMT2_BV_TYPE, // (_ BitVec ...)
  PP_OPEN_SMT2_FF_DEC, // (_ ff... ..)
  PP_OPEN_SMT2_FF_TYPE, // (_ FiniteField ...)
  PP_OPEN_SMT2_MODEL,   // (model ...)
  PP_OPEN_SMT2_DEF,     // (define-fun ...)
  PP_OPEN_SMT2_STORE,   // (store <array> <index> <value>)
  PP_OPEN_SMT2_AS_CONST,  // (as const <type> <value>)  (for constant arrays. type is the array type).
  PP_OPEN_SMT2_AS,        // (as <identifier> <type> )
} pp_open_type_t;

#define NUM_PP_OPENS ((uint32_t) (PP_OPEN_SMT2_AS + 1))



/*
 * CLOSE-BLOCK TOKENS
 */

/*
 * Two versions: close with a parenthesis or close with nothing
 */
typedef enum {
  PP_CLOSE,
  PP_CLOSE_PAR,
} pp_close_type_t;




/*
 * FULL PRETTY PRINTER
 */

/*
 * - pp: pretty printer object
 * - open_store: for allocation of open-block tokens
 * - atom_store: for allocation of atomic tokens
 * - two statically allocated close tokens
 * - a string buffer for conversion of atoms to strings
 */
typedef struct yices_pp_s {
  pp_t pp;
  object_store_t open_store;
  object_store_t atom_store;
  pp_close_token_t close_nopar;
  pp_close_token_t close_par;
  void *close[2];  // close[0] = nopar, close[1] = par
  string_buffer_t buffer;
} yices_pp_t;




/*
 * Initialize the internal table of open-token descriptors
 * - this must be called first.
 */
extern void init_yices_pp_tables(void);

/*
 * Initialize a pretty printer
 * - file = output file (must be NULL or a stream open for write)
 * - area = display area (cf. pretty_printer.h) 
 * - mode = initial print mode (cf. pretty printer.h)
 * - indent = initial indentation
 *
 * If file is NULL, then the pretty printer is initialized for 
 * a string buffer. Otherwise, it writes to file.
 *
 * If area is NULL, then the default is used (cf. pretty_printer.h)
 */
extern void init_yices_pp(yices_pp_t *printer, FILE *file, pp_area_t *area,
                          pp_print_mode_t mode, uint32_t indent);


/*
 * Variant: use default mode and indent
 */
static inline void init_default_yices_pp(yices_pp_t *printer, FILE *file, pp_area_t *area) {
  init_yices_pp(printer, file, area, PP_VMODE, 0);
}


/*
 * Flush: print everything pending + a newline
 * - then reset the line counter to 0
 */
extern void flush_yices_pp(yices_pp_t *printer);


/*
 * Extract the string constructed by printer
 * - printer must be initialized for a string (i.e., with file = NULL)
 * - this must be called after flush
 * - the string length is stored in *len
 * - the returned string must be deleted when no-longer needed using free.
 */
extern char *yices_pp_get_string(yices_pp_t *printer, uint32_t *len);


/*
 * Delete a pretty printer
 * - if flush is true, print everything pending + a newline
 * - then free all memory used
 */
extern void delete_yices_pp(yices_pp_t *printer, bool flush);


/*
 * Check for saturation: when this is true, we should stop sending tokens
 */
static inline bool yices_pp_is_full(yices_pp_t *printer) {
  return pp_is_full(&printer->pp);
}


/*
 * Get the print depth = number of open blocks sent to the printer
 */
static inline uint32_t yices_pp_depth(yices_pp_t *printer) {
  return pp_depth(&printer->pp);
}


/*
 * Check for print error and error code
 */
static inline bool yices_pp_print_failed(yices_pp_t *printer) {
  return writer_failed(&printer->pp.printer.writer);
}

static inline int yices_pp_errno(yices_pp_t *printer) {
  return writer_errno(&printer->pp.printer.writer);
}



/*
 * PRINT ATOMS
 */

/*
 * Safe atoms:
 * - pp_rational make an internal copy of q
 * - pp_mpz, pp_mpq: the z or the q is translated to a rational
 * - pp_algebraic: converted to a double
 */
extern void pp_char(yices_pp_t *printer, char c);
extern void pp_bool(yices_pp_t *printer, bool tt);
extern void pp_int32(yices_pp_t *printer, int32_t x);
extern void pp_uint32(yices_pp_t *printer, uint32_t x);
extern void pp_mpz(yices_pp_t *printer, mpz_t z);
extern void pp_mpq(yices_pp_t *printer, mpq_t q);
extern void pp_rational(yices_pp_t *printer, rational_t *q);
extern void pp_bv64(yices_pp_t *printer, uint64_t bv, uint32_t n);
extern void pp_finitefield(yices_pp_t *printer, value_ff_t *v);
extern void pp_algebraic(yices_pp_t *printer, void *a);

/*
 * String and bv atoms without cloning
 * - pp_id(printer, prefix, id): prints <prefix><id>
 *   (example, pp_id(printer, "tau_", 23) prints "tau_23")
 * - pp_varid(printer, prefix, id): prints <prefix>!<id>
 * - for pp_bv64 and pp_bv, n is the number of bits (n must be positive)
 *
 * Function pp_string does not make a copy of the string s so s must
 * remain valid until the printer is deleted. Same thing for prefix
 * function in pp_id. Function pp_bv does not make a copy
 * of the word array *bv either.
 */
extern void pp_string(yices_pp_t *printer, const char *s);
extern void pp_id(yices_pp_t *printer, const char *prefix, int32_t id);
extern void pp_varid(yices_pp_t *printer, const char *prefix, int32_t id);
extern void pp_bv(yices_pp_t *printer, uint32_t *bv, uint32_t n);

/*
 * String and bv atoms with cloning
 * - these print the same  thing as above but they make an internal
 *   copy of the string or bv array.
 */
extern void pp_clone_string(yices_pp_t *printer, const char *s);
extern void pp_clone_id(yices_pp_t *printer, const char *prefix, int32_t id);
extern void pp_clone_varid(yices_pp_t *printer, const char *prefix, int32_t id);
extern void pp_clone_bv(yices_pp_t *printer, uint32_t *bv, uint32_t n);



/*
 * Print 0b0...0, 0b0...01, or 0b1...1: n = number of bits
 */
extern void pp_bv_zero(yices_pp_t *printer, uint32_t n);
extern void pp_bv_one(yices_pp_t *printer, uint32_t n);
extern void pp_bv_minus_one(yices_pp_t *printer, uint32_t n);


/*
 * Separator token: same as a string, but the pretty printer
 * does not add spaces before and after the token
 */
extern void pp_separator(yices_pp_t *printer, const char *s);

/*
 * Quoted string:
 * - open_quote = character before the string (or '\0' if nothing needed)
 * - close_quote = character after the string (or '\0' if nothing needed)
 *
 * Examples
 *   pp_qstring(printer, '"', '"', "abcde") will print "abcde" (quotes included)
 *   pp_qstring(printer, '\'', '\0', "abcde") will print 'abcde
 *
 * The default version does not make a copy of s, so s must remain valid until
 * the printer is flushed. The clone  version makes an internal copy of s.
 */
extern void pp_qstring(yices_pp_t *printer, char open_quote, char close_quote, const char *s);
extern void pp_clone_qstring(yices_pp_t *printer, char open_quote, char close_quote, const char *s);

/*
 * Quoted id:
 * - same as pp_id but with open and close quote
 *
 * Examples: pp_quoted_id(printer, "x!", 20, '|', '|') will print |x!20|
 *
 * The default version does not make a copy of prefix, so prefix must remain valid until
 * the printer is flushed. The clone  version makes an internal copy of prefix.
 */
extern void pp_quoted_id(yices_pp_t *printer, const char *prefix, int32_t id, char open_quote, char close_quote);
extern void pp_clone_quoted_id(yices_pp_t *printer, const char *prefix, int32_t id, char open_quote, char close_quote);

/*
 * Variant(s) for SMT2 atoms
 * - pp_smt2_bv uses the prefix #b instead of 0b
 *
 * pp_smt2_bv: does not make a copy of bv.
 * pp_clone_smt2_bv: makes an internal copy.
 */
extern void pp_smt2_bv64(yices_pp_t *printer, uint64_t bv, uint32_t n);
extern void pp_smt2_bv(yices_pp_t *printer, uint32_t *bv, uint32_t n);
extern void pp_clone_smt2_bv(yices_pp_t *printer, uint32_t *bv, uint32_t n);

/*
 * Another SMT2 special
 * - print an integer converted to real as in 12.0 instead of 12
 * - the value is provided as a rational but the denominator must be one.
 */
extern void pp_smt2_integer_as_real(yices_pp_t *printer, rational_t *q);


/*
 * PRINT UTILITIES BORROWED FROM SMT2 PRINTER
 */

/*
 * Default printer for bitvector
 */
extern void pp_bitvector(yices_pp_t *printer, value_bv_t *b);

/*
 * For uninterpreted constants: always print an abstract name
 */
extern void pp_unint_name(yices_pp_t *printer, value_t c);

/*
 * Function: always use a default name, even if fun has a name
 */
extern void pp_fun_name(yices_pp_t *printer, value_t c);

/*
 * Format to display a function:
 * (function <name>
 *   (type (-> tau_1 ... tau_n sigma))
 *   (= (<name> x_1 ... x_n) y_1)
 *    ...
 *   (default z))
 */
extern void pp_function_header(yices_pp_t *printer, value_table_t *table, value_t c, type_t tau);

/*
 * Print the function c
 * - if show_default is true, also print the default falue
 */
extern void pp_function(yices_pp_t *printer, value_table_t *table, value_t c, bool show_default);

/*
 * Expand update c and print it as a function
 * - the name "@fun_c"
 * - if show_default is true, also print the default value
 */
extern void normalize_and_pp_update(yices_pp_t *printer, value_table_t *table, value_t c, bool show_default);

/*
 * Print object c on stream f
 *
 * There's no support for tuples or mappings in SMT2. They should never occur here.
 */
extern void pp_object(yices_pp_t *printer, value_table_t *table, value_t c);

/*
 * Print object c on FILE f
 *
 */
extern void pp_value(FILE *f, value_table_t *table, value_t c);



/*
 * OPEN AND CLOSE BLOCK
 */

/*
 * Start an block given the open-block id
 */
extern void pp_open_block(yices_pp_t *printer, pp_open_type_t id);

/*
 * Close a block
 * - par: true if a parenthesis is required
 *        false to close and print nothing
 */
extern void pp_close_block(yices_pp_t *printer, bool par);


#endif /* __YICES_PP_H */
