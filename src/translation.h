/*
 * Translation table:
 * - map object ids in the global term table to an internal code
 * - the mapping is stored in three tables:
 *   - term2code[t] = internalization of a term t
 *   - arith_var2code[x] = internalization of an arithmetic variable x
 *   - bv_var2code[b] = internalization of a bit vector variable b
 */

#ifndef __TRANSLATION_H
#define __TRANSLATION_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "internalization_map.h"

#include "terms.h"
#include "smt_core.h"
#include "egraph.h"


/*
 * Internalization code for terms
 * - a term t can be mapped to a theory variable, a literal, or an 
 *   egraph term-occurrence.
 * - we encode the mapping as a 32bit code stored in term_map.
 *
 * - If the code of is negative, t is not mapped to anything yet,
 *   otherwise the code is of the form [0 b30 .... b2 b1 b0].
 *
 * - If b0 == 0, the code denotes the term occurrence [0 0 b30 ... b1].
 *   The term occurrence is the concatenation of an eterm id [0 0 0 b30 ... b2] 
 *   and the polarity bit b1. For a non-boolean term, b1 is always 0.
 *
 * - If b0 == 1,  the code is a theory variable or a literal, depending on 
 *   the type of t.
 *   - type = BOOL: 
 *      the code denotes literal [0 0 b30 ... b2 b1] 
 *      (i.e., boolean variable [0 0 0 b30 ...b2] + polarity bit b1).
 *   - type = INT or REAL:
 *      t is mapped to the variable [0 0 b30 ... b1] in the arithmetic solver
 *   - type = (BITVECTOR k)
 *      t is mapped to the variable [0 0 b30 ... b1] in the bitvector solver
 *
 * Internalization code for arithmetic and bitvector variables:
 * - If the code for x is nil, x is not mapped to anything yet, otherwise
 *   the code is a variable index in the arithmetic or bitvector solver.
 */

/*
 * Conversion of literal, term occurrence, or theory variable to
 * internalization codes.
 */
typedef int32_t icode_t;

static inline icode_t occ2code(occ_t x) {
  assert(x >= 0);
  return x << 1;
}

static inline icode_t eterm2code(eterm_t t) {
  assert(t >= 0);
  return t << 2; // same as occ2code(pos_occ(t))
}

static inline icode_t literal2code(literal_t l) {
  assert(l >= 0);
  return (l<<1) | 1;
}

static inline icode_t bvar2code(bvar_t v) {
  return literal2code(pos_lit(v));
}


static inline icode_t arithvar2code(arith_var_t x) {
  assert(x >= 0);
  return (x<<1) | 1;
}

static inline icode_t bvvar2code(bv_var_t b) {
  assert(b >= 0);
  return (b<<1) | 1;
}

static inline icode_t var2code(thvar_t x) {
  assert(x >= 0);
  return (x<<1) | 1;
}

/*
 * Code for true or false egraph occurrences
 */
static inline icode_t bool2code(bool val) {
  return occ2code(bool2occ(val));
}



/*
 * Checks on code c and conversion to literal, theory variable, or
 * term occurrence.
 */
static inline bool code_is_valid(icode_t c) {
  return c >= 0;
}

static inline bool code_is_eterm(icode_t c) {
  assert(c >= 0);
  return (c & 1) == 0;
}

static inline bool code_is_var(icode_t c) {
  assert(c >= 0);
  return (c & 1) == 1;
}

static inline occ_t code2occ(icode_t c) {
  assert(code_is_eterm(c));
  return c>>1;
}

static inline eterm_t code2eterm(icode_t c) {
  assert(code_is_eterm(c));
  return c>>2;
}

static inline literal_t code2literal(icode_t c) {
  assert(code_is_var(c));
  return c>>1;
}

static inline bvar_t code2bvar(icode_t c) {
  assert(code_is_var(c));
  return c>>2;
}

static inline arith_var_t code2arithvar(icode_t c) {
  assert(code_is_var(c));
  return c>>1;
}

static inline bv_var_t code2bvvar(icode_t c) {
  assert(code_is_var(c));
  return c>>1;
}

static inline thvar_t code2var(icode_t c) {
  assert(code_is_var(c));
  return c>>1;
}




/*
 * Translator object: three maps
 */
typedef struct translator_s {
  itable_t term_map;
  itable_t arith_map;
  itable_t bv_map;
} translator_t;
 



/****************
 *  OPERATIONS  *
 ***************/

/*
 * Initialize translator:
 * - t_size = initial size of term_map
 * - a_size = initial size of arih_map
 * - b_size = initial size of bv_map
 * (0 means use the default size, defined in internalization_map.h)
 */
static inline void init_translator(translator_t *trans, uint32_t t_size, uint32_t a_size, uint32_t b_size) {
  init_itable(&trans->term_map, t_size);
  init_itable(&trans->arith_map, a_size);
  init_itable(&trans->bv_map, b_size);
}

/*
 * Delete all maps
 */
static inline void delete_translator(translator_t *trans) {
  delete_itable(&trans->term_map);
  delete_itable(&trans->arith_map);
  delete_itable(&trans->bv_map);
}

/*
 * Reset
 */
static inline void reset_translator(translator_t *trans) {
  reset_itable(&trans->term_map);
  reset_itable(&trans->arith_map);
  reset_itable(&trans->bv_map);
}

/*
 * Push: start new scope
 */
static inline void translator_push(translator_t *trans) {
  itable_push(&trans->term_map);
  itable_push(&trans->arith_map);
  itable_push(&trans->bv_map);
}

/*
 * Pop: return to previous scope.
 */
static inline void translator_pop(translator_t *trans) {
  itable_pop(&trans->term_map);
  itable_pop(&trans->arith_map);
  itable_pop(&trans->bv_map);
}




/*
 * TERMS
 */

/*
 * Get code for term t
 */
static inline icode_t code_of_term(translator_t *trans, term_t t) {
  return itable_get(&trans->term_map, t);
}

static inline occ_t occ_of_term(translator_t *trans, term_t t) {
  return code2occ(code_of_term(trans, t));
}

static inline occ_t eterm_of_term(translator_t *trans, term_t t) {
  return code2eterm(code_of_term(trans, t));
}

static inline literal_t literal_of_term(translator_t *trans, term_t t) {
  return code2literal(code_of_term(trans, t));
}

static inline bvar_t bvar_of_term(translator_t *trans, term_t t) {
  return code2bvar(code_of_term(trans, t));
}

static inline arith_var_t arithvar_of_term(translator_t *trans, term_t t) {
  return code2arithvar(code_of_term(trans, t));
}

static inline bv_var_t bvvar_of_term(translator_t *trans, term_t t) {
  return code2bvvar(code_of_term(trans, t));
}


/*
 * Size of the term mapping (1 + index of the last term mapped to something
 * or colored black or grey)
 */
static inline uint32_t number_of_terms(translator_t *trans) {
  return itable_num_elements(&trans->term_map);
}

/*
 * Check whether t is mapped to true_occ or false_occ
 */
static inline bool term_mapped_to_true(translator_t *trans, term_t t) {
  return code_of_term(trans, t) == occ2code(true_occ);
}

static inline bool term_mapped_to_false(translator_t *trans, term_t t) {
  return code_of_term(trans, t) == occ2code(false_occ);
}


/*
 * Put a mark on term t
 */
static inline void put_term_mark(translator_t *trans, term_t t) {
  itable_mark(&trans->term_map, t);
}


/*
 * Set/reset the color of term t
 */
static inline void mark_term_grey(translator_t *trans, term_t t) {
  itable_mark_grey(&trans->term_map, t);
}

static inline void mark_term_black(translator_t *trans, term_t t) {
  itable_mark_black(&trans->term_map, t);
}

static inline void clr_term_color(translator_t *trans, term_t t) {
  itable_clr_mark(&trans->term_map, t);
}


/*
 * Check the color of term t
 */
static inline bool term_is_white(translator_t *trans, term_t t) {
  return itable_is_white(&trans->term_map, t);
}

static inline bool term_is_grey(translator_t *trans, term_t t) {
  return itable_is_grey(&trans->term_map, t);
}

static inline bool term_is_black(translator_t *trans, term_t t) {
  return itable_is_black(&trans->term_map, t);
}



/*
 * Map term t to a code
 * - the current mapping of t must be nil or mark
 * - c must be != nil
 */
static inline void map_term_to_code(translator_t *trans, term_t t, icode_t c) {
  itable_map(&trans->term_map, t, c);
}

static inline void map_term_to_occ(translator_t *trans, term_t t, occ_t x) {
  map_term_to_code(trans, t, occ2code(x));
}

static inline void map_term_to_eterm(translator_t *trans, term_t t, eterm_t u) {
  map_term_to_code(trans, t, eterm2code(u));
}

static inline void map_term_to_literal(translator_t *trans, term_t t, literal_t l) {
  map_term_to_code(trans, t, literal2code(l));
}

static inline void map_term_to_bvar(translator_t *trans, term_t t, bvar_t v) {
  map_term_to_code(trans, t, bvar2code(v));
}

static inline void map_term_to_arithvar(translator_t *trans, term_t t, arith_var_t x) {
  map_term_to_code(trans, t, arithvar2code(x));
}

static inline void map_term_to_bvvar(translator_t *trans, term_t t, bv_var_t b) {
  map_term_to_code(trans, t, bvvar2code(b));
}

static inline void map_term_to_bool(translator_t *trans, term_t t, bool val) {
  map_term_to_code(trans, t, bool2code(val));
}


/*
 * Remap: change the code of t
 * - t must be mapped to a non-nil code
 * - the new code must be non-nill too
 */
static inline void remap_term_to_code(translator_t *trans, term_t t, icode_t c) {
  itable_remap(&trans->term_map, t, c);
}

static inline void remap_term_to_occ(translator_t *trans, term_t t, occ_t x) {
  remap_term_to_code(trans, t, occ2code(x));
}

static inline void remap_term_to_eterm(translator_t *trans, term_t t, eterm_t u) {
  remap_term_to_code(trans, t, eterm2code(u));
}

static inline void remap_term_to_literal(translator_t *trans, term_t t, literal_t l) {
  remap_term_to_code(trans, t, literal2code(l));
}

static inline void remap_term_to_bvar(translator_t *trans, term_t t, bvar_t v) {
  remap_term_to_code(trans, t, bvar2code(v));
}

static inline void remap_term_to_arithvar(translator_t *trans, term_t t, arith_var_t x) {
  remap_term_to_code(trans, t, arithvar2code(x));
}

static inline void remap_term_to_bvvar(translator_t *trans, term_t t, bv_var_t b) {
  remap_term_to_code(trans, t, bvvar2code(b));
}

static inline void remap_term_to_bool(translator_t *trans, term_t t, bool val) {
  remap_term_to_code(trans, t, bool2code(val));
}



/*
 * THEORY VARIABLES
 */

/*
 * Arithmetic variable for v:
 * - return nil (same as null_thvar and null_idx) if v is not mapped to anything yet
 */
static inline thvar_t code_of_arithvar(translator_t *trans, arith_var_t v) {
  return itable_get(&trans->arith_map, v);
}

// map v to x: x must be non-nil
static inline void map_arithvar(translator_t *trans, arith_var_t v, thvar_t x) {
  itable_map(&trans->arith_map, v, x);
}

// change mapping of v to x: current mapping must be non-nil, x must be non-nil
static inline void remap_arithvar(translator_t *trans, arith_var_t v, thvar_t x) {
  itable_remap(&trans->arith_map, v, x);
}



/*
 * Bitvector variable for v
 */
static inline thvar_t code_of_bvvar(translator_t *trans, bv_var_t v) {
  return itable_get(&trans->bv_map, v);
}

// map v to b: b must be non-nil
static inline void map_bvvar(translator_t *trans, bv_var_t v, thvar_t b) {
  itable_map(&trans->bv_map, v, b);
}

// change mapping of v to b: current mapping must be non-nil, b must be non-nil
static inline void remap_bvvar(translator_t *trans, bv_var_t v, thvar_t b) {
  itable_remap(&trans->bv_map, v, b);
}




#endif /* __TRANSLATION_H */
