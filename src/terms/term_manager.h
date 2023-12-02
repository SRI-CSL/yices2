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
 * TERM MANAGER
 */

/*
 * A term manager includes a term_table and auxiliary buffers and data
 * structures that are used to implement term constructors and
 * simplifications.
 *
 * Most of this used to be in 'yices_api.c' and relied on global variables.
 * A term_manager is more flexible and modular. It enables use of independent
 * term tables.
 */

#ifndef __TERM_MANAGER_H
#define __TERM_MANAGER_H

#include <stdint.h>

#include "terms/bvlogic_buffers.h"
#include "terms/terms.h"


/*
 * Internal components:
 * - terms = pointer to a term table
 * - pprod = pointer to a power-product table
 * - types = pointer to an external type table.
 *
 * Optional components allocated and initialized lazily:
 * - nodes = node table for bvlogic buffer
 * - bvarith_store = store for bitvector monomials (large coefficients)
 * - bvarith64_store = store for bitvector monomials (64bit coefficients)
 *
 * Internal buffers: allocated lazily too
 * - arith_buffer = for arithmetic polynomials
 * - bvarith_buffer = for bit-vector polynomials
 * - bvlogic_buffer = for other bit-vector constructs
 * - pp_buffer = for power products
 *
 * Auxiliary objects:
 * - r0: rational buffer
 * - bv0, bv1, bv2: buffers to store bitvector constants
 * - vector0: vector of integers
 *
 * Options:
 * - simplify_ite = true if ite simplication is enabled
 * - simplify_bveq1 = true if bitvector equalities of size 1 can simplify to Boolean
 */
typedef struct term_manager_s {
  term_table_t *terms;
  type_table_t *types;
  pprod_table_t *pprods;

  rba_buffer_t *arith_buffer;
  bvarith_buffer_t *bvarith_buffer;
  bvarith64_buffer_t *bvarith64_buffer;
  bvlogic_buffer_t *bvlogic_buffer;
  pp_buffer_t *pp_buffer;

  object_store_t *bvarith_store;
  object_store_t *bvarith64_store;
  node_table_t *nodes;

  rational_t r0;
  bvconstant_t bv0;
  bvconstant_t bv1;
  bvconstant_t bv2;
  ivector_t vector0;

  bool simplify_ite;
  bool simplify_bveq1;
  bool simplify_bvite_offset;

} term_manager_t;



/*
 * GLOBAL OPERATIONS
 */

/*
 * Initialization:
 * - terms = attached term table
 */
extern void init_term_manager(term_manager_t *manager, term_table_t *terms);


/*
 * Delete all: free memory
 */
extern void delete_term_manager(term_manager_t *manager);


/*
 * Reset:
 * - free the internal buffers and empty the stores
 */
extern void reset_term_manager(term_manager_t *manager);



/*
 * Get the internal components
 */
static inline term_table_t *term_manager_get_terms(term_manager_t *manager) {
  return manager->terms;
}

static inline pprod_table_t *term_manager_get_pprods(term_manager_t *manager) {
  return manager->pprods;
}

static inline type_table_t *term_manager_get_types(term_manager_t *manager) {
  return manager->types;
}


/*
 * Access to the internal stores:
 * - the store is allocated and initialized if needed
 */
extern node_table_t *term_manager_get_nodes(term_manager_t *manager);
extern object_store_t *term_manager_get_bvarith_store(term_manager_t *manager);
extern object_store_t *term_manager_get_bvarith64_store(term_manager_t *manager);


/*
 * Access to the internal buffers:
 * - they are allocated and initialized if needed (and the store they need too)
 *
 * WARNING:
 * - the term constructors may modify these buffers
 */
extern rba_buffer_t *term_manager_get_arith_buffer(term_manager_t *manager);
extern bvarith_buffer_t *term_manager_get_bvarith_buffer(term_manager_t *manager);
extern bvarith64_buffer_t *term_manager_get_bvarith64_buffer(term_manager_t *manager);
extern bvlogic_buffer_t *term_manager_get_bvlogic_buffer(term_manager_t *manager);
extern pp_buffer_t *term_manager_get_pp_buffer(term_manager_t *manager);


/*
 * BOOLEAN TERM CONSTRUCTORS
 */

/*
 * Binary constructor: both x and y must be Boolean terms (in manager->terms)
 * - all constructors apply the obvious simplifications
 * - and is converted to not (or (not ..) ...)
 * - iff and binary xor are turned into a binary equality between Boolean terms
 */
extern term_t mk_binary_or(term_manager_t *manager, term_t x, term_t y);
extern term_t mk_binary_and(term_manager_t *manager, term_t x, term_t y);
extern term_t mk_binary_xor(term_manager_t *manager, term_t x, term_t y);
extern term_t mk_implies(term_manager_t *manager, term_t x, term_t y);
extern term_t mk_iff(term_manager_t *manager, term_t x, term_t y);


/*
 * Boolean if-then-else: (ite c x y)
 * - both x and y must be Boolean (and c too)
 */
extern term_t mk_bool_ite(term_manager_t *manager, term_t c, term_t x, term_t y);


/*
 * N-ary constructors
 * - n = number of arguments (must be positive and no more than YICES_MAX_ARITY)
 * - a = array of n Boolean terms
 *
 * SIDE EFFECT: a is modified
 */
extern term_t mk_or(term_manager_t *manager, uint32_t n, term_t a[]);
extern term_t mk_and(term_manager_t *manager, uint32_t n, term_t a[]);
extern term_t mk_xor(term_manager_t *manager, uint32_t n, term_t a[]);


/*
 * Variants: do not modify a
 */
extern term_t mk_or_safe(term_manager_t *manager, uint32_t n, const term_t a[]);
extern term_t mk_and_safe(term_manager_t *manager, uint32_t n, const term_t a[]);
extern term_t mk_xor_safe(term_manager_t *manager, uint32_t n, const term_t a[]);



/*
 * GENERIC CONSTRUCTORS
 */

/*
 * Constant of type tau and index i
 * - tau must be uninterpreted or scalar type
 * - i must be non-negative and smaller than the size of tau
 *   (which matters only if tau is scalar)
 */
extern term_t mk_constant(term_manager_t *manager, type_t tau, int32_t i);


/*
 * New uninterpreted term (global variable) of type tau
 */
extern term_t mk_uterm(term_manager_t *manager, type_t tau);


/*
 * Fresh variable of type tau (for quantifiers)
 */
extern term_t mk_variable(term_manager_t *manager, type_t tau);


/*
 * Function application:
 * - fun must have arity n
 * - arg = array of n arguments
 * - the argument types much match the domain of f
 */
extern term_t mk_application(term_manager_t *manager, term_t fun, uint32_t n, const term_t arg[]);


/*
 * If-then-else: (if c then t else e)
 * - c must be Boolean
 * - t and e must have compatible types tau1 and tau2
 * - tau must be the least common supertype of tau1 and tau2
 */
extern term_t mk_ite(term_manager_t *manager, term_t c, term_t t, term_t e, type_t tau);


/*
 * Equality: t1 and t2 must have compatible types
 */
extern term_t mk_eq(term_manager_t *manager, term_t t1, term_t t2);
extern term_t mk_neq(term_manager_t *manager, term_t t1, term_t t2);  // t1 != t2


/*
 * Array equality:
 * - given two arrays a and b of n term, build
 *   (and (= a[0] b[0]) ... (= a[n-1] b[n-1])
 */
extern term_t mk_array_eq(term_manager_t *manager, uint32_t n, const term_t a[], const term_t b[]);


/*
 * Array inequality:
 * - given two arrays a and b of n terms, build the term
 *   (or (/= a[0] b[0]) ... (/= a[n-1] b[n-1]))
 */
extern term_t mk_array_neq(term_manager_t *manager, uint32_t n, const term_t a[], const term_t b[]);


/*
 * Tuple constructor:
 * - arg = array of n terms
 * - n must be positive and no more than YICES_MAX_ARITY
 */
extern term_t mk_tuple(term_manager_t *manager, uint32_t n, const term_t arg[]);


/*
 * Projection: component i of tuple
 */
extern term_t mk_select(term_manager_t *manager, uint32_t i, term_t tuple);


/*
 * Function update: (update f (arg[0] ... arg[n-1]) new_v)
 * - f must have function type and arity n
 */
extern term_t mk_update(term_manager_t *manager, term_t fun, uint32_t n, const term_t arg[], term_t new_v);


/*
 * Distinct: all terms arg[0] ... arg[n-1] must have compatible types
 * - n must be positive and no more than YICES_MAX_ARITY
 * - arg[] may be modified (sorted)
 */
extern term_t mk_distinct(term_manager_t *manager, uint32_t n, term_t arg[]);


/*
 * Tuple update: replace component i of tuple by new_v
 */
extern term_t mk_tuple_update(term_manager_t *manager, term_t tuple, uint32_t index, term_t new_v);


/*
 * Quantifiers:
 * - n = number of variables (n must be positive and no more than YICES_MAX_VAR)
 * - all variables v[0 ... n-1] must be distinct
 * - body must be a Boolean term
 */
extern term_t mk_forall(term_manager_t *manager, uint32_t n, const term_t v[], term_t body);
extern term_t mk_exists(term_manager_t *manager, uint32_t n, const term_t v[], term_t body);


/*
 * Lambda terms:
 * - n = number of variables (must be positive and no more than YICES_MAX_VAR)
 * - all variables v[0 ... n-1] must be distinct
 */
extern term_t mk_lambda(term_manager_t *manager, uint32_t n, const term_t v[], term_t body);



/*
 * ARITHMETIC TERM AND ATOM CONSTRUCTORS
 */

/*
 * Arithmetic constant
 * - r must be normalized
 */
extern term_t mk_arith_constant(term_manager_t *manager, rational_t *r);


/*
 * Convert b to an arithmetic term:
 * - b->ptbl must be equal to manager->pprods
 * - b may be the same as manager->arith_buffer
 * - side effect: b is reset
 *
 * - if b is a constant then a constant rational is created
 * - if b is of the form 1. t then t is returned
 * - if b is of the from 1. t_1^d_1 ... t_n^d_n then a power product is returned
 * - otherwise a polynomial term is created
 */
extern term_t mk_arith_term(term_manager_t *manager, rba_buffer_t *b);

/*
 * Variant: use the term table
 */
extern term_t mk_direct_arith_term(term_table_t *tbl, rba_buffer_t *b);


/*
 * Create an arithmetic atom from the content of buffer b:
 * - b->ptbl must be equal to manager->pprods
 * - b may be the same as manager->arith_buffer
 * - all functions normalize b first
 * - side effect: b is reset
 */
extern term_t mk_arith_eq0(term_manager_t *manager, rba_buffer_t *b);   // b == 0
extern term_t mk_arith_neq0(term_manager_t *manager, rba_buffer_t *b);  // b != 0
extern term_t mk_arith_geq0(term_manager_t *manager, rba_buffer_t *b);  // b >= 0
extern term_t mk_arith_leq0(term_manager_t *manager, rba_buffer_t *b);  // b <= 0
extern term_t mk_arith_gt0(term_manager_t *manager, rba_buffer_t *b);   // b > 0
extern term_t mk_arith_lt0(term_manager_t *manager, rba_buffer_t *b);   // b < 0


/*
 * Variant: create an arithmetic atom from term t
 */
extern term_t mk_arith_term_eq0(term_manager_t *manager, term_t t);   // t == 0
extern term_t mk_arith_term_neq0(term_manager_t *manager, term_t t);  // t != 0
extern term_t mk_arith_term_geq0(term_manager_t *manager, term_t t);  // t >= 0
extern term_t mk_arith_term_leq0(term_manager_t *manager, term_t t);  // t <= 0
extern term_t mk_arith_term_gt0(term_manager_t *manager, term_t t);   // t > 0
extern term_t mk_arith_term_lt0(term_manager_t *manager, term_t t);   // t < 0



/*
 * Binary atoms
 * - t1 and t2 must be arithmetic terms in manager->terms
 */
extern term_t mk_arith_eq(term_manager_t *manager, term_t t1, term_t t2);   // t1 == t2
extern term_t mk_arith_neq(term_manager_t *manager, term_t t1, term_t t2);  // t1 != t2
extern term_t mk_arith_geq(term_manager_t *manager, term_t t1, term_t t2);  // t1 >= t2
extern term_t mk_arith_leq(term_manager_t *manager, term_t t1, term_t t2);  // t1 <= t2
extern term_t mk_arith_gt(term_manager_t *manager, term_t t1, term_t t2);   // t1 > t2
extern term_t mk_arith_lt(term_manager_t *manager, term_t t1, term_t t2);   // t1 < t2


/*
 * Variants: direct construction/simplification from a term table
 * These functions normalize b then create an atom
 * - side effect: b is reset
 * If simplify_ite is true, simplifications are enabled
 */
extern term_t mk_direct_arith_geq0(term_table_t *tbl, rba_buffer_t *b, bool simplify_ite);  // b >= 0
extern term_t mk_direct_arith_leq0(term_table_t *tbl, rba_buffer_t *b, bool simplify_ite);  // b <= 0
extern term_t mk_direct_arith_gt0(term_table_t *tbl, rba_buffer_t *b, bool simplify_ite);   // b > 0
extern term_t mk_direct_arith_lt0(term_table_t *tbl, rba_buffer_t *b, bool simplify_ite);   // b < 0
extern term_t mk_direct_arith_eq0(term_table_t *tbl, rba_buffer_t *b, bool simplify_ite);   // b == 0


/*
 * Arithmetic root atom.
 */
extern term_t mk_arith_root_atom(term_manager_t* manager, uint32_t k, term_t x, term_t p, root_atom_rel_t r);

/*
 * Arithmetic root atom (b is a buffer that can be cleared and used for computation).
 */
extern term_t mk_direct_arith_root_atom(rba_buffer_t* b, term_table_t* terms, uint32_t k, term_t x, term_t p, root_atom_rel_t r, bool simplify_ite);


/*
 * Arithmetic root atoms.
 */
extern term_t mk_arith_root_atom_lt(term_manager_t *manager, uint32_t k, term_t x, term_t p);
extern term_t mk_arith_root_atom_leq(term_manager_t *manager, uint32_t k, term_t x, term_t p);
extern term_t mk_arith_root_atom_eq(term_manager_t *manager, uint32_t k, term_t x, term_t p);
extern term_t mk_arith_root_atom_neq(term_manager_t *manager, uint32_t k, term_t x, term_t p);
extern term_t mk_arith_root_atom_gt(term_manager_t *manager, uint32_t k, term_t x, term_t p);
extern term_t mk_arith_root_atom_geq(term_manager_t *manager, uint32_t k, term_t x, term_t p);


/*
 * Arithmetic root atoms (direct versions).
 */
extern term_t mk_direct_arith_root_atom_lt(rba_buffer_t* b, term_table_t* terms, uint32_t k, term_t x, term_t p, bool simplify_ite);
extern term_t mk_direct_arith_root_atom_leq(rba_buffer_t* b, term_table_t* terms, uint32_t k, term_t x, term_t p, bool simplify_ite);
extern term_t mk_direct_arith_root_atom_eq(rba_buffer_t* b, term_table_t* terms, uint32_t k, term_t x, term_t p, bool simplify_ite);
extern term_t mk_direct_arith_root_atom_neq(rba_buffer_t* b, term_table_t* terms, uint32_t k, term_t x, term_t p, bool simplify_ite);
extern term_t mk_direct_arith_root_atom_gt(rba_buffer_t* b, term_table_t* terms, uint32_t k, term_t x, term_t p, bool simplify_ite);
extern term_t mk_direct_arith_root_atom_geq(rba_buffer_t* b, term_table_t* terms, uint32_t k, term_t x, term_t p, bool simplify_ite);



/*
 * More arithmetic constructs for div/mod and mixed arithmetic
 * - these are to support SMT-LIB 2 operators
 */
extern term_t mk_arith_is_int(term_manager_t *manager, term_t t);              // is_int t
extern term_t mk_arith_idiv(term_manager_t *manager, term_t t1, term_t t2);    // (div t1 t2)
extern term_t mk_arith_mod(term_manager_t *manager, term_t t1, term_t t2);     // (mod t1 t2)
extern term_t mk_arith_divides(term_manager_t *manager, term_t t1, term_t t2); // t1 divides t2

extern term_t mk_arith_abs(term_manager_t *manager, term_t t);    // absolute value of t
extern term_t mk_arith_floor(term_manager_t *manager, term_t t);  // largest integer <= t
extern term_t mk_arith_ceil(term_manager_t *manager, term_t t);   // smallest integer >= t


/*
 * Rational division
 */
extern term_t mk_arith_rdiv(term_manager_t *manager, term_t t1, term_t t2);


/*
 * FINITE FIELD ARITHMETIC
 */

/*
 * Finite field arithmetic constant
 * - r must be normalized wrt. mod
 */
extern term_t mk_arith_ff_constant(term_manager_t *manager, rational_t *r, rational_t *mod);

/*
 * Convert b to a finite field arithmetic term:
 * - b->ptbl must be equal to manager->pprods
 * - b may be the same as manager->arith_buffer
 * - tau must be a type in manager->types
 * - side effect: b is reset
 *
 * - if b is a constant then a constant finite field is created
 * - if b is of the form 1. t then t is returned
 * - if b is of the from 1. t_1^d_1 ... t_n^d_n then a power product is returned
 * - otherwise a polynomial term is created
 */
extern term_t mk_arith_ff_term(term_manager_t *manager, rba_buffer_t *b, rational_t *mod);

/*
 * Variant: use the term table
 */
extern term_t mk_direct_arith_ff_term(term_table_t *tbl, rba_buffer_t *b, rational_t *mod);

/*
 * Create a finite field arithmetic atom from the content of buffer b:
 * - b->ptbl must be equal to manager->pprods
 * - b may be the same as manager->arith_buffer
 * - all functions normalize b first
 * - tau must be a type in manager->types
 * - side effect: b is reset
 */
extern term_t mk_arith_ff_eq0(term_manager_t *manager, rba_buffer_t *b, rational_t *mod);   // b == 0
extern term_t mk_arith_ff_neq0(term_manager_t *manager, rba_buffer_t *b, rational_t *mod);  // b != 0

/*
 * Variant: create an arithmetic atom from term t
 */
extern term_t mk_arith_ff_term_eq0(term_manager_t *manager, term_t t);   // t == 0
extern term_t mk_arith_ff_term_neq0(term_manager_t *manager, term_t t);  // t != 0

/*
 * Binary atoms
 * - t1 and t2 must be finite field arithmetic terms in manager->terms
 * - t1 and t2 must have the same finite field type tau
 */
extern term_t mk_arith_ff_eq(term_manager_t *manager, term_t t1, term_t t2);   // t1 == t2
extern term_t mk_arith_ff_neq(term_manager_t *manager, term_t t1, term_t t2);  // t1 != t2

/*
 * Variants: direct construction/simplification from a term table
 * These functions normalize b then create an atom
 * - side effect: b is reset
 * If simplify_ite is true, simplifications are enabled
 */
extern term_t mk_direct_arith_ff_eq0(term_table_t *tbl, rba_buffer_t *b, rational_t *mod, bool simplify_ite);   // b == 0


/*
 * BITVECTOR TERMS AND ATOMS
 */

/*
 * Bitvector constant:
 * - b->bitsize must be positive and no more than YICES_MAX_BVSIZE
 */
extern term_t mk_bv_constant(term_manager_t *manager, bvconstant_t *b);


/*
 * Convert a polynomial buffer to a bitvector terms:
 * - b must use the same pprod as manager (i.e., b->ptbl = &manager->pprods)
 * - b may be equal to manager->bvarith_buffer
 * - side effect: b is reset
 *
 * This normalizes b first then check for the following:
 * 1) b reduced to a single variable x: return x
 * 2) b reduced to a power product pp: return pp
 * 3) b is constant, return a BV64_CONSTANT or BV_CONSTANT term
 * 4) b can be converted to a BV_ARRAY term (by converting + and *
 *    to bitwise or and shift): return the BV_ARRAY
 *
 * Otherwise, build a bit-vector polynomial.
 */
extern term_t mk_bvarith_term(term_manager_t *manager, bvarith_buffer_t *b);


/*
 * Same thing for a 64bit coefficient buffer
 */
extern term_t mk_bvarith64_term(term_manager_t *manager, bvarith64_buffer_t *b);


/*
 * Same thing for a logical buffer b (array of bits), then reset b.
 * - b must not be empty.
 * - build a bitvector constant if possible
 * - if b is of the form (select 0 t) ... (select k t) and t has bitsize (k+1)
 *   then return t
 * - otherwise build a bitarray term
 */
extern term_t mk_bvlogic_term(term_manager_t *manager, bvlogic_buffer_t *b);


/*
 * Bit-vector if-then-else (ite c t e)
 * - c must be Boolean
 * - t and e must bitvector terms of the same type
 */
extern term_t mk_bv_ite(term_manager_t *manager, term_t c, term_t t, term_t e);


/*
 * Bit array
 * - a must be an array of n boolean terms
 * - n must be positive and no more than YICES_MAX_BVSIZE
 */
extern term_t mk_bvarray(term_manager_t *manager, uint32_t n, const term_t *a);


/*
 * Shift and division constructors
 * - t1 and t2 must be bitvector terms of the same type
 */
extern term_t mk_bvshl(term_manager_t *manager, term_t t1, term_t t2);   // t1 << t2
extern term_t mk_bvlshr(term_manager_t *manager, term_t t1, term_t t2);  // t1 >> t2 (logical shift)
extern term_t mk_bvashr(term_manager_t *manager, term_t t1, term_t t2);  // t1 >> t2 (arithmetic shift)

// unsigned division of t1 by t2
extern term_t mk_bvdiv(term_manager_t *manager, term_t t1, term_t t2);   // quotient
extern term_t mk_bvrem(term_manager_t *manager, term_t t1, term_t t2);   // remainder

// signed division, with rounding to zero
extern term_t mk_bvsdiv(term_manager_t *manager, term_t t1, term_t t2);   // quotient
extern term_t mk_bvsrem(term_manager_t *manager, term_t t1, term_t t2);   // remainder

// remainder in signed division, with rounding to -infinity
extern term_t mk_bvsmod(term_manager_t *manager, term_t t1, term_t t2);


/*
 * Extract bit i of t
 * - t must be a bitvector term
 * - i must be between 0 and n-1, where n = bitsize of t
 */
extern term_t mk_bitextract(term_manager_t *manager, term_t t, uint32_t i);


/*
 * Convert bit i of buffer b to a Boolean term then reset b
 * - i must be between 0 and n-1 when n = b->bitsize
 */
extern term_t bvl_get_bit(term_manager_t *manager, bvlogic_buffer_t *b, uint32_t i);


/*
 * Atoms: t1 and t2 must be bitvector terms of the same type
 */
extern term_t mk_bveq(term_manager_t *manager, term_t t1, term_t t2);   // t1 == t2
extern term_t mk_bvneq(term_manager_t *manager, term_t t1, term_t t2);  // t1 != t2

// unsigned inequalities
extern term_t mk_bvge(term_manager_t *manager, term_t t1, term_t t2);   // t1 >= t2
extern term_t mk_bvgt(term_manager_t *manager, term_t t1, term_t t2);   // t1 > t2
extern term_t mk_bvle(term_manager_t *manager, term_t t1, term_t t2);   // t1 <= t2
extern term_t mk_bvlt(term_manager_t *manager, term_t t1, term_t t2);   // t1 < t2


// signed inequalities
extern term_t mk_bvsge(term_manager_t *manager, term_t t1, term_t t2);   // t1 >= t2
extern term_t mk_bvsgt(term_manager_t *manager, term_t t1, term_t t2);   // t1 >  t2
extern term_t mk_bvsle(term_manager_t *manager, term_t t1, term_t t2);   // t1 <= t2
extern term_t mk_bvslt(term_manager_t *manager, term_t t1, term_t t2);   // t1 <  t2



/*
 * POWER-PRODUCT AND POLYNOMIAL CONSTRUCTORS
 */

/*
 * The following functions are intended to support operations such as term_substitution
 * or simplification of terms:
 * - for example, for a power product p = t_1^e_1 ... t_k^e_k, we want to construct
 *      f(t_1)^e_1 ... f(t_k)^e_k
 *   where f is a function that maps terms to terms.
 *   To do this: first construct an array a such that a[i] = f(t_i) then call function
 *    mk_pprod(manager, p, n, a) where n = p->len = size of a
 */

/*
 * Arithmetic product:
 * - p is a power product descriptor: t_0^e_0 ... t_{n-1}^e_{n-1}
 * - a is an array of n arithmetic terms
 * - this function constructs the term a[0]^e_0 ... a[n-1]^e_{n-1}
 *
 * IMPORTANT: make sure the total degree is no more than YICES_MAX_DEGREE
 * before calling this function.
 */
extern term_t mk_arith_pprod(term_manager_t *manager, pprod_t *p, uint32_t n, const term_t *a);

/*
 * Bitvector product: 1 to 64 bits vector
 * - p is a power product descriptor: t_0^e_0 ... t_{n-1}^e_{n-1}
 * - a is an array of n bitvector terms
 * - nbits = number of bits in each term of a
 * - this function constructs the term a[0]^e_0 ... a[n-1]^e_{n-1}
 *
 * IMPORTANT: make sure the total degree is no more than YICES_MAX_DEGREE
 * before calling this function.
 */
extern term_t mk_bvarith64_pprod(term_manager_t *manager, pprod_t *p, uint32_t n, const term_t *a, uint32_t nbits);

/*
 * Bitvector product: more than 64 bits
 * - p is a power product descriptor: t_0^e_0 ... t_{n-1}^e_{n-1}
 * - a is an array of n bitvector terms
 * - nbits = number of bits in each term of a
 * - this function constructs the term a[0]^e_0 ... a[n-1]^e_{n-1}
 *
 * IMPORTANT: make sure the total degree is no more than YICES_MAX_DEGREE
 * before calling this function.
 */
extern term_t mk_bvarith_pprod(term_manager_t *manager, pprod_t *p, uint32_t n, const term_t *a, uint32_t nbits);

/*
 * Generic product:
 * - p is a power product descriptor
 * - a is an array of term
 * - n must be positive
 * - this function check the type of a[0] then calls one of the three preceding
 *   mk_..._pprod functions
 *
 * All terms of a must be arithmetic terms or all of them must be bitvector terms
 * with the same bitsize (number of bits).
 */
extern term_t mk_pprod(term_manager_t *manager, pprod_t *p, uint32_t n, const term_t *a);

/*
 * Arithmetic polynomials:
 * - p is c_0 t_0 + ... + c_{n-1} t_{n-1}
 * - a must be an array of n terms (or const_idx)
 * - the function builds c_0 a[0] + ... + c_{n-1} a[n-1]
 *
 * Special convention: if a[i] is const_idx (then c_i * a[i] is just c_i)
 */
extern term_t mk_arith_poly(term_manager_t *manager, polynomial_t *p, uint32_t n, const term_t *a);

/*
 * Bitvector polynomial: same as mk_arith_poly but all elements of a
 * must be either const_idx of bitvector terms of the equal size
 * - the size must be the same as the coefficients of p
 */
extern term_t mk_bvarith64_poly(term_manager_t *manager, bvpoly64_t *p, uint32_t n, const term_t *a);

/*
 * Bitvector polynomials: terms with more than 64bits
 * - same conventions as mk_bvarith64_poly.
 */
extern term_t mk_bvarith_poly(term_manager_t *manager, bvpoly_t *p, uint32_t n, const term_t *a);


/*
 * Support for eliminating arithmetic variables:
 * - given a polynomial p and a term t that occurs in p,
 *   construct the polynomial q such that (t == q) is equivalent to (p == 0)
 *   (i.e., write p as a.t + r and construct  q :=  -r/a).
 * - returns a term equal to q if (t == q) is equivalent to (a.t + r == 0)
 * - return NULL_TERM if the types of t and q are not compatible (i.e., t is an
 *   integer term, but q is not an integer polynomial).
 */
extern term_t mk_arith_elim_poly(term_manager_t *manager, polynomial_t *p, term_t t);


#endif /* __TERM_MANAGER_H */
