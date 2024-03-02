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
 * BUFFER FOR ARITHMETIC OPERATIONS USING RED-BLACK TREES
 */

/*
 * The arith_buffers represent polynomials as lists of monomials.
 * This makes some operations inefficient (if the list is long).
 * On some of the SMT-LIB 2 QF_LIA/miplib benchmarks, this causes
 * a  major slow down (polynomial construction takes minutes).
 *
 * This module is an alternative representation based on balanced binary trees.
 */

#ifndef __BALANCED_ARITH_BUFFERS_H
#define __BALANCED_ARITH_BUFFERS_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/polynomials.h"
#include "terms/pprod_table.h"
#include "terms/rationals.h"
#include "utils/bitvectors.h"
#include "utils/int_vectors.h"


/*
 * Buffer = tree of monomials.
 *
 * Each node in the tree is identified by an index (uint32_t)
 * - index 0 (= null_node) is a marker for leaves
 * - other nodes have an index between 1 and nterms
 *
 * The tree is represented using three arrays:
 * - mono[i] = monomial for node i
 * - child[i] = pair of children:
 *   child[i][0] = left child, child[i][1] = right child
 *   (if i is a leaf node then left and right children are 0)
 * - isred[i] = one bit: 1 means red node, 0 means black node
 *
 * Global data:
 * - size = size of arrays mono, node, isred
 * - num_nodes = total number of nodes
 * - nterms = total number of terms
 * - free_list = start of the free list (or null_node)
 * - root = id of the root node (or null_node for the empty tree)
 * - ptbl = pprod table for construction of power products
 * - stack = vector used for balancing = path form root to a new node
 *
 * The arrays are used as follows:
 * - index i between 0 and num_nodes - 1: initialized nodes
 * - the null node has index 0 it's always in the tree (and it has coefficient 0)
 * - any other node with coefficient 0, is not in the tree, it's in the free list.
 * - nterms = number of nodes in the tree = number of non-zero monomials
 *          = num_nodes - (size of the free list + 1).
 *
 * The free list is maintained by using child[i][0] as a link (null_node
 * marks the end of the list).
 */

// monomial structure = pair power product/rational
typedef struct mono_s {
  pprod_t *prod;
  rational_t coeff;
} mono_t;

// node = array of two indices
typedef uint32_t rb_node_t[2];

// important: rba_null must be 0
enum {
  rba_null = 0,
};

// tree structure
typedef struct rba_buffer_s {
  mono_t *mono;
  rb_node_t *child;
  byte_t *isred;
  pprod_table_t *ptbl;
  ivector_t stack;

  uint32_t size;
  uint32_t num_nodes;
  uint32_t nterms;
  uint32_t root;
  uint32_t free_list;
} rba_buffer_t;


/*
 * Default and maximal size
 */
#define DEF_RBA_BUFFER_SIZE 4
#define MAX_RBA_BUFFER_SIZE (UINT32_MAX/sizeof(mono_t))


/*
 * OPERATIONS
 */

/*
 * Initialize:
 * - ptbl = attached power product table
 * - the buffer contains the empty tree (i.e., zero polynomial)
 */
extern void init_rba_buffer(rba_buffer_t *b, pprod_table_t *ptbl);

/*
 * Delete: free all memory
 */
extern void delete_rba_buffer(rba_buffer_t *b);

/*
 * Reset (to the empty tree)
 */
extern void reset_rba_buffer(rba_buffer_t *b);



/*
 * LOW-LEVEL TREE OPERATIONS (EXPORTED FOR TESTING)
 */

/*
 * Search for a node whose prod is equal to r
 * - return its index or rba_null if there's no such node
 */
extern uint32_t rba_find_node(rba_buffer_t *b, pprod_t *r);

/*
 * Search for a monomial whose prod is equal to r
 * - if there's one return its id and set new_node to false
 * - if there isn't one, create a new node (with coeff = 0 and prod = r)
 *   and set new_node to true.
 *
 * Side effects:
 * - if a new node is created, num_terms is incremented
 * - if new_node is false, the path from the root to the returned
 *   node p is stored in b->stack in the form
 *     [rba_null, root, ...., q] where q is p's parent
 */
extern uint32_t rba_get_node(rba_buffer_t *b, pprod_t *r, bool *new_node);


/*
 * Delete node i
 * - mono[i].coeff must be zero
 * - b->stack must contain the path from the root to i's parent
 *   (as set by get_node: [null, root, ...., parent of i]
 *
 * Side effect:
 * - decrement b->num_terms
 */
extern void rba_delete_node(rba_buffer_t *b, uint32_t i);




/*************
 *  QUERIES  *
 ************/

/*
 * Number of terms
 */
static inline uint32_t rba_buffer_num_terms(const rba_buffer_t *b) {
  return b->nterms;
}


/*
 * Check whether b is zero
 */
static inline bool rba_buffer_is_zero(const rba_buffer_t *b) {
  return b->nterms == 0;
}


/*
 * Check whether b is constant
 */
extern bool rba_buffer_is_constant(const rba_buffer_t *b);


/*
 * Check whether b is constant and nonzero
 */
extern bool rba_buffer_is_nonzero(const rba_buffer_t *b);


/*
 * Check whether b is constant and positive, negative, etc.
 */
extern bool rba_buffer_is_pos(const rba_buffer_t *b);
extern bool rba_buffer_is_neg(const rba_buffer_t *b);
extern bool rba_buffer_is_nonneg(const rba_buffer_t *b);
extern bool rba_buffer_is_nonpos(const rba_buffer_t *b);


/*
 * Check whether b is of the form a * X - a * Y
 * for a non-zero rational a and two products X and Y.
 * If so return X in *r1 and Y in *r2
 */
extern bool rba_buffer_is_equality(const rba_buffer_t *b, pprod_t **r1, pprod_t **r2);


/*
 * Check whether b is of the form 1 * X for a non-null power-product X
 * If so return X in *r
 */
extern bool rba_buffer_is_product(const rba_buffer_t *b, pprod_t **r);


/*
 * Get degree of polynomial in buffer b.
 * - returns 0 if b is zero
 */
extern uint32_t rba_buffer_degree(const rba_buffer_t *b);


/*
 * Degree of variable x in b
 * - return largest d such that x^d occurs in b
 * - return 0 if x does not occur in b
 */
extern uint32_t rba_buffer_var_degree(const rba_buffer_t *b, int32_t x);


/*
 * Main term = maximal power product of b in the deg-lex ordering.
 * - b must be non-zero
 */
extern pprod_t *rba_buffer_main_term(const rba_buffer_t *b);


/*
 * Main monomial = monomial whose pp is the main term
 * - b must be non-zero
 */
extern mono_t *rba_buffer_main_mono(const rba_buffer_t *b);


/*
 * Root monomial: b must be non-zero
 */
static inline mono_t *rba_buffer_root_mono(const rba_buffer_t *b) {
  assert(b->nterms > 0);
  return b->mono + b->root;
}


/*
 * Extract the first and second monomial (b must have 2 monomials)
 *  m[0] --> fist monomial in lex order
 *  m[1] --> second monomial in lex order
 */
extern void rba_buffer_monomial_pair(const rba_buffer_t *b, mono_t *m[2]);


/*
 * Return the monomial of b whose pp is equal to r
 * - return NULL if r does not occur in b
 */
extern mono_t *rba_buffer_get_mono(rba_buffer_t *b, pprod_t *r);


/*
 * Get the constant monomial of b
 * - return NULL if b does not have a constant monomial
 */
extern mono_t *rba_buffer_get_constant_mono(const rba_buffer_t *b);


/*
 * Check whether b1 and b2 are equal
 * - both must use the same ptbl
 */
extern bool rba_buffer_equal(rba_buffer_t *b1, rba_buffer_t *b2);




/*****************************
 *  POLYNOMIAL CONSTRUCTION  *
 ****************************/

/*
 * All operations update the first argument b.
 *
 * Some operations have a power product r as argument.
 * The power product r must be defined in b's internal
 * power-product table (i.e., either r is empty_pp, or
 * r is a tagged variable, or r occurs in b->ptbl).
 *
 * Some operations use one or two other buffers b1 and b2.  In such
 * cases, b, b1, and b2 must all have the same power-product table
 * and the modified buffer b must be distinct from b1 and b2.
 */

/*
 * Set b to the constant 1
 */
extern void rba_buffer_set_one(rba_buffer_t *b);


/*
 * Multiply b by -1
 */
extern void rba_buffer_negate(rba_buffer_t *b);


/*
 * Multiply b by constant a
 */
extern void rba_buffer_mul_const(rba_buffer_t *b, const rational_t *a);


/*
 * Divide b by constant a
 * - a must be non-zero
 */
extern void rba_buffer_div_const(rba_buffer_t *b, const rational_t *a);


/*
 * Take all coefficients mod m
 * - b must have integer coefficients only
 * - m must be a positive integer
 */
extern void rba_buffer_mod_const(rba_buffer_t *b, const rational_t *m);


/*
 * Multiply b by power product r
 */
extern void rba_buffer_mul_pp(rba_buffer_t *b, pprod_t *r);


/*
 * Multiply b by (- r)
 */
extern void rba_buffer_mul_negpp(rba_buffer_t *b, pprod_t *r);


/*
 * Multiply b by a * r
 */
extern void rba_buffer_mul_mono(rba_buffer_t *b, const rational_t *a, pprod_t *r);



/*
 * Add constant a to b
 */
extern void rba_buffer_add_const(rba_buffer_t *b, const rational_t *a);


/*
 * Add constant (-a) to b
 */
extern void rba_buffer_sub_const(rba_buffer_t *b, const rational_t *a);


/*
 * Add r to b
 */
extern void rba_buffer_add_pp(rba_buffer_t *b, pprod_t *r);


/*
 * Add -r to b
 */
extern void rba_buffer_sub_pp(rba_buffer_t *b, pprod_t *r);


/*
 * Add a * r to b
 */
extern void rba_buffer_add_mono(rba_buffer_t *b, const rational_t *a, pprod_t *r);


/*
 * Add -a * r to b
 */
extern void rba_buffer_sub_mono(rba_buffer_t *b, const rational_t *a, pprod_t *r);


/*
 * Add b1 to b
 * - b1 must be different from b
 */
extern void rba_buffer_add_buffer(rba_buffer_t *b, rba_buffer_t *b1);


/*
 * Add (-b1) to b
 * - b1 must be different from b
 */
extern void rba_buffer_sub_buffer(rba_buffer_t *b, rba_buffer_t *b1);


/*
 * Multiply b by b1
 * - b1 must be different form b
 */
extern void rba_buffer_mul_buffer(rba_buffer_t *b, rba_buffer_t *b1);


/*
 * Compute the square of b
 */
extern void rba_buffer_square(rba_buffer_t *b);


/*
 * Add a * b1 to b
 * - b1 must be different from b
 */
extern void rba_buffer_add_const_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a);


/*
 * Add (-a) * b1 to b
 * - b1 must be different from b
 */
extern void rba_buffer_sub_const_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a);


/*
 * Add r * b1 to b
 * - b1 must be different from b
 */
extern void rba_buffer_add_pp_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, pprod_t *r);


/*
 * Add - r * b1 to b
 * - b1 must be different from b
 */
extern void rba_buffer_sub_pp_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, pprod_t *r);


/*
 * Add a * r * b1 to b
 * - b1 must be different from b
 */
extern void rba_buffer_add_mono_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a, pprod_t *r);

/*
 * Add -a * r * b1 to b
 * - b1 must be different from b
 */
extern void rba_buffer_sub_mono_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a, pprod_t *r);


/*
 * Add b1 * b2 to b
 * - b1 and b2 must be distinct from b (but b1 may be equal to b2)
 */
extern void rba_buffer_add_buffer_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, rba_buffer_t *b2);


/*
 * Add - b1 * b2 to b
 * - b1 and b2 must be distinct from b (but b1 may be equal to b2)
 */
extern void rba_buffer_sub_buffer_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, rba_buffer_t *b2);





/*************************************
 *  OPERATIONS WITH MONOMIAL ARRAYS  *
 ************************************/

/*
 * A monomial array contains a monomials of the form (coeff, index)
 * where indices are signed integers. Operations between buffers and
 * monomial arrays require to convert the integer indices used by
 * monomials to power products used by buffers.
 *
 * All operations below take three arguments:
 * - b is an rb_arithmetic buffer
 * - poly is an array of monomials
 * - pp is an array of power products
 *   if poly[i] is a monomial a_i x_i then pp[i] must be the conversion
 *   of x_i to a power product.
 *
 * All operations are in place operations on the first argument b
 * (i.e., all modify the buffer). There are two requirements
 * on mono and pp:
 * - poly must be terminated by and end-marker (var = max_idx).
 * - pp must be sorted in the deg-lex ordering and have at least
 *   as many elements as length of mono - 1.
 * In particular, if poly contains a constant monomial (with x_i = const_idx),
 * then that monomial must comes first (i.e., i must be 0) and pp[0] must
 * be empty_pp.
 */

/*
 * Add poly to buffer b
 */
extern void rba_buffer_add_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp);


/*
 * Subtract poly from buffer b
 */
extern void rba_buffer_sub_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp);


/*
 * Add a * poly to buffer b
 */
extern void rba_buffer_add_const_times_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp, const rational_t *a);


/*
 * Subtract a * poly from b
 */
extern void rba_buffer_sub_const_times_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp, const rational_t *a);


/*
 * Add a * r * poly to b
 */
extern void rba_buffer_add_mono_times_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp, const rational_t *a, pprod_t *r);


/*
 * Add -a * r * poly to b
 */
extern void rba_buffer_sub_mono_times_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp, const rational_t *a, pprod_t *r);


/*
 * Multiply b by poly
 */
extern void rba_buffer_mul_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp);


/*
 * Multiply b by  p ^ d
 * - pp = power products for the variables of p
 * - use aux as an auxiliary buffer (aux must be distinct from b)
 * - store the result in b
 */
extern void rba_buffer_mul_monarray_power(rba_buffer_t *b, monomial_t *poly, pprod_t **pp, uint32_t d, rba_buffer_t *aux);



/*******************************************************************
 *  SUPPORT FOR HASH CONSING AND CONVERSION TO POLYNOMIAL OBJECTS  *
 ******************************************************************/

/*
 * The conversion of a buffer b to a polynomial object requires two steps:
 * 1) convert all the power-products in b to integer indices.
 *    This must map empty_pp to const_idx and end_pp to max_idx.
 * 2) build a polynomial from the coefficients of b and the integer indices
 *
 * The operations below use a buffer b and an integer array v.
 * The array v stores the conversion from power-products to integer indices:
 * If b contains a_0 r_0 + ... + a_n r_n then v must have (n+2) elements
 * and the integer index for power product r_i is v[i], and the last element
 * of v must be max_idx.
 *
 * The pair (b, v) defines then a polynomial P(b, v) = a_1 v[1] + ... + a_n v[n],
 */

/*
 * Hash code for P(b, v).
 * This function is consistent with hash_polynomial defined in polynomials.c:
 * If P(b, v) = p0 then hash_rba_buffer(b, v) = hash_polynomial(p0).
 */
extern uint32_t hash_rba_buffer(rba_buffer_t *b, int32_t *v);


/*
 * Check where P(b, v) is equal to p
 */
extern bool rba_buffer_equal_poly(const rba_buffer_t *b, int32_t *v, const polynomial_t *p);


/*
 * Build P(b, v) (i.e., convert b to a polynomial then reset b).
 * SIDE EFFECT: b is reset to the zero polynomial.
 */
extern polynomial_t *rba_buffer_get_poly(rba_buffer_t *b, int32_t *v);


/*
 * Check whether b is an integral polynomial
 * (i.e., all variables and coefficients are integer)
 * - this uses a function pointer var_is_int to check the type of all
 *   variables:
 * - for every variable x, var_is_int(aux, x) must return true if x is
 *   integer, false if x is real.
 */
typedef bool (*var_type_fun_t)(void *aux, int32_t x);
extern bool rba_buffer_is_int(const rba_buffer_t *b, void *aux, var_type_fun_t var_is_int);

/*
 * Check whether the every coefficient c of b is int and 0 <= c < mod
 */
extern bool rba_buffer_is_mod(const rba_buffer_t *b, const rational_t *mod);


/****************
 *  SHORT CUTS  *
 ***************/

/*
 * All operations that take a power product r have a variant that takes a single
 * variable x as argument.
 */

/*
 * Multiply b by x
 */
static inline void rba_buffer_mul_var(rba_buffer_t *b, int32_t x) {
  rba_buffer_mul_pp(b, var_pp(x));
}


/*
 * Multiply b by (- x)
 */
static inline void rba_buffer_mul_negvar(rba_buffer_t *b, int32_t x) {
  rba_buffer_mul_negpp(b, var_pp(x));
}


/*
 * Multiply b by a * x
 */
static inline void rba_buffer_mul_varmono(rba_buffer_t *b, const rational_t *a, int32_t x) {
  rba_buffer_mul_mono(b, a, var_pp(x));
}


/*
 * Add x to b
 */
static inline void rba_buffer_add_var(rba_buffer_t *b, int32_t x) {
  rba_buffer_add_pp(b, var_pp(x));
}


/*
 * Add -x to b
 */
static inline void rba_buffer_sub_var(rba_buffer_t *b, int32_t x) {
  rba_buffer_sub_pp(b, var_pp(x));
}


/*
 * Add a * x to b
 */
static inline void rba_buffer_add_varmono(rba_buffer_t *b, const rational_t *a, int32_t x) {
  rba_buffer_add_mono(b, a, var_pp(x));
}


/*
 * Add -a * x to b
 */
static inline void rba_buffer_sub_varmono(rba_buffer_t *b, const rational_t *a, int32_t x) {
  rba_buffer_sub_mono(b, a, var_pp(x));
}


/*
 * Add x * b1 to b
 */
static inline void rba_buffer_add_var_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, int32_t x) {
  rba_buffer_add_pp_times_buffer(b, b1, var_pp(x));
}


/*
 * Add - x * b1 to b
 */
static inline void rba_buffer_sub_var_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, int32_t x) {
  rba_buffer_sub_pp_times_buffer(b, b1, var_pp(x));
}


/*
 * Add a * x * b1 to b
 */
static inline void
rba_buffer_add_varmono_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a, int32_t x) {
  rba_buffer_add_mono_times_buffer(b, b1, a, var_pp(x));
}


/*
 * Add -a * x * b1 to b
 */
static inline void
rba_buffer_sub_varmono_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a, int32_t x) {
  rba_buffer_sub_mono_times_buffer(b, b1, a, var_pp(x));
}




#endif /* __BALANCED_ARITH_BUFFERS_H */
