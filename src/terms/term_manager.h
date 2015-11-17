/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
 * - bvarith_buffer = for bit-vector polynomials
 * - bvarith64_buffer = for bit-vector polynomials (64bit coefficients)
 * - bvlogic_buffer = for other bit-vector constructs
 * - pp_buffer = for power products
 *
 * Auxiliary objects:
 * - bv0, bv1, bv2: buffers to store bitvector constants
 * - vector0: vector of integers
 */
typedef struct term_manager_s {
  term_table_t *terms;
  type_table_t *types;
  pprod_table_t *pprods;

  bvarith_buffer_t *bvarith_buffer;
  bvarith64_buffer_t *bvarith64_buffer;
  bvlogic_buffer_t *bvlogic_buffer;
  pp_buffer_t *pp_buffer;

  object_store_t *bvarith_store;
  object_store_t *bvarith64_store;
  node_table_t *nodes;

  bvconstant_t bv0;
  bvconstant_t bv1;
  bvconstant_t bv2;
  ivector_t vector0;
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
 * Distinct: all terms arg[0] ... arg[n-1] must have compatible types
 * - n must be positive and no more than YICES_MAX_ARITY
 * - arg[] may be modified (sorted)
 */
extern term_t mk_distinct(term_manager_t *manager, uint32_t n, term_t arg[]);


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
 * Same thing for a logical buffer (array of bits)
 * - b must be nonempty
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
 * - this function check the type of a[0] then calls one of the two preceding
 *   mk_..._pprod functions
 *
 * All terms of a must be bitvector terms with the same bitsize (number of bits).
 */
extern term_t mk_pprod(term_manager_t *manager, pprod_t *p, uint32_t n, const term_t *a);

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



#endif /* __TERM_MANAGER_H */
