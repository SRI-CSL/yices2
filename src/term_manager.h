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

#include "bvlogic_buffers.h"
#include "terms.h"


/*
 * Internal components:
 * - terms = term table
 * - pprod = power-product table
 * - types = pointer to an external type table.
 * 
 * Optional components allocated and initialized lazily:
 * - nodes = node table for bvlogic buffer
 * - arith_store = store for arithmetic monomials
 * - bvarith_store = store for bitvector monomials (large coefficients)
 * - bvarith64_store = store for bitvector monomials (64bit coefficients)
 *
 * Internal buffers: allocated lazily too
 * - arith_buffer = for arithmetic polynomials
 * - bvarith_buffer = for bit-vector polynomials
 * - bvarith64_buffer = for bit-vector polynomials (64bit coefficients)
 * - bvlogic_buffer = for other bit-vector constructs
 *
 * Auxiliary objects:
 * - r0: rational buffer
 * - bv0, bv1, bv2: buffers to store bitvector constants
 * - vector0: vector of integers
 */
typedef struct term_manager_s {
  term_table_t terms;
  type_table_t *types;
  pprod_table_t pprods;

  arith_buffer_t *arith_buffer;
  bvarith_buffer_t *bvarith_buffer;
  bvarith64_buffer_t *bvarith64_buffer;
  bvlogic_buffer_t *bvlogic_buffer;

  object_store_t *arith_store;
  object_store_t *bvarith_store;
  object_store_t *bvarith64_store;
  node_table_t *nodes;

  rational_t r0;
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
 * - n = initial term table size
 * - types = attached type table
 */
extern void init_term_manager(term_manager_t *manager, type_table_t *types, uint32_t n);


/*
 * Delete all: free memory
 */
extern void delete_term_manager(term_manager_t *manager);


/*
 * Get the internal components
 */
static inline term_table_t *term_manager_get_terms(term_manager_t *manager) {
  return &manager->terms;
}

static inline pprod_table_t *term_manager_get_pprods(term_manager_t *manager) {
  return &manager->pprods;
}

static inline type_table_t *term_manager_get_types(term_manager_t *manager) {
  return manager->types;
}


/*
 * Access to the internal stores: 
 * - the store is allocated and initialized if needed
 */
extern node_table_t *term_manager_get_nodes(term_manager_t *manager);
extern object_store_t *term_manager_get_arith_store(term_manager_t *manager);
extern object_store_t *term_manager_get_bvarith_store(term_manager_t *manager);
extern object_store_t *term_manager_get_bvarith64_store(term_manager_t *manager);


/*
 * Access to the internal buffers:
 * - they are allocated and initialized if needed (and the store they need too)
 *
 * WARNING:
 * - the term constructors may modify these buffers
 */
extern arith_buffer_t *term_manager_get_arith_buffer(term_manager_t *manager);
extern bvarith_buffer_t *term_manager_get_bvarith_buffer(term_manager_t *manager);
extern bvarith64_buffer_t *term_manager_get_bvarith64_buffer(term_manager_t *manager);
extern bvlogic_buffer_t *term_manager_get_bvlogic_buffer(term_manager_t *manager);




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
 * side effect; a is modified
 */
extern term_t mk_or(term_manager_t *manager, uint32_t n, term_t a[]);
extern term_t mk_and(term_manager_t *manager, uint32_t n, term_t a[]);
extern term_t mk_xor(term_manager_t *manager, uint32_t n, term_t a[]);




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
extern term_t mk_application(term_manager_t *manager, term_t fun, uint32_t n, term_t arg[]);


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
 * Tuple constructor:
 * - arg = array of n terms
 * - n must be positive and no more than YICES_MAX_ARITY
 */
extern term_t mk_tuple(term_manager_t *manager, uint32_t n, term_t arg[]);


/*
 * Projection: component i of tuple
 */
extern term_t mk_select(term_manager_t *manager, uint32_t i, term_t tuple);


/*
 * Function update: (update f (arg[0] ... arg[n-1]) new_v)
 * - f must have function type and arity n
 */
extern term_t mk_update(term_manager_t *manager, term_t fun, uint32_t n, term_t arg[], term_t new_v);


/*
 * Distinct: all terms arg[0] ... arg[n-1] must have compatible types
 * - n must be positive and no more than YICES_MAX_ARITY
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
extern term_t mk_forall(term_manager_t *manager, uint32_t n, term_t v[], term_t body);
extern term_t mk_exists(term_manager_t *manager, uint32_t n, term_t v[], term_t body);


/*
 * Lambda terms:
 * - n = number of variables (must be positive and no more than YICES_MAX_VAR)
 * - all variables v[0 ... n-1] must be distinct
 */
extern term_t mk_lambda(term_manager_t *manager, uint32_t n, term_t v[], term_t body);



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
 * - b must be normalized
 * - b->ptbl must be equal to manager->pprods
 * - b may be the same as manager->arith_buffer
 * - side effect: b is reset
 *
 * - if b is a constant then a constant rational is created
 * - if b is of the form 1. t then t is returned
 * - if b is of the from 1. t_1^d_1 ... t_n^d_n then a power product is returned
 * - otherwise a polynomial term is created
 */
extern term_t mk_arith_term(term_manager_t *manager, arith_buffer_t *b);


/*
 * Create an arithmetic atom from the content of buffer b:
 * - b->ptbl must be equal to manager->pprods
 * - b may be the same as manager->arith_buffer
 * - all functions normalize b first
 * - side effect: b is reset
 */
extern term_t mk_arith_eq0(term_manager_t *manager, arith_buffer_t *b);   // b == 0
extern term_t mk_arith_neq0(term_manager_t *manager, arith_buffer_t *b);  // b != 0
extern term_t mk_arith_geq0(term_manager_t *manager, arith_buffer_t *b);  // b >= 0
extern term_t mk_arith_leq0(term_manager_t *manager, arith_buffer_t *b);  // b <= 0
extern term_t mk_arith_gt0(term_manager_t *manager, arith_buffer_t *b);   // b > 0
extern term_t mk_arith_lt0(term_manager_t *manager, arith_buffer_t *b);   // b < 0


/*
 * Variant: create an arithmetci atom from term t
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
 */
extern term_t mk_direct_arith_geq0(term_table_t *tbl, arith_buffer_t *b);  // b >= 0
extern term_t mk_direct_arith_leq0(term_table_t *tbl, arith_buffer_t *b);  // b <= 0
extern term_t mk_direct_arith_gt0(term_table_t *tbl, arith_buffer_t *b);   // b > 0
extern term_t mk_direct_arith_lt0(term_table_t *tbl, arith_buffer_t *b);   // b < 0


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
extern term_t mk_bvarray(term_manager_t *manager, uint32_t n, term_t *a);


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



#endif /* __TERM_MANAGER_H */
