/*
 * Polynomials: represented as sums of monomials
 *
 * All polynomials are attached to a manager that keeps
 * track of the variables and monomial ids.
 */

#ifndef __POLYNOMIALS_H
#define __POLYNOMIALS_H

#include <stdint.h>
#include <assert.h>

#include "rationals.h"
#include "arithmetic_variable_manager.h"
#include "object_stores.h"
#include "int_vectors.h"


/*
 * Polynomials are represented as sums of pairs <coeff, index>
 * - the coeff is a rational number.
 * - the index represents a variable.
 * - there are two kinds of variables:
 *   - primitive variables have a name
 *   - auxiliary variables represent products of primitive variables
 * - index 0 is reserved for the empty product (i.e., the constant terms).
 *
 * Polynomial object:
 * - mono = array of pairs <coeff, variable>
 * - nterms = number of monomials
 *   the polynomial is mono[0] + ... + mono[nterms - 1]
 * The polynomial is stored in normalized from:
 * - monomials are sorted in increasing order 
 *   (monomials of smallest degree first, with ties broken using
 *   lexicographic ordering)
 * - mono[nterms].var contains the end-marker max_idx
 * - the coefficients are non-zero.
 *
 * Arith_Buffer object:
 * - list = list of pairs <coeff, variable> sorted in increasing order
 * - some of the coeffs may be zero.
 * - zero coefficients are removed by the normalize operation
 * - list contains at least two elements:
 *   first element is start marker (variable = null_idx) 
 *   last element is end marker (variable = max_idx).
 * - nterms = number of monomials in the list, excluding the start and end markers.
 */

typedef int32_t arith_var_t;

// monomial
typedef struct {
  arith_var_t var;
  rational_t coeff;
} monomial_t;

// polynomial
typedef struct {
  int32_t nterms;
  monomial_t mono[0];
} polynomial_t;

// list of monomials
typedef struct mlist_s {
  struct mlist_s *next;
  arith_var_t var;
  rational_t coeff;
} mlist_t;

// Block size of mlist object-stores
#define MLIST_BANK_SIZE 64

typedef struct arith_buffer_s {
  int32_t nterms;         // length of the list
  mlist_t *list;          // start of the list 
  object_store_t *store;  // for allocation of list elements
  arithvar_manager_t *manager;
} arith_buffer_t;


/*
 * Maximal size of a monomial array = maximal number of terms in a polynomial
 * This makes sure no arithmetic overflow occurs when computing 
 *   sizeof(polynomial) + (n+1) * sizeof(monomial_t)
 * where n = number of terms in poly->mono
 */
#define MAX_POLY_SIZE (((UINT32_MAX-sizeof(polynomial_t))/sizeof(monomial_t))-1)



/************************************************
 * Low-level operations on arrays of monomials  *
 ***********************************************/

/*
 * - allocation: n = size of array = number of monomials
 * - realloc: n = current size, new_size = new_size
 * we must have 0 <= n < MAX_POLY_SIZE, and new_size < MAX_POLY_SIZE.
 * These functions initialize all the rational coefficients (to zero).
 */ 
extern monomial_t *alloc_monarray(int32_t n);
extern monomial_t *realloc_monarray(monomial_t *a, int32_t n, int32_t new_size);

/*
 * Allocate a polynomial of n terms
 * - n+1 monomials are allocated
 * - the last monomial is set to the end-marker
 * - the rational coefficients are initialized to 0
 * - the variable indices in poly->mono are not initialized
 */
extern polynomial_t *alloc_raw_polynomial(uint32_t n);


/*
 * Clear all the coefficients in a[0] to a[n-1]
 */
extern void clear_monarray(monomial_t *a, int32_t n);

/*
 * sort array a in order defined by m.
 * - a must be terminated by the end-marker max_idx 
 * - n = number of monomials in a excluding the end marker
 * (i.e., a[n].var must be max_idx).
 */
extern void sort_monarray(arithvar_manager_t *m, monomial_t *a, int32_t n);


/*
 * Simpler sort: don't use a manager, just sort the array in 
 * increasing variable order.
 * - a must be terminated by the end-marker max_idx
 * - n = number of monomials in a excluding the end marker
 */
extern void varsort_monarray(monomial_t *a, int32_t n);


/*
 * Normalize a: merge monomials with the same variable and remove 
 * monomials with a zero coefficient.
 * - a must be sorted first (using either sort_monarray or varsort_monarray)
 * - n = number of monomials in a (excluding end marker)
 * - result = size of a after normalization.
 */
extern int32_t normalize_monarray(monomial_t *a, int32_t n);

/*
 * Create a polynomial_t object from a.
 * - n = number of monomials in a (excluding end marker)
 * - a must be normalized.
 * SIDE EFFECT: a is reset to zero (all coefficients are cleared).
 */
extern polynomial_t *monarray_getpoly(monomial_t *a, int32_t n);


/*
 * Create a polynomial_t object from a, without side effects
 * - n = number of monomials in a (excluding end marker)
 * - a must be normalized.
 * This function makes a copy of all coefficients (so it has no side effects).
 * This may be somewhat expensive if the coefficients are large GMP numbers.
 */
extern polynomial_t *monarray_copy(monomial_t *a, int32_t n);


/*
 * Hash code for polynomial p
 * - p must be normalized.
 */
extern uint32_t hash_monarray(monomial_t *p);

/*
 * Check whether all variables and coefficients in p are integer
 * - p must be normalized and all its variables must be declared in m
 */
extern bool is_int_monarray(monomial_t *p, arithvar_manager_t *m);


/*
 * Check whether all variables of p are integer
 * - p must be normalized and all its variables must be declared in m
 */
extern bool all_integer_vars_in_monarray(monomial_t *p, arithvar_manager_t *m);



/*
 * Compute period and phase of polynomial p:
 * Let p be b_0 + a_1 x_1 + ... + a_n x_n where x_1 ... x_n are 
 * integer variables and b_0, a_1, ..., a_n are rationals.
 * The period Q and phase R are rationals such that 
 *     FORALL x_1, ..., x_n: EXISTS y: p(x_1 ... x_n) = Q y + R
 * This is computed via
 *   Q := gcd(a_1, ..., a_n) and
 *   R := remainder of b_0 modulo Q.
 *
 * Input: p must be normalized and terminated by the end marker
 * - period and phase must be initialized rationals
 * Output: thre result is copied into *period and *phase
 * - if p is a constant polynomial then period is set to 0
 *   and phase is equal to p.
 */
extern void monarray_period_and_phase(monomial_t *p, rational_t *period, rational_t *phase);


/*
 * Compute factor := gcd of all coefficients in p
 * - all the coefficients must be integers
 * - p must be normalized
 * - if p is zero, then factor is set to 0
 */
extern void monarray_common_factor(monomial_t *p, rational_t *factor);

/*
 * Compute period = gcd of all non-constant coefficients in p
 * - all the coefficients must be integer (except the constant if there's one)
 * - p must be normalized.
 * - if p is constant then period is set to 0
 */
extern void monarray_gcd(monomial_t *p, rational_t *gcd);


/*
 * Copy the constant term of p into c
 * - p must be normalized
 */
extern void monarray_constant(monomial_t *p, rational_t *c);



/*
 * Core operations
 * 
 *  copy:          p := p1
 *  negate:        p := -p1
 *  mul_const:     p := a * p1
 *  mul_var:       p := v * p1
 *  mul_negvar:    p := - v * p1
 *  mul_mono:      p := a * v * p1
 *  add:           p := p1 + p2
 *  sub:           p := p1 - p2
 *  addmul_const:  p := p1 + a * p2
 *  submul_const:  p := p1 - a * p2
 * 
 * - the arguments p1 and p2 must be normalized.
 * - rational a must be non-zero.
 * - variable v must be defined in manager m
 * - p must be large enough to store the result
 * - p must not overlap with p1 or p2
 * - all functions return the size of the result = 
 *   number of monomials, not including the end marker.
 */
extern int32_t copy_monarray(monomial_t *p, monomial_t *p1);
extern int32_t negate_monarray(monomial_t *p, monomial_t *p1);
extern int32_t mul_const_monarray(monomial_t *p, monomial_t *p1, rational_t *a);
extern int32_t mul_var_monarray(monomial_t *p, monomial_t *p1, arith_var_t v, arithvar_manager_t *m);
extern int32_t mul_negvar_monarray(monomial_t *p, monomial_t *p1, arith_var_t v, arithvar_manager_t *m);
extern int32_t mul_mono_monarray(monomial_t *p, monomial_t *p1, arith_var_t v, rational_t *a, arithvar_manager_t *m);

extern int32_t add_monarrays(monomial_t *p, monomial_t *p1, monomial_t *p2);
extern int32_t sub_monarrays(monomial_t *p, monomial_t *p1, monomial_t *p2);
extern int32_t addmul_const_monarrays(monomial_t *p, monomial_t *p1, monomial_t *p2, rational_t *a);
extern int32_t submul_const_monarrays(monomial_t *p, monomial_t *p1, monomial_t *p2, rational_t *a);

/*
 * In-place operations: p must be normalized, terminated by max_idx.
 * - a must be non-zero 
 */
extern void in_place_negate_monarray(monomial_t *p);
extern void in_place_mul_const_monarray(monomial_t *p, rational_t *a);
extern void in_place_mul_var_monarray(monomial_t *p, arith_var_t v, arithvar_manager_t *m);
extern void in_place_mul_negvar_monarray(monomial_t *p, arith_var_t v, arithvar_manager_t *m);
extern void in_place_mul_mono_monarray(monomial_t *p, arith_var_t v, rational_t *a, arithvar_manager_t *m);


/*
 * Comparison: p1 and p2 must be normalized.
 */
extern bool equal_monarray(monomial_t *p1, monomial_t *p2);


/*
 * Check whether p1 and p2 cannot be equal.
 * - if this returns true, then p1(x) != p2(x) for any x
 * - the function just checks whether (p1 - p2) is a non-zero 
 *   constant, so it's not complete.
 * - p1 and p2 must be normalized
 */
extern bool must_disequal_monarray(monomial_t *p1, monomial_t *p2);






/*******************
 *   POLYNOMIALS   *
 ******************/

/*
 * Deletion of polynomial objects.
 */
static inline void free_polynomial(polynomial_t *p) {
  clear_monarray(p->mono, p->nterms);
  safe_free(p);
}

/*
 * Get main variable of p. 
 * returns null_idx if p is zero,
 * returns const_idx if p is a constant polynomial.
 */
extern arith_var_t polynomial_main_var(polynomial_t *p);

/*
 * Degree of p. return 0 if p is zero.
 * m = variable manager for variables of p
 */
extern int32_t polynomial_degree(polynomial_t *p, arithvar_manager_t *m);


/*
 * Degree of variable x in p.
 * - m = variable manager for variables of p
 * - x must be a primitive variable in m
 * - return 0 if x does not occur in p
 */
extern int32_t polynomial_var_degree(polynomial_t *p, arithvar_manager_t *m, arith_var_t x);


/*
 * Get the (primitive) variables of polynomial p and store them in u
 */
extern void polynomial_get_vars(polynomial_t *p, arithvar_manager_t *m, ivector_t *u);


/*
 * Get all the terms occurring in polynomial p: store them in vector u
 */
extern void polynomial_get_terms(polynomial_t *p, arithvar_manager_t *m, ivector_t *u);



/*
 * Check whether p1 - p2 is a nonzero constant
 */
static inline bool must_disequal_polynomial(polynomial_t *p1, polynomial_t *p2) {
  return must_disequal_monarray(p1->mono, p2->mono);
}


/*
 * Check whether p is constant.
 */
static inline bool polynomial_is_constant(polynomial_t *p) {
  return p->nterms == 0 || (p->nterms == 1 && p->mono[0].var == const_idx);
}


/*
 * Check whether p is constant and zero
 */
static inline bool polynomial_is_zero(polynomial_t *p) {
  return p->nterms == 0;
}

/*
 * Check whether p is constant and nonzero
 */
static inline bool polynomial_is_nonzero(polynomial_t *p) {
  return p->nterms == 1 && p->mono[0].var == const_idx;
}


/*
 * Check whether p is constant and positive, negative, etc.  
 * These checks are incomplete (but cheap). They always return 
 * false if p is non-constant.
 */
static inline bool polynomial_is_pos(polynomial_t *p) {
  return p->nterms == 1 && p->mono[0].var == const_idx 
    && q_is_pos(&p->mono[0].coeff);
}

static inline bool polynomial_is_neg(polynomial_t *p) {
  return p->nterms == 1 && p->mono[0].var == const_idx 
    && q_is_neg(&p->mono[0].coeff);
}

static inline bool polynomial_is_nonneg(polynomial_t *p) {
  return p->nterms == 0 || 
    (p->nterms == 1 && p->mono[0].var == const_idx 
     && q_is_pos(&p->mono[0].coeff));
}

static inline bool polynomial_is_nonpos(polynomial_t *p) {
  return p->nterms == 0 || 
    (p->nterms == 1 && p->mono[0].var == const_idx 
     && q_is_neg(&p->mono[0].coeff));
}


/*
 * Check whether p == k + x for non-zero k and variable x
 */
static inline bool polynomial_is_const_plus_var(polynomial_t *p, arith_var_t x) {
  return p->nterms == 2 && p->mono[0].var == const_idx && p->mono[1].var == x 
    && q_is_one(&p->mono[1].coeff);
}

/*
 * Check whether p == x for variable x
 */
static inline bool polynomial_is_var(polynomial_t *p, arith_var_t x) {
  return p->nterms == 1 && p->mono[0].var == x && q_is_one(&p->mono[0].coeff);
}


/*
 * Check whether p is an integer polynomial
 * (i.e. all variables and coefficients are integer)
 * - m must be the manager where variables of p are defined.
 */
static inline bool polynomial_is_int(polynomial_t *p, arithvar_manager_t *m) {
  return is_int_monarray(p->mono, m);
}



/****************************
 * BUFFER-BASED OPERATIONS  *
 ***************************/

/*
 * Initialize store s for list elements
 */
extern void init_mlist_store(object_store_t *s);

/*
 * Delete store s: free all attached memory and clear all rationals.
 * Must not be called unless all buffers with store s are deleted.
 */
extern void delete_mlist_store(object_store_t *s);

/*
 * Initialize buffer b. Initial value = zero polynomial
 * - m = attached manager.
 * - s = attached store
 * All variables occurring in b must be defined in m.
 */
extern void init_arith_buffer(arith_buffer_t *b, arithvar_manager_t *m, object_store_t *s);

/*
 * Delete b and free all attached memory
 */
extern void delete_arith_buffer(arith_buffer_t *b);

/*
 * Normalize: remove any zero monomials from b
 */
extern void arith_buffer_normalize(arith_buffer_t *b);

/*
 * Reset: empty the buffer
 */
extern void arith_buffer_reset(arith_buffer_t *b);

/*
 * Construct a polynomial_t object out of b.
 * - b must be normalized.
 * - SIDE EFFECT: b is reset.
 */
extern polynomial_t *arith_buffer_getpoly(arith_buffer_t *b);

/*
 * Get degree of polynomial in buffer b.
 * - b must be normalized
 * - returns 0 if b is zero
 */
extern int32_t arith_buffer_degree(arith_buffer_t *b);


/*
 * Degree of variable x in b.
 * - x must be a primitive variable in b's variable manager
 * - return 0 if x does not occur in b
 */
extern int32_t arith_buffer_var_degree(arith_buffer_t *b, arith_var_t x);



/*
 * Get main variable of polynomial in b.
 * - b must be normalized.
 * - returns null_idx if b is zero.
 * - returns const_idx if b is a nonzero constant.
 */
extern arith_var_t arith_buffer_main_variable(arith_buffer_t *b);

/*
 * Size = number of terms.
 * - b must be normalized.
 * - returns 0 iff b is zero.
 */
static inline int32_t arith_buffer_size(arith_buffer_t *b) {
  return b->nterms;
}

/*
 * Hash code for buffer b
 * - b must be normalized.
 */
extern uint32_t arith_buffer_hash(arith_buffer_t *b);

/*
 * Check whether all variables and coefficients in b are integer
 * - b must be normalized
 */
extern bool arith_buffer_is_int(arith_buffer_t *b);



/*
 * Comparison with a monomial array p1
 * - b and p1 must be normalized.
 */
extern bool arith_buffer_equal_monarray(arith_buffer_t *b, monomial_t *p1);

/*
 * Comparison with a polynomial_t p
 */
static inline bool arith_buffer_equal_polynomial(arith_buffer_t *b, polynomial_t *p) {
  return b->nterms == p->nterms && arith_buffer_equal_monarray(b, p->mono);
}

/*
 * Comparison with a buffer b1
 * - b and b1 must be normalized.
 */
extern bool arith_buffer_equal_buffer(arith_buffer_t *b, arith_buffer_t *b1);


/*
 * Check whether b is constant
 * - b must be normalized
 */
static inline bool arith_buffer_is_constant(arith_buffer_t *b) {
  return b->nterms == 0 || (b->nterms == 1 && b->list->next->var == const_idx);
}


/*
 * Check whether b is constant and zero
 * - b must be normalized
 */
static inline bool arith_buffer_is_zero(arith_buffer_t *b) {
  return b->nterms == 0;
}

/*
 * Check whether b is constant and nonzero
 * - b must be normalized
 */
static inline bool arith_buffer_is_nonzero(arith_buffer_t *b) {
  return b->nterms == 1 && b->list->next->var == const_idx;
}

/*
 * Check whether b is constant and positive, negative, etc.
 * - b must be normalized
 */
static inline bool arith_buffer_is_pos(arith_buffer_t *b) {
  return b->nterms == 1 && b->list->next->var == const_idx 
    && q_is_pos(&b->list->next->coeff);
}

static inline bool arith_buffer_is_neg(arith_buffer_t *b) {
  return b->nterms == 1 && b->list->next->var == const_idx 
    && q_is_neg(&b->list->next->coeff);
}

static inline bool arith_buffer_is_nonneg(arith_buffer_t *b) {
  return b->nterms == 0 || 
    (b->nterms == 1 && b->list->next->var == const_idx 
     && q_is_pos(&b->list->next->coeff));
}

static inline bool arith_buffer_is_nonpos(arith_buffer_t *b) {
  return b->nterms == 0 || 
    (b->nterms == 1 && b->list->next->var == const_idx 
     && q_is_neg(&b->list->next->coeff));
}


/*
 * Check whether b == k + x for non-zero k and variable x
 * - b must be normalized
 */
extern bool arith_buffer_is_const_plus_var(arith_buffer_t *b, arith_var_t x);

/*
 * Check whether b == x for a variable x
 */
static inline bool arith_buffer_is_var(arith_buffer_t *b, arith_var_t x) {
  return b->nterms == 1 && b->list->next->var == x && q_is_one(&b->list->next->coeff);
}


/*
 * Check whether b is of the form a * (x - y) for two variables x and y
 * - b must be normalized
 */
extern bool arith_buffer_is_equality(arith_buffer_t *b, arith_var_t *x, arith_var_t *y);




/*
 * Buffer operations: in-place operations on b.
 */
extern void arith_buffer_negate(arith_buffer_t *b);

// v must be a valid variable
extern void arith_buffer_mul_var(arith_buffer_t *b, arith_var_t v);

// v must be a valid variable
extern void arith_buffer_mul_negvar(arith_buffer_t *b, arith_var_t v);

// a must be nonzero
extern void arith_buffer_mul_const(arith_buffer_t *b, rational_t *a);

// a must be nonzero
extern void arith_buffer_div_const(arith_buffer_t *b, rational_t *a);

// v must be a valid variable, a must be nonzero
extern void arith_buffer_mul_mono(arith_buffer_t *b, arith_var_t v, rational_t *a);

// v must be a valid variable
extern void arith_buffer_add_mono(arith_buffer_t *b, arith_var_t v, rational_t *a);

// v must be a valid variable
extern void arith_buffer_sub_mono(arith_buffer_t *b, arith_var_t v, rational_t *a);

// v must be a valid variable
extern void arith_buffer_add_var(arith_buffer_t *b, arith_var_t v);

// v must be a valid variable
extern void arith_buffer_sub_var(arith_buffer_t *b, arith_var_t v);

// no particular constraints
extern void arith_buffer_add_const(arith_buffer_t *b, rational_t *c);

// no particular constraints
extern void arith_buffer_sub_const(arith_buffer_t *b, rational_t *c);

// p1 must be normalized (and terminated by max_idx)
extern void arith_buffer_add_monarray(arith_buffer_t *b, monomial_t *p1);

// p1 must be normalized (and terminated by max_idx)
extern void arith_buffer_sub_monarray(arith_buffer_t *b, monomial_t *p1);

// p1 must be normalized (and terminated by max_idx)
extern void arith_buffer_mul_monarray(arith_buffer_t *b, monomial_t *p1);

// p1 must be normalized (and terminated by max_idx), a must be nonzero
extern void arith_buffer_add_const_times_monarray(arith_buffer_t *b, monomial_t *p1, rational_t *a);

// p1 must be normalized (and terminated by max_idx), a must be nonzero
extern void arith_buffer_sub_const_times_monarray(arith_buffer_t *b, monomial_t *p1, rational_t *a);

// p1 must be normalized (and terminated by max_idx), v1 must be a valid variable
extern void arith_buffer_add_var_times_monarray(arith_buffer_t *b, monomial_t *p1, arith_var_t v1);

// p1 must be normalized (and terminated by max_idx), v1 must be a valid variable
extern void arith_buffer_sub_var_times_monarray(arith_buffer_t *b, monomial_t *p1, arith_var_t v1);

// p1 must be normalized (and terminated by max_idx), v1 must be a valid variable, a must be nonzero 
extern void arith_buffer_add_mono_times_monarray(arith_buffer_t *b, monomial_t *p1, arith_var_t v1, rational_t *a);

// p1 must be normalized (and terminated by max_idx), v1 must be a valid variable, a must be nonzero 
extern void arith_buffer_sub_mono_times_monarray(arith_buffer_t *b, monomial_t *p1, arith_var_t v1, rational_t *a);

// p1 and p2 must be normalized and terminated by max_idx (they can be equal)
extern void arith_buffer_add_monarray_times_monarray(arith_buffer_t *b, monomial_t *p1, monomial_t *p2);

// p1 and p2 must be normalized and terminated by max_idx (they can be equal)
extern void arith_buffer_sub_monarray_times_monarray(arith_buffer_t *b, monomial_t *p1, monomial_t *p2);

// should work with b == b1 (but slow)
extern void arith_buffer_add_buffer(arith_buffer_t *b, arith_buffer_t *b1);

// should work with b == b1 (but slow)
extern void arith_buffer_sub_buffer(arith_buffer_t *b, arith_buffer_t *b1);

// b must be distinct from b1
extern void arith_buffer_mul_buffer(arith_buffer_t *b, arith_buffer_t *b1);

// no special constraints
extern void arith_buffer_square(arith_buffer_t *b);

// a must be nonzero, should work with b == b1
extern void arith_buffer_add_const_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a);

// a must be nonzero, should work with b == b1
extern void arith_buffer_sub_const_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a);

// v must be a valid variable, should work with b == b1
extern void arith_buffer_add_var_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_var_t v1);

// v must be a valid variable, should work with b == b1
extern void arith_buffer_sub_var_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_var_t v1);

// v must be a valid variable, a must be nonzero, should work with b == b1
extern void arith_buffer_add_mono_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_var_t v1, rational_t *a);

// v must be a valid variable, a must be nonzero, should work with b == b1
extern void arith_buffer_sub_mono_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_var_t v1, rational_t *a);

// b1 and b2 must be distinct from b (but b1 may be equal to b2)
extern void arith_buffer_add_buffer_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_buffer_t *b2);

// b1 and b2 must be distinct from b (but b1 may be equal to b2)
extern void arith_buffer_sub_buffer_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_buffer_t *b2);





#endif /* __POLYNOMIALS_H */
