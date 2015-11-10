/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Power products: x_1^d_1 ... x_n^d_n
 * - each x_i is a 32bit integer
 * - each exponent d_i is a positive integer
 *
 * There's a limit on the total degree (YICES_MAX_DEGREE) defined in 'yices_limits.h'.
 * If power products p1 and p2 have degree less than MAX_DEGREE
 * then degree(p1) + degree(p2) can be computed without overflow on 32bit numbers.
 * Power products (and polynomials) of degree >= YICES_MAX_DEGREE are not supported.
 */

#ifndef __POWER_PRODUCTS_H
#define __POWER_PRODUCTS_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#include "utils/tagged_pointers.h"

/*
 * Product:
 * - len = number of components
 * - prod = array of components, each component is a pair <var, exp>
 * - degree = sum of the exponents
 * - each variable is represented as a 32bit signed integer
 * When normalized:
 * - the variables are in increasing order
 * - there are no duplicate variables; each var occurs in a single pair
 * - the exponents are non-zero
 */
// pair <variable, exponent>
typedef struct {
  int32_t var;
  uint32_t exp;
} varexp_t;

// power product
typedef struct {
  uint32_t len;
  uint32_t degree;
  varexp_t prod[0]; // real size is len
} pprod_t;


/*
 * Buffer for intermediate computations.
 */
typedef struct {
  uint32_t size;    // size of the array prod
  uint32_t len;     // elements of prod currently used
  varexp_t *prod;
} pp_buffer_t;


/*
 * Maximal number of pairs <variable, exponent> in a product
 * - this is to ensure we can compute len * sizeof(varexp_t)
 *   on 32bits without overflow
 */
#define PPROD_MAX_LENGTH ((UINT32_MAX-sizeof(pprod_t))/sizeof(varexp_t))


/*
 * Maximal variable index: variables should be between 0 and MAX_PROD_VAR
 */
#define MAX_PPROD_VAR (INT32_MAX/2)





/*
 * POINTER TAGGING
 */

/*
 * Power product are part of the polynomial representation. But in many
 * cases, the polynomials are linear expressions (i.e., each power product
 * is either the empty product or a single variable with exponent 1). To
 * compactly encode the common case, we use tagged pointers and the
 * following conventions.
 * - the empty power product is the NULL pointer
 * - a single variable x is packed in a pprod_t pointer with tag bit set to 1
 *   (this gives a compact representation for x^1)
 * - otherwise, the product p is a pointer to an actual pprod_t object
 *
 * We also use a special end-marker in polynomial representations.
 * The end marker is larger than any other power product in the deglex ordering.
 */

/*
 * Empty product
 */
#define empty_pp ((pprod_t *) NULL)

/*
 * End marker: all bits are one
 */
#define end_pp ((pprod_t *) ~((uintptr_t) 0))

/*
 * Variable x encoded as a power product
 */
static inline pprod_t *var_pp(int32_t x) {
  assert(0 <= x && x <= MAX_PPROD_VAR);
  return (pprod_t *) tag_i32(x);
}

/*
 * Check whether p is empty or a variable
' */
static inline bool pp_is_empty(pprod_t *p) {
  return p == empty_pp;
}

static inline bool pp_is_var(pprod_t *p) {
  return has_int_tag(p);
}

/*
 * Get the variable index of p if pp_is_var(p) holds
 */
static inline int32_t var_of_pp(pprod_t *p) {
  assert(pp_is_var(p));
  return untag_i32(p);
}




/*
 * PRODUCT BUFFERS
 */

/*
 * Initialize a buffer of initial size n:
 * - initial value = empty product
 */
extern void init_pp_buffer(pp_buffer_t *b, uint32_t n);
extern void delete_pp_buffer(pp_buffer_t *b);

/*
 * Operations:
 * - reset to empty product
 * - set to or multiply by v
 * - set to or multiply v^d
 * - set to or multiply by v[0] * ... * v[n-1]
 * - set to or multiply by v[0]^d[0] * ... * v[n-1]^d[n-1]
 * all modify buffer b.
 *
 * The set_xxx operations do not normalize b.
 * The mul_xxx operations do normalize b.
 */
extern void pp_buffer_reset(pp_buffer_t *b);

extern void pp_buffer_set_var(pp_buffer_t *b, int32_t v);
extern void pp_buffer_set_varexp(pp_buffer_t *b, int32_t v, uint32_t d);
extern void pp_buffer_set_vars(pp_buffer_t *b, uint32_t n, int32_t *v);
extern void pp_buffer_set_varexps(pp_buffer_t *b, uint32_t n, int32_t *v, uint32_t *d);

extern void pp_buffer_mul_var(pp_buffer_t *b, int32_t v);
extern void pp_buffer_mul_varexp(pp_buffer_t *b, int32_t v, uint32_t d);
extern void pp_buffer_mul_vars(pp_buffer_t *b, uint32_t n, int32_t *v);
extern void pp_buffer_mul_varexps(pp_buffer_t *b, uint32_t n, int32_t *v, uint32_t *d);


/*
 * Lower-level operation: add v or v^d as a factor of b
 * - this does not normalize b
 */
extern void pp_buffer_push_var(pp_buffer_t *b, int32_t v);
extern void pp_buffer_push_varexp(pp_buffer_t *n, int32_t v, uint32_t d);


/*
 * Raise b to power d and normalize the result
 */
extern void pp_buffer_exponentiate(pp_buffer_t *b, uint32_t d);


/*
 * Assign or multiply b by a power-product p
 * - p must follow the pointer tagging conventions
 */
extern void pp_buffer_set_pprod(pp_buffer_t *b, pprod_t *p);
extern void pp_buffer_mul_pprod(pp_buffer_t *b, pprod_t *p);

/*
 * Copy src into b or multiply b by a
 */
extern void pp_buffer_copy(pp_buffer_t *b, pp_buffer_t *src);
extern void pp_buffer_mul_buffer(pp_buffer_t *b, pp_buffer_t *a);


/*
 * Normalize: remove x^0 and replace x^n * x^m by x^(n+m)
 * also sort in increasing variable order
 */
extern void pp_buffer_normalize(pp_buffer_t *b);

/*
 * Check whether b contains a trivial product
 * (either empty or a single variable with exponent 1)
 * - b must be normalized
 */
static inline bool pp_buffer_is_trivial(pp_buffer_t *b) {
  return (b->len == 0) || (b->len == 1 && b->prod[0].exp == 1);
}



/*
 * Degree computation
 */
extern uint32_t pp_buffer_degree(pp_buffer_t *b);

/*
 * Check whether the degree is less than MAX_DEGREE.
 */
extern bool pp_buffer_below_max_degree(pp_buffer_t *b);

/*
 * Degree of a variable x in product p
 * (0 if x does not occur in p).
 */
extern uint32_t pp_buffer_var_degree(pp_buffer_t *b, int32_t x);


/*
 * Convert b's content to a power-product object.
 * - b must be normalized.
 * - if b is empty or is of the form x^1 then the result is
 *   the appropriate tagged pointer.
 */
extern pprod_t *pp_buffer_getprod(pp_buffer_t *b);



/*
 * POWER PRODUCT OPERATIONS
 */

/*
 * All the operations assume p follows the tagged pointer
 * conventions.
 * - p = NULL denotes the empty product
 * - a tagged pointer x denotes the product (x^1)
 * - other wise, p is a pointer to an actual pprod_t structure
 *   that must be normalized
 */

/*
 * Degree of p
 * - p must be distinct from end_pp
 */
extern uint32_t pprod_degree(pprod_t *p);


/*
 * Check whether p's degree is below MAX_DEGREE
 * - p must be distinct from end_pp
 */
extern bool pprod_below_max_degree(pprod_t *p);


/*
 * Degree of variable x in product p
 * - returns 0 if x does not occur in p
 * - p must be distinct from end_pp
 */
extern uint32_t pprod_var_degree(pprod_t *p, int32_t x);


/*
 * Lexicographic ordering:
 * - lex_cmp(p1, p2) < 0 means p1 < p2
 * - lex_cmp(p1, p2) = 0 means p1 = p2
 * - lex_cmp(p1, p2) > 0 means p2 < p1
 *
 * The order is defined by
 *   x_1^d_1 ... x_n^d_n < x_1^c_1 ... x_n^c_n
 * if, for some index i, we have
 *   d_1 = c_1 ... d_{i-1} = c_{i-1} and d_i > c_i.
 *
 * p1 and p2 must be distinct from end_pp
 */
extern int32_t pprod_lex_cmp(pprod_t *p1, pprod_t *p2);


/*
 * Degree then lex ordering. This ordering is defined by
 *  p1 < p2 if degree(p1) < degree(p2)
 *          or degree(p1) = degree(p2) and (p1 < p2 in lex ordering)
 *
 * That's the ordering we use for normalizing polynomials.
 * p1 or p2 (or both) may be equal to the end marker end_pp.
 *
 * There are three cases:
 * - if p1 = end_pp then
 *     pprod_precedes(p1, p2) is false for any p2
 * - if p1 != end_pp and p2 = end_pp then
 *     pprod_precedes(p1, p2) is true
 * - otherwise,
 *     pprod_precedes(p1, p2) is true
 *        iff p1 < p2 in the deglex ordering
 */
extern bool pprod_precedes(pprod_t *p1, pprod_t *p2);


/*
 * Check whether p1 and p2 are equal
 * - p1 and p2 must be distinct from end_pp
 */
extern bool pprod_equal(pprod_t *p1, pprod_t *p2);


/*
 * Divisibility test: returns true if p1 is a divisor of p2
 * - p1 and p2 must be distinct from end_pp
 */
extern bool pprod_divides(pprod_t *p1, pprod_t *p2);


/*
 * Same thing but also computes the quotient (p2/p1) in b
 * - p1 and p2 must be distinct from end_pp
 */
extern bool pprod_divisor(pp_buffer_t *b, pprod_t *p1, pprod_t *p2);


/*
 * Free a power-product
 * - p must be the result of pp_buffer_getprod or make_pprod.
 * - do nothing if p is empty or a variable.
 */
extern void free_pprod(pprod_t *p);





/*
 * LOW-LEVEL OPERATIONS
 */

/*
 * Check whether a and b (both of length n) are equal
 * - both a and b must be normalized
 */
extern bool varexp_array_equal(varexp_t *a, varexp_t *b, uint32_t n);

/*
 * Build a pproduct by making a copy of a
 * - a must be normalized
 * - n must be the length of a
 * - n must be less than PPROD_MAX_LENGTH
 */
extern pprod_t *make_pprod(varexp_t *a, uint32_t n);




#endif /* __POWER_PRODUCTS_H */
