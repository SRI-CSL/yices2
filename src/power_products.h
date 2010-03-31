/*
 * Power products: x_1^d_1 ... x_n^d_n 
 * - each x_i is a 32bit integer
 * - each exponent d_i is a positive integer
 */

#ifndef __POWER_PRODUCTS_H
#define __POWER_PRODUCTS_H

#include <stdint.h>
#include <stdbool.h>

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
 * Maximal degree: to detect overflows in product computations.
 * - bound: if p1 and p2 have degree less than MAX_DEGREE
 *   then degree(p1 * p2) can be computed without overflow on 32bit numbers
 */
#define MAX_DEGREE (UINT32_MAX/2)


/*
 * Maximal number of pairs <variable, exponent> in a product
 * - this is to ensure we can compute len * sizeof(varexp_t)
 *   on 32bits without overflow
 */ 
#define PPROD_MAX_LENGTH ((UINT32_MAX-sizeof(pprod_t))/sizeof(varexp_t))


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
 * Assign or multiply b by a power-product p
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

static inline uint32_t pprod_degree(pprod_t *p) {
  return p->degree;
}

/*
 * Check whether the degree is less than MAX_DEGREE.
 */
extern bool pp_buffer_below_max_degree(pp_buffer_t *b);

static inline bool pprod_below_max_degree(pprod_t *p) {
  return p->degree < MAX_DEGREE;
}

/*
 * Degree of a variable x in product p
 * (0 if x does not occur in p).
 */
extern uint32_t pp_buffer_var_degree(pp_buffer_t *b, int32_t x);
extern uint32_t pprod_var_degree(pprod_t *p, int32_t x);


/*
 * Hash code
 */
extern uint32_t pp_buffer_hash(pp_buffer_t *b);
extern uint32_t pprod_hash(pprod_t *p);


/*
 * Allocate and construct a pprod object from the content of b.
 * - b must be normalized.
 */
extern pprod_t *pp_buffer_getprod(pp_buffer_t *b);



/*
 * Comparison:
 * - lex_cmp(p1, p2) < 0 means p1 < p2
 * - lex_cmp(p1, p2) = 0 means p1 = p2
 * - lex_cmp(p1, p2) > 0 means p2 < p1
 *
 * The order is defined by
 *   x_1^d_1 ... x_n^d_n < x_1^c_1 ... x_n^c_n
 * if, for some index i, we have
 *   d_1 = c_1 ... d_{i-1} = c_{i-1} and d_i > c_i.
 */
extern int32_t pprod_lex_cmp(pprod_t *p1, pprod_t *p2);

/*
 * Check whether p1 and p2 are equal
 */
extern bool pprod_equal(pprod_t *p1, pprod_t *p2);

/*
 * Divisibility test: returns true if p1 is a divisor of p2
 */
extern bool pprod_divides(pprod_t *p1, pprod_t *p2);

/*
 * Same thing but also computes the divisor in b
 */
extern bool pprod_divisor(pp_buffer_t *b, pprod_t *p1, pprod_t *p2);




/*
 * LOW-LEVEL OPERATIONS
 * - direct operations on arrays of pairs <var, exponent>
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
