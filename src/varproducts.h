/*
 * Products of variables: x_1^d_1 ... x_n^d_n 
 */

#ifndef __VARPRODUCTS_H
#define __VARPRODUCTS_H

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

typedef struct {
  uint32_t len;
  uint32_t degree;
  varexp_t prod[0]; // real size is len
} varprod_t;


/*
 * Buffer for intermediate computations.
 */
typedef struct {
  uint32_t size;    // size of the array prod
  uint32_t len;     // elements of prod currently used
  varexp_t *prod;
} vpbuffer_t;


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
#define VARPROD_MAX_LENGTH ((UINT32_MAX-sizeof(varprod_t))/sizeof(varexp_t))


/*
 * Initialize a buffer of initial size n:
 * - initial value = empty product
 */
extern void init_vpbuffer(vpbuffer_t *b, uint32_t n);
extern void delete_vpbuffer(vpbuffer_t *b);

/*
 * Operations:
 * - reset to empty product
 * - set to or multiply by v
 * - set to or multiply v^d
 * - set to or multiply by v[0] * ... * v[n-1]
 * - set to or multiply by v[0]^d[0] * ... * v[n-1]^d[n-1]
 * all modify buffer b.
 */
extern void vpbuffer_reset(vpbuffer_t *b);

extern void vpbuffer_set_var(vpbuffer_t *b, int32_t v);
extern void vpbuffer_set_varexp(vpbuffer_t *b, int32_t v, uint32_t d);
extern void vpbuffer_set_vars(vpbuffer_t *b, uint32_t n, int32_t *v);
extern void vpbuffer_set_varexps(vpbuffer_t *b, uint32_t n, int32_t *v, uint32_t *d);

extern void vpbuffer_mul_var(vpbuffer_t *b, int32_t v);
extern void vpbuffer_mul_varexp(vpbuffer_t *b, int32_t v, uint32_t d);
extern void vpbuffer_mul_vars(vpbuffer_t *b, uint32_t n, int32_t *v);
extern void vpbuffer_mul_varexps(vpbuffer_t *b, uint32_t n, int32_t *v, uint32_t *d);

/*
 * Assign or multiply b by a power-product p
 */
extern void vpbuffer_set_varprod(vpbuffer_t *b, varprod_t *p);
extern void vpbuffer_mul_varprod(vpbuffer_t *b, varprod_t *p);

/*
 * Copy src into b or multiply b by a
 */
extern void vpbuffer_copy(vpbuffer_t *b, vpbuffer_t *src);
extern void vpbuffer_mul_buffer(vpbuffer_t *b, vpbuffer_t *a);


/*
 * Normalize: remove x^0 and replace x^n * x^m by x^(n+m)
 * also sort in increasing variable order
 */
extern void vpbuffer_normalize(vpbuffer_t *b);

/*
 * Check whether b contains a trivial product
 * (either empty or a single variable with exponent 1)
 * - b must be normalized
 */
static inline bool vpbuffer_is_trivial(vpbuffer_t *b) {
  return (b->len == 0) || (b->len == 1 && b->prod[0].exp == 1);
}


/*
 * Degree computation
 */
extern uint32_t vpbuffer_degree(vpbuffer_t *b);


/*
 * Check whether the degree is less than MAX_DEGREE.
 */
extern bool vpbuffer_below_max_degree(vpbuffer_t *b);


/*
 * Degree of a variable x in product p
 */
extern uint32_t vpbuffer_var_degree(vpbuffer_t *b, int32_t x);
extern uint32_t varprod_var_degree(varprod_t *p, int32_t x);



/*
 * Allocate and construct a varprod object from the content of b.
 * - b must be normalized.
 */
extern varprod_t *vpbuffer_getprod(vpbuffer_t *b);



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
extern int32_t varprod_lex_cmp(varprod_t *p1, varprod_t *p2);

/*
 * Check whether p1 and p2 are equal
 */
extern bool varprod_equal(varprod_t *p1, varprod_t *p2);

/*
 * Divisibility test: returns true if p1 is a divisor of p2
 */
extern bool varprod_divides(varprod_t *p1, varprod_t *p2);

/*
 * Same thing but also computes the divisor in b
 */
extern bool varprod_divisor(vpbuffer_t *b, varprod_t *p1, varprod_t *p2);




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
 * Build a varproduct by making a copy of a
 * - a must be normalized
 * - n must be the length of a
 * - n must be less than VARPROD_MAX_LENGTH
 */
extern varprod_t *make_varprod(varexp_t *a, uint32_t n);



#endif /* __VARPRODUCTS_H */
