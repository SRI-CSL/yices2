/*
 * The Yices SMT Solver. Copyright 2016 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Support for constructing Mixed-integer Gomory cuts.
 *
 * A Gomory cut requires:
 *
 * 1) a term  a_1 x_1 + ... + a_n x_n 
 *    that is required to be integer for all feasible solutions.
 *
 * 2) bounds on all the variables x_i (one bound per variable)
 *    the bound on x_i can either be a lower bound (x_i >= l_i)
 *    or an upper bound (x_i <= u_i). We assume x_1 ... x_k have
 *    lower bounds and x_k+1 ... x_n have upper bounds.
 *
 * 3) the sum b = a_1 l_1 + ... + a_k l_k + a_k+1 u_k+1 ... + a_n u_n
 *    must not be an integer.
 *
 * To build the cut:
 *
 * 1) first compute the fractional part f of b. Since b is not an integer,
 *    we have 0 < f < 1.
 *
 * 2) got through all variables x_1, ..., x_n
 *
 *    if x_i is an integer variable with lower bound (x_i >= l_i)
 *      compute f_i = fractional part of a_i.
 *      if f_i > 1 - f,   replace a_i by f_i       (f_i > 0)
 *      if f_i <= 1 - f,  replace a_i by f_i - 1   (f_i - 1 < 0)
 *
 *    if x_i is an integer variable with upper bound (x_i <= u_i)
 *      compute f_i = fractional part of a_i
 *      if f_i < f,   replace a_i by f_i
 *      if f_i >= f,  replace a_i by f_i - 1 
 *
 *
 * 3) after this pass, build a term (c_i * (x_i - l_i)) or (c_i * (x_i - u_i)) for
 *    every variable:
 *
 *    if a_i > 0 and the bound on x_i is l_i,  c_i is    a_i/(1-f)
 *    if a_i > 0 and the bound on x_i is u_i,  c_i is   -a_i/f
 *    if a_i < 0 and the bound on x_i is l_i,  c_i is   -a_i/f
 *    if a_i < 0 and the bound on x_i is u_i,  c_i is    a_i/(1-f)
 *
 * 4) the cut is the constraint:
 *    
 *    c_1 (x_1 - l_1) + ... + c_k (x_k - l_k) + c_k+1 (x_k+1 - u_k+1) + ... + c_n (x_n - u_n) >= 1.
 *
 */


#ifndef __GOMORY_CUTS_H
#define __GOMORY_CUTS_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "terms/poly_buffer.h"
#include "terms/rationals.h"


/*
 * Auxiliary structure to store the term a_1 x_1 + ... + a_n x_n
 * and the bounds.
 *
 * For each i, we store
 * - coefficient a_i
 * - bound b_i
 * - variable x_i
 * - a tag tag_i, indicating wheher x_i is an integer variable
 *   and whether the bound is lower or upper.
 * For now, we require the bounds to be rational numbers (although
 * the cut would work too with extended rationals).
 *
 * Flag for variable i are stored in the two lower bits of tag[i]
 * - bit 0 --> variable type: 1 means integer, 0 means not integer
 * - bit 1 --> bound type: 1 means lower bound, 0 means upper bound
 */
typedef struct gomory_vector_s {
  uint8_t *tag;
  int32_t *var;
  rational_t *coeff;
  rational_t *bound;
  uint32_t nelems;
  uint32_t size;

  // auxiliary components for computations
  rational_t sum;           // store sum a_i * bound_i
  rational_t fraction;      // store f = fractional part of the sum
  rational_t ext;           // store 1 - f

  rational_t aux_fraction;  // store f_i = a_i - floor(a_i)
  rational_t aux_coeff;     // store c_i
  rational_t aux;
} gomory_vector_t;


#define MAX_GOMORY_VECTOR_SIZE (UINT32_MAX/sizeof(rational_t))
#define DEF_GOMORY_VECTOR_SIZE 16

#define GOMORY_VTYPE_MASK ((uint8_t)1)
#define GOMORY_BTYPE_MASK ((uint8_t)2)



/*
 * Initialization: use the default size
 * - nelem is 0
 */
extern void init_gomory_vector(gomory_vector_t *v);

/*
 * Reset: empty the vector, also reset all the rationals to 0
 */
extern void reset_gomory_vector(gomory_vector_t *v);

/*
 * Delete: free memory
 */
extern void delete_gomory_vector(gomory_vector_t *v);

/*
 * Add an element to the vector:
 * - x = variable
 * - a = coefficient
 * - b = bound
 * - is_int: true if x is an integer variable
 * - is_lb:  true if b is a lower bound (i.e., x >= b)
 *
 * Important: if x is an integer variable then the bound must be
 * and integer constant.
 */
extern void gomory_vector_add_elem(gomory_vector_t *v, int32_t x, rational_t *a, rational_t *b, 
				   bool is_int, bool is_lb);


/*
 * Check whether variable i is integer
 */
static inline bool gomory_var_is_int(gomory_vector_t *v, uint32_t i) {
  assert(i < v->nelems);
  return v->tag[i] & GOMORY_VTYPE_MASK;
}

static inline bool gomory_var_is_not_int(gomory_vector_t *v, uint32_t i) {
  return !gomory_var_is_int(v, i);
}

/*
 * Check whether the bound on variable is is lower or upper bound.
 */
static inline bool gomory_bound_is_lb(gomory_vector_t *v, uint32_t i) {
  assert(i < v->nelems);
  return v->tag[i] & GOMORY_BTYPE_MASK;
}

static inline bool gomory_bound_is_ub(gomory_vector_t *v, uint32_t i) {
  return !gomory_bound_is_lb(v, i);
}

/*
 * Build a tag:
 * - is_int: true means the variable is an integer
 * - is_lb: true means the bound is a lower bound
 */
static inline uint8_t gomory_tag(bool is_int, bool is_lb) {
  return (uint8_t) (2*is_lb + is_int);
}


/*
 * Build the Gomory cut from vector v:
 * - the cut returned in of the form (poly >= 0)
 * - this function stores poly in buffer
 *
 * Return false is the cut can't be constructed (i.e., the fraction f is 0)
 */
extern bool make_gomory_cut(gomory_vector_t *v, poly_buffer_t *buffer);


#endif
