/*
 * Manager for arithmetic variables. Extension of polynomial_manager
 * with bitvector flag for storing variable type (integer or not).
 */

#ifndef __ARITHMETIC_VARIABLE_MANAGER_H
#define __ARITHMETIC_VARIABLE_MANAGER_H

#include <assert.h>
#include <stdint.h>

#include "polynomial_manager.h"
#include "bitvectors.h"


// polynomial_manager + i_flag vector
typedef struct {
  polynomial_manager_t pm;
  byte_t *i_flag;   // one bit per variable: 1 if integer, 0 if real
} arithvar_manager_t;


/*
 * Initialize manager m with initial size = n.
 */
extern void init_arithvar_manager(arithvar_manager_t *m, uint32_t n);

/*
 * Delete m: all variable products constructed with m are freed.
 */
extern void delete_arithvar_manager(arithvar_manager_t *m);

/*
 * Declare a fresh arithmetic variable: returns its id.
 * - is_int = true means that var is integer.
 * - term_id = index of the term mapped to that variable.
 */
extern int32_t arithvar_manager_new_var(arithvar_manager_t *m, bool is_int, int32_t term_id);

/*
 * Delete variable v
 */
static inline void arithvar_manager_delete_var(arithvar_manager_t *m, int32_t v) {
  polymanager_delete_var(&m->pm, v);
}

/*
 * Return the variable representing v1 * v2
 * - if v1 * v2 reduces to a single primitive var v, then the result is v,
 * - otherwise the result is an auxiliary var
 */
static inline int32_t arithvar_manager_mul_var(arithvar_manager_t *m, int32_t v1, int32_t v2) {
  return polymanager_mul_var(&m->pm, v1, v2);
}

/*
 * Get the auxiliary variable representing v[0] * ... * v[n-1]
 * each v[i] must be primitive
 */
static inline int32_t arithvar_manager_product_vars(arithvar_manager_t *m, int32_t n, int32_t *v) {
  return polymanager_product_vars(&m->pm, n, v);
}

/*
 * Same thing with exponents: product of v[0]^d[0]  to v[n-1]^d[n-1]
 * each v[i] must be primitve and d[i] must be non-negative.
 */
static inline int32_t arithvar_manager_product_varexps(arithvar_manager_t *m, int32_t n, int32_t *v, int32_t *d) {
  return polymanager_product_varexps(&m->pm, n, v, d);
}


/*
 * Get primitive variables of v: add them to vector u
 */
static inline void arithvar_manager_get_vars(arithvar_manager_t *m, int32_t v, ivector_t *u) {
  polymanager_get_vars(&m->pm, v, u);
}

/*
 * Get the terms attached to v's primitive variables
 */
static inline void arithvar_manager_get_terms(arithvar_manager_t *m, int32_t v, ivector_t *u) {
  polymanager_get_terms(&m->pm, v, u);
}


/*
 * Compute the degree of x in the product represented by variable i
 * - x must be a primitive variable in m
 * - i v is primitive, return 1 if x == i, 0 if x != i
 * - otherwise, get the exponent of x in the product i
 */
static inline int32_t arithvar_manager_var_degree_in_prod(arithvar_manager_t *m, int32_t i, int32_t x) {
  return polymanager_var_degree_in_prod(&m->pm, i, x);
}

/*
 * Access to manager data
 */
static inline bool arithvar_manager_var_is_int(arithvar_manager_t *m, int32_t i) {
  assert(polymanager_var_is_valid(&m->pm, i));
  return tst_bit(m->i_flag, i);
}

static inline bool arithvar_manager_var_is_real(arithvar_manager_t *m, int32_t i) {
  assert(polymanager_var_is_valid(&m->pm, i));
  return ! tst_bit(m->i_flag, i);
}

static inline int32_t arithvar_manager_var_degree(arithvar_manager_t *m, int32_t i) {
  return polymanager_var_degree(&m->pm, i);
}

static inline bool arithvar_manager_var_is_primitive(arithvar_manager_t *m, int32_t i) {
  return polymanager_var_is_primitive(&m->pm, i);
}

static inline bool arithvar_manager_var_is_const(arithvar_manager_t *m, int32_t i) {
  return polymanager_var_is_const(&m->pm, i);
}

static inline bool arithvar_manager_var_is_aux(arithvar_manager_t *m, int32_t i) {
  return polymanager_var_is_aux(&m->pm, i);
}

static inline int32_t arithvar_manager_term_of_var(arithvar_manager_t *m, int32_t i) {
  return polymanager_var_index(&m->pm, i);
}

static inline varprod_t *arithvar_manager_var_product(arithvar_manager_t *m, int32_t i) {
  return polymanager_var_product(&m->pm, i);
}


/*
 * Number of elements = number of variables (unless variables are deleted)
 */
static inline uint32_t arithvar_manager_nelems(arithvar_manager_t *m) {
  return polymanager_nelems(&m->pm);
}

/*
 * Set (or change) the term index for variable i
 */
static inline void arithvar_manager_set_term_of_var(arithvar_manager_t *m, int32_t i, int32_t term_id) {
  polymanager_set_var_index(&m->pm, i, term_id);
}


#endif
