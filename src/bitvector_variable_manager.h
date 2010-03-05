/*
 * Manager for bitvector variables.
 * Polynomial manager + extra data attached to each variable:
 * - its size in bit (except for const_idx)
 * - an optional array of bit-expression it's mapped to 
 */

#ifndef __BITVECTOR_VARIABLE_MANAGER_H
#define __BITVECTOR_VARIABLE_MANAGER_H

#include <assert.h>
#include <stdint.h>

#include "polynomial_manager.h"
#include "bit_expr.h"


/*
 * manager:
 * - pm = manager for hash-consing of varproducts
 * - bm = table for construction of bit expressions
 * - bitsize[i] = size of variable i (number of bits)
 * - bit[i] = array of bit expressions attached to i
 */
typedef struct {
  polynomial_manager_t pm;
  uint32_t *bitsize;
  bit_t **bit;  
  node_table_t *bm;
} bv_var_manager_t;


/*
 * Initialize a manager with initial size = n.
 * - node_table = the attached table of bit expressions
 */
extern void init_bv_var_manager(bv_var_manager_t *m, uint32_t n, node_table_t *node_table);

/*
 * Delete m: all variable products constructed with m are freed.
 * All bit arrays attached to these variables are also freed.
 */
extern void delete_bv_var_manager(bv_var_manager_t *m);

/*
 * Declare a fresh bitvector variable: returns its id.
 * - size = number of bits
 * - term_id = index of the term mapped to that variable.
 */
extern int32_t bv_var_manager_new_var(bv_var_manager_t *m, uint32_t size, int32_t term_id);

/*
 * Delete variable v
 * - if v has a bitarray attached, the nodes in that array must be deleted
 *   outside this function, using the bit-expression garabage collector.
 */
extern void bv_var_manager_delete_var(bv_var_manager_t *m, int32_t v);

/*
 * Return the variable representing v1 * v2.
 * Both variables must have the same bitsize. The result also has the same size.
 */
static inline int32_t bv_var_manager_mul_var(bv_var_manager_t *m, int32_t v1, int32_t v2) {
  return polymanager_mul_var(&m->pm, v1, v2);
}

/*
 * Get the auxiliary variable representing v[0] * ... * v[n-1]
 * each v[i] must be primitive, all variables must have the same size 
 */
static inline int32_t bv_var_manager_product_vars(bv_var_manager_t *m, int32_t n, int32_t *v) {
  return polymanager_product_vars(&m->pm, n, v);    
}

/*
 * Same thing with exponents: product of v[0]^d[0]  to v[n-1]^d[n-1]
 * each v[i] must be primitve and d[i] must be non-negative.
 */
static inline int32_t bv_var_manager_product_varexps(bv_var_manager_t *m, int32_t n, int32_t *v, int32_t *d) {
  return polymanager_product_varexps(&m->pm, n, v, d);
}

/*
 * Get primitive variables of v: add them to vector u
 */
static inline void bv_var_manager_get_vars(bv_var_manager_t *m, int32_t v, ivector_t *u) {
  polymanager_get_vars(&m->pm, v, u);
}

/*
 * Get the terms attached to v's primitive variables
 */
static inline void bv_var_manager_get_terms(bv_var_manager_t *m, int32_t v, ivector_t *u) {
  polymanager_get_terms(&m->pm, v, u);
}


/*
 * Return the bit-expression array attached to variable v.  If no
 * array is currently attached, then fresh nodes are allocated and
 * the array is initialized.
 */
extern bit_t *bv_var_manager_get_bit_array(bv_var_manager_t *m, int32_t v);


/*
 * Return the index of bit-expression bit in the array attached to variable v
 * - v must be a valid variable
 * - return -1 if bit does not occur in the array (or if v has no array attached)
 */
extern int32_t bv_var_manager_get_index_of_node(bv_var_manager_t *m, int32_t v, node_t bit);



/*
 * Return the bit array attached to v (or NULL if there's none).
 */
static inline bit_t *bv_var_bit_array(bv_var_manager_t *m, int32_t v) {
  assert(polymanager_var_is_valid(&m->pm, v));
  return m->bit[v];
}

/*
 * Return bitsize of v
 */
static inline uint32_t bv_var_bitsize(bv_var_manager_t *m, int32_t v) {
  assert(polymanager_var_is_valid(&m->pm, v));
  return m->bitsize[v];
}




/*
 * Other data inherited from polymanager
 */
static inline int32_t bv_var_manager_var_degree(bv_var_manager_t *m, int32_t i) {
  return polymanager_var_degree(&m->pm, i);
}

static inline bool bv_var_manager_var_is_primitive(bv_var_manager_t *m, int32_t i) {
  return polymanager_var_is_primitive(&m->pm, i);
}

static inline bool bv_var_manager_var_is_const(bv_var_manager_t *m, int32_t i) {
  return polymanager_var_is_const(&m->pm, i);
}

static inline bool bv_var_manager_var_is_aux(bv_var_manager_t *m, int32_t i) {
  return polymanager_var_is_aux(&m->pm, i);
}

static inline int32_t bv_var_manager_term_of_var(bv_var_manager_t *m, int32_t i) {
  return polymanager_var_index(&m->pm, i);
}

static inline varprod_t *bv_var_manager_var_product(bv_var_manager_t *m, int32_t i) {
  return polymanager_var_product(&m->pm, i);
}


/*
 * Set (or change) the term index for variable i
 */
static inline void bv_var_manager_set_term_of_var(bv_var_manager_t *m, int32_t i, int32_t term_id) {
  polymanager_set_var_index(&m->pm, i, term_id);
}




#endif
