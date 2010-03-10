/*
 * Polynomial manager: hash consing for variable products.
 * Store data for two kinds of variables:
 * - primitive variables are attached to a term index (int32_t)
 * - auxiliary variables represent products of primitive variables
 * Index 0 is reserved for the empty product.
 */

#ifndef __POLYNOMIAL_MANAGER_H
#define __POLYNOMIAL_MANAGER_H

#include <assert.h>
#include <stdint.h>
#include <stdbool.h>

#include "varproducts.h"
#include "symbol_tables.h"
#include "int_hash_tables.h"
#include "int_vectors.h"


/*
 * For a variable index i and manager m:
 * 1) m->degree[i] = degree of the product represented by i
 *    if m->degree[i] = 1 then i is a primitive variable
 *    otherwise, i is an auxiliary variable
 * 2) m->desc[i] = descriptor 
 *    the descriptor is either an integer or a varprod
 *    if m->degree[i] = 1 then 
 *    m->desc[i].integer is the index of the term represented by i
 *    if m->degree[i] != 1 then m->desc[i].prod = product of 
 *    variables represented by 1.
 *
 * For i = const_idx, we have m->degree[i] = 0 and m->desc[i].prod =
 * empty product.
 *
 * Other fields in manager m:
 * - free_list, size, nelems for allocation of new indices.
 * - m->int_hash_table: table for hash consing of products.
 * - m->vpbuffer: auxiliary buffer for constructing products.
 *
 * Hooks used by arithmetic_variable_manager and bitvector_variable_manager:
 * - m->notify_resize(m, old_size, new_size) is called whenever
 *   the manager size is increased.
 * - m->notify_new_prod(m, i, prod) is called whenever a new product (prod)
 *   is stored. i is the auxiliary variable index.
 */

// special indices
enum {
  null_idx = -1,
  const_idx = 0,
  max_idx = INT32_MAX,
};

// descriptor: either a varprod pointer or an integer
typedef union {
  int32_t integer;
  varprod_t *prod;
} polyvar_desc_t;

// hook functions
typedef void (*resize_notifier_t)(void *, uint32_t, uint32_t);
typedef void (*newprod_notifier_t)(void *, int32_t, varprod_t *);

// manager
typedef struct {
  int32_t *degree; // 1 for primitive variables
  polyvar_desc_t *desc;

  uint32_t size;
  uint32_t nelems;
  int32_t free_idx;

  int_htbl_t htbl;
  vpbuffer_t vpbuffer;

  resize_notifier_t notify_resize;
  newprod_notifier_t notify_newprod;
} polynomial_manager_t;


/*
 * Maximal size of the manager tables:
 * - we want to make sure there's no arithmetic overflow when 
 *   computing n * sizeof(polyvar_desc_t)
 * - also ensure all variables have an index smaller than max_idx
 */
#define MAX_VARTBL_SIZE (UINT32_MAX/sizeof(polyvar_desc_t))

/*
 * Initialize a manager with initial size = n.
 */
extern void init_polymanager(polynomial_manager_t *m, uint32_t n);


/*
 * Delete m: all variable products constructed with m are freed.
 */
extern void delete_polymanager(polynomial_manager_t *m);


/*
 * Set the resize notifier
 */
static inline void polymanager_set_resize_notifier(polynomial_manager_t *m, resize_notifier_t func) {
  m->notify_resize = func;
}

/*
 * Set the newprod notifier
 */
static inline void polymanager_set_newprod_notifier(polynomial_manager_t *m, newprod_notifier_t func) {
  m->notify_newprod = func;
}

/*
 * Declare a fresh variable with attached term_index, returns its id.
 */
extern int32_t polymanager_new_var(polynomial_manager_t *m, int32_t term_index);

/*
 * Return the variable representing v1 * v2
 * - if v1 * v2 reduces to a single primitive var v, then the result is v,
 * - otherwise the result is an auxiliary var
 */
extern int32_t polymanager_mul_var(polynomial_manager_t *m, int32_t v1, int32_t v2);

/*
 * Get the auxiliary variable representing v[0] * ... * v[n-1]
 * each v[i] must be primitive
 */
extern int32_t polymanager_product_vars(polynomial_manager_t *m, int32_t n, int32_t *v);  

/*
 * Same thing with exponents: product of v[0]^d[0]  to v[n-1]^d[n-1]
 * each v[i] must be primitive and d[i] must be non-negative.
 */
extern int32_t polymanager_product_varexps(polynomial_manager_t *m, int32_t n, int32_t *v, int32_t *d);  

/*
 * Delete variable v
 */
extern void polymanager_delete_var(polynomial_manager_t *m, int32_t v);

/*
 * var_precedes(m, v, w) returns true if v < w.
 *
 * - the order on variables is defined by 
 *   v < w iff degree(v) < degree(w) 
 *         or  degree(v) = degree(w) = 1 and v < w
 *         or  degree(v) = degree(w) > 1 and prod(v) < prod(w) in lexical ordering
 */
extern bool polymanager_var_precedes(polynomial_manager_t *m, int32_t v, int32_t w);


/*
 * Collect the primitive variables of v: add them to vector u
 * - either v itself or all variables occurring in product 
 */
extern void polymanager_get_vars(polynomial_manager_t *m, int32_t v, ivector_t *u);


/*
 * Collect the terms occurring in variable v: add them to vector u
 * - for a primitive variable v, add the term = m->desc[v]
 * - for an auxiliaty variable v, add m->desc[w] for every w in product v
 */
extern void polymanager_get_terms(polynomial_manager_t *m, int32_t v, ivector_t *u);


/*
 * Compute the degree of x in the product represented by variable v
 * - x must be a primitive variable in m
 * - if v is primitive, return 1 if x == v, 0 if x != v
 * - otherwise, get the exponent of x in the product v
 */
extern int32_t polymanager_var_degree_in_prod(polynomial_manager_t *m, int32_t v, int32_t x);



/*
 * Access to manager data
 */
static inline bool polymanager_is_full(polynomial_manager_t *m) {
  return (m->free_idx < 0) && (m->nelems == m->size);
}

static inline uint32_t polymanager_nelems(polynomial_manager_t *m) {
  return m->nelems;
}


static inline bool polymanager_var_is_valid(polynomial_manager_t *m, int32_t i) {
  return 0 <= i && i < ((int32_t) m->nelems);
}

static inline int32_t polymanager_var_degree(polynomial_manager_t *m, int32_t i) {
  assert(0 <= i && i < ((int32_t) m->nelems));
  return m->degree[i];
}

static inline bool polymanager_var_is_primitive(polynomial_manager_t *m, int32_t i) {
  assert(0 <= i && i < ((int32_t) m->nelems));
  return m->degree[i] == 1;
}

static inline bool polymanager_var_is_const(polynomial_manager_t *m, int32_t i) {
  assert(0 <= i && i < ((int32_t) m->nelems));
  return i == const_idx;
}

static inline bool polymanager_var_is_aux(polynomial_manager_t *m, int32_t i) {
  assert(0 <= i && i < ((int32_t) m->nelems));
  return m->degree[i] != 1;
}

static inline int32_t polymanager_var_index(polynomial_manager_t *m, int32_t i) {
  assert(polymanager_var_is_primitive(m, i));
  return m->desc[i].integer;
}

static inline varprod_t *polymanager_var_product(polynomial_manager_t *m, int32_t i) {
  assert(polymanager_var_is_aux(m, i));
  return m->desc[i].prod;
}


/*
 * Set (or change) the term index for variable i
 */
static inline void polymanager_set_var_index(polynomial_manager_t *m, int32_t i, int32_t term_index) {
  assert(polymanager_var_is_primitive(m, i));
  m->desc[i].integer = term_index;
}


#endif
