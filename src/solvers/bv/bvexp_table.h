/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * For bitvector solver: map variable indices to an expanded polynomial.
 * This is used to detect whether two bitvector expression are equal
 * modulo bitvector arithmetic.
 */

#ifndef __BVEXP_TABLE_H
#define __BVEXP_TABLE_H

#include <stdint.h>
#include <assert.h>

#include "solvers/bv/bv_vartable.h"
#include "terms/bvarith64_buffers.h"
#include "terms/bvarith_buffers.h"
#include "utils/int_hash_tables.h"


/*
 * Table:
 * - for a variable index i:
 *   def[i] = NULL if i has no expanded form
 *   otherwise def[i] is a list of bitvector monomials.
 * - depending on the variable's bitsize, def[i] is either
 *   a bvmlist_t pointer (more than 64bits) or a bvmlist64_t pointer
 *   (1 to 64bits).
 * - nvars = number of variables present (nvars <= size)
 * - size = total size of array def
 *
 * Other components:
 * - vtbl = pointer to the associated vartable
 * - store, store64 = object stores used for allocating monomials
 * - pprods = table for building power products
 * - htbl = hash table
 *
 * Auxiliary buffers used in internal computations
 * - aux = bvarith_buffer
 * - aux64 = bvarith64_buffer
 * - pp = pp_buffer
 * - bvconst: bvconstant buffer
 */
typedef struct bvexp_table_s {
  uint32_t nvars;
  uint32_t size;
  void **def;
  bv_vartable_t *vtbl;
  object_store_t store;
  object_store_t store64;
  pprod_table_t pprods;
  int_htbl_t htbl;

  bvarith_buffer_t aux;
  bvarith64_buffer_t aux64;
  pp_buffer_t pp;
  bvconstant_t bvconst;
} bvexp_table_t;

#define DEF_BVEXPTABLE_SIZE 100
#define MAX_BVEXPTABLE_SIZE (UINT32_MAX/sizeof(void *))



/*
 * OPERATIONS
 */

/*
 * Initialize table
 * - the table is initially empty (size = 0)
 * - the array def is allocated on the first addition
 * - vtbl = associated variable table
 */
extern void init_bvexp_table(bvexp_table_t *table, bv_vartable_t *vtbl);


/*
 * Delete table: free all memory
 */
extern void delete_bvexp_table(bvexp_table_t *table);


/*
 * Empty the table
 */
extern void reset_bvexp_table(bvexp_table_t *table);


/*
 * Remove all variables of index >= nv
 */
extern void bvexp_table_remove_vars(bvexp_table_t *table, uint32_t nv);


/*
 * Initialize buffers to be used with table
 */
static inline void bvexp_init_buffer(bvexp_table_t *table, bvarith_buffer_t *b) {
  init_bvarith_buffer(b, &table->pprods, &table->store);
}

static inline void bvexp_init_buffer64(bvexp_table_t *table, bvarith64_buffer_t *b) {
  init_bvarith64_buffer(b, &table->pprods, &table->store64);
}


/*
 * Check whether the polynomial p stored in buffer is present in table
 * - if so, return the variable index i such that def[i] = p
 *   otherwise, return -1
 * - buffer must be normalized and h must be the hash code of p
 * - buffer->store must be the same as table->store (or table->store64).
 * - two versions depending on the number of bits in p
 */
extern thvar_t bvexp_table_find(bvexp_table_t *table, bvarith_buffer_t *buffer, uint32_t h);
extern thvar_t bvexp_table_find64(bvexp_table_t *table, bvarith64_buffer_t *buffer, uint32_t h);


/*
 * Add the mapping def[v] = p to the table
 * - v must be not have a definition already
 * - p is the polynomial stored in buffer
 * - p must not be present in table (call find first)
 * - buffer must be normalized and h must be the hash code of p
 * Side effect: buffer is reset to the zero polynomial
 */
extern void bvexp_table_add(bvexp_table_t *table, thvar_t v, bvarith_buffer_t *buffer, uint32_t h);
extern void bvexp_table_add64(bvexp_table_t *table, thvar_t v, bvarith64_buffer_t *buffer, uint32_t h);


/*
 * Get the monomial list for variable x
 * - x must be positive (0 is reserved for const_idx)
 * - return NULL if def[x] is NULL or if x >= table->nvars
 */
static inline void *bvexp_get_def(bvexp_table_t *table, thvar_t x) {
  assert(0 < x);
  return (x < table->nvars) ? table->def[x] : NULL;
}

static inline bvmlist_t *bvexp_def(bvexp_table_t *table, thvar_t x) {
  assert(bvvar_bitsize(table->vtbl, x) > 64);
  return (bvmlist_t *) bvexp_get_def(table, x);
}

static inline bvmlist64_t *bvexp_def64(bvexp_table_t *table, thvar_t x) {
  assert(bvvar_bitsize(table->vtbl, x) <= 64);
  return (bvmlist64_t *) bvexp_get_def(table, x);
}



/*
 * EXPANDED FORMS
 */

/*
 * Expanded form of a bitvector polynomial p
 * - p is stored in a bvpoly_buffer object
 * - the expansion is returned in a bvarith_buffer or bvarith64_buffer object
 * - the result is normalized
 */
extern void expand_bvpoly64(bvexp_table_t *table, bvarith64_buffer_t *buffer, bvpoly_buffer_t *p);
extern void expand_bvpoly(bvexp_table_t *table, bvarith_buffer_t *buffer, bvpoly_buffer_t *p);


/*
 * Expanded form for a product c * p
 * - c is a normalized bitvector constant
 * - p is a power product stored in a pp_buffer object
 * - n = bitsize of p
 * - the expansion is returned in a bvarith_buffer or bvarith64_buffer object
 * - the result is normalized
 */
extern void expand_bvpprod64(bvexp_table_t *table, bvarith64_buffer_t *buffer, pp_buffer_t *p, uint32_t n, uint64_t c);
extern void expand_bvpprod(bvexp_table_t *table, bvarith_buffer_t *buffer, pp_buffer_t *p, uint32_t n, uint32_t *c);


#endif /* __BVEXP_TABLE_H */
