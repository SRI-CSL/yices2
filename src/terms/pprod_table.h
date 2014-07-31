/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Table for hash-consing of power products
 */

#ifndef __PPROD_TABLE_H
#define __PPROD_TABLE_H

#include <stdint.h>

#include "utils/bitvectors.h"
#include "utils/int_hash_tables.h"
#include "terms/power_products.h"


/*
 * For each i between 0 and nelems - 1, data[i] stores the
 * power product of index i.
 * - data[i] is valid if its tag bit is 0.
 *   Then data[i] is a pointer to a valid  pprod_t structure of degree >= 2.
 *   There's a corresponding record (with index i) in the htbl.
 * - data[i] is a deleted product if its tag bit is 1.
 *   In that case, data[i] encodes the next element in a global free list.
 * - mark[i] is used during garbage collection.
 *
 * Other components:
 * - size = size of array data and bitvector mark
 * - nelems = number of array elements used
 * - free_idx = start of the free list (-1 means that the free list is empty)
 * - htbl = hash table for hash consing
 * - buffer = buffer for constructing power products
 */
typedef struct pprod_table_s {
  pprod_t **data;
  byte_t *mark;

  uint32_t size;
  uint32_t nelems;
  int32_t free_idx;

  int_htbl_t htbl;
  pp_buffer_t buffer;
} pprod_table_t;


/*
 * Default and maximal sizes
 */
#define PPROD_TABLE_DEF_SIZE 64
#define PPROD_TABLE_MAX_SIZE (UINT32_MAX/sizeof(pprod_t *))


/*
 * Initialization: create an empty table.
 * - n = initial size. If n=0, the default is used.
 */
extern void init_pprod_table(pprod_table_t *table, uint32_t n);


/*
 * Delete the table and all the power products it contains.
 */
extern void delete_pprod_table(pprod_table_t *table);


/*
 * Empty the table
 */
extern void reset_pprod_table(pprod_table_t *table);


/*
 * Construct a power product from an array a of n pairs (variable, exponent).
 * - a must be normalized
 * - return null_pp if n is zero
 * - return a tagged variable if a contains a single pair (x, 1)
 * - if there's an element p equal to a already in the table, then return p,
 * - otherwise, create a new pprod_t structure equal to a and store it in
 *   the table.
 */
extern pprod_t *pprod_from_array(pprod_table_t *table, varexp_t *a, uint32_t n);


/*
 * Construct a power product from a buffer b
 * - b must be normalized.
 * - same behavior as above.
 */
static inline pprod_t *pprod_from_buffer(pprod_table_t *table, pp_buffer_t *b) {
  return pprod_from_array(table, b->prod, b->len);
}


/*
 * Construct the power product (p1 * p2)
 * - both p1 and p2 must be normalized and distinct from end_pp
 */
extern pprod_t *pprod_mul(pprod_table_t *table, pprod_t *p1, pprod_t *p2);


/*
 * Construct the power product p ^ d
 * - p must be normalized and distinct from end_pp
 */
extern pprod_t *pprod_exp(pprod_table_t *table, pprod_t *p, uint32_t d);


/*
 * Construct the power product x ^ d
 * - x = a variable index (between 0 and MAX_PPROD_VAR)
 */
extern pprod_t *pprod_varexp(pprod_table_t *table, int32_t x, uint32_t d);



/*
 * DELETION AND GARBAGE COLLECTION
 */

/*
 * Remove p from the table and free the corresponding pprod_t object.
 * - p must be present in the table (and must be distinct from end_pp,
 *   empty_pp, or any tagged variable).
 */
extern void delete_pprod(pprod_table_t *table, pprod_t *p);

/*
 * Mark p to prevent its deletion during garbage collection
 * - p must be present in the table
 */
extern void pprod_table_set_gc_mark(pprod_table_t *table, pprod_t *p);

/*
 * Call the garbage collector:
 * - delete every product not marked
 * - then clear all the marks
 */
extern void pprod_table_gc(pprod_table_t *table);


#endif /* __PPROD_TABLE_H */
