/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * HASH TABLES OF NON-NEGATIVE INTEGERS
 *
 * These are intended for hash consing: terms are identified by an
 * index in a global term table. A hash-table stores records <k, v>
 * where v is the index of a term and k is the hash of that term.
 * There should never be duplicates (i.e., distinct records <k1, v1> and
 * <k2, v2> with v1 = v2).
 */


#ifndef __INT_HASH_TABLES_H
#define __INT_HASH_TABLES_H 1

#include <stdint.h>
#include <stdbool.h>


/*
 * Hash table = array of records
 * - each record is a pair <key, value> (key = hash code, value = index)
 * - an empty record has value = NULL_VALUE
 * - a deleted record has value = DELETED_VALUE
 * - other records have a non-negative value
 * Other fields:
 * - size = size of the record array
 * - nelems = number of elements actually stored
 * - ndeleted = number of deleted elements
 *
 * - resize_threshold: the table is resized when
 *    nelems + ndeleted > resize_threshold
 * - cleanup_threshold: deleted elements are removed when
 *    ndeleted > cleanup_threshold
 */
typedef struct int_hrec_s {
  uint32_t key;
  int32_t value;
} int_hrec_t;

enum {
  DELETED_VALUE = -2,
  NULL_VALUE = -1,
};

typedef struct int_htbl_s {
  int_hrec_t *records;
  uint32_t size;
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} int_htbl_t;

/*
 * Default initial size
 */
#define INT_HTBL_DEFAULT_SIZE 64

/*
 * Maximal size: we want to ensure no numerical overflow when
 * computing n * sizeof(int_hrec_t)
 */
#define MAX_HTBL_SIZE (UINT32_MAX/sizeof(int_hrec_t))


/*
 * Ratios: resize_threshold = size * RESIZE_RATIO
 *         cleanup_threshold = size * CLEANUP_RATIO
 */
#define RESIZE_RATIO 0.6
#define CLEANUP_RATIO 0.2


/*
 * To interface with the hash table, we use a semi object-oriented
 * approach, an object o must start by a int_hobj_t struct that
 * must provide three operations:
 *  o->hash(o) = hash code of o
 *  o->eq(o, i) = comparison between o and term i
 *  o->build(o) = store o in the term table and return its index
 *                (called if o is not already present in the table).
 *
 * Added 2007/08/31:
 *  o->build(o) can signal an error by returning a negative number
 *  if that happens, nothing is added to the hash table
 */
typedef uint32_t (*hobj_hash_t)(const void *);
typedef bool     (*hobj_eq_t)(const void *, int32_t);
typedef int32_t  (*hobj_build_t)(const void*);

typedef struct int_hobj_s {
  hobj_hash_t hash;
  hobj_eq_t eq;
  hobj_build_t build;
} int_hobj_t;


/*
 * Initialize: empty table of size n (n must be a power of 2)
 * If n = 0, the default initial size is used = 64.
 */
extern void init_int_htbl(int_htbl_t *table, uint32_t n);

/*
 * Delete: free the allocated memory
 */
extern void delete_int_htbl(int_htbl_t *table);

/*
 * Reset: empty the table
 */
extern void reset_int_htbl(int_htbl_t *table);

/*
 * Delete record <k, v>. No effect if <k, v> is not present in table.
 */
extern void int_htbl_erase_record(int_htbl_t *table, uint32_t k, int32_t v);

/*
 * Add record <k, v> to table. The record must not be present in table.
 */
extern void int_htbl_add_record(int_htbl_t *table, uint32_t k, int32_t v);

/*
 * Get index of object equal to o if present in the hash table,
 * return NULL_VALUE (-1) if no such object is present.
 */
extern int32_t int_htbl_find_obj(const int_htbl_t *table, const int_hobj_t *o);

/*
 * Get index of object equal to o if present, otherwise, build o and return
 * the new index.
 */
extern int32_t int_htbl_get_obj(int_htbl_t *table, const int_hobj_t *o);


#endif /* __INT_HASH_TABLES */
