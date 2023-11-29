/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2023 SRI International.
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

#ifndef __INDEXED_TABLE_H
#define __INDEXED_TABLE_H

#include <stddef.h>
#include <stdint.h>

/* An index into the table. */
typedef int32_t index_t;

/* An unsigned index into the table. */
typedef uint32_t uindex_t;

typedef struct indexed_table_s indexed_table_t;

typedef struct indexed_table_vtbl_s {
  /* The size of an individual element. */
  size_t elem_size;

  /* The maximum number of elements permitted in the table. */
  uindex_t max_elems;

  /* Called after extending the table. */
  void (*extend)(indexed_table_t *t);
} indexed_table_vtbl_t;

/* The type of elements on the free list. */
typedef struct indexed_table_elem_s {
  index_t next;
} indexed_table_elem_t;

/* The type of a function called on elements of the table. */
typedef void (*indexed_table_elem_fn)(indexed_table_elem_t *,
				      index_t,
				      void *);

/*
 * An index_table_t is an expandable array, with idices of type
 * index_t.
 */
struct indexed_table_s {
  /* The elements themselves. 

     Declared as "void *" to prevent accidental pointer arithmetic or
     array access. */
  void *elems;

  /* The number of elements allocated in the table. */
  uindex_t size;

  /* The number of elements that have (at some point) been
     used. Elements with this index (or greater) are unused. */
  uindex_t nelems;

  /* The number of active elements in the table. The sum of live_elems
     and the length of the free list is always equal to nelems. */
  uindex_t live_elems;

  /* If greater than or equal to zero, the head of the free list. The
     free list is composed of deleted entries. */
  index_t free_idx;

  /* Callbacks for derived classes. */
  const indexed_table_vtbl_t *vtbl;
};

/*
 * Initialize the table, making room for N elements.
 */
extern void indexed_table_init(indexed_table_t *t,
			       uindex_t n,
			       const indexed_table_vtbl_t *vtbl);

/*
 * Delete the table, freeing all associated storage.
 */
extern void indexed_table_destroy(indexed_table_t *t);

/*
 * Allocate a new entry in the table.
 */
extern index_t indexed_table_alloc(indexed_table_t *t);

/*
 * Free an entry in the table.
 */
extern void indexed_table_free(indexed_table_t *t, index_t i);

/*
 * Remove all entries from the table.
 */
extern void indexed_table_clear(indexed_table_t *t);

/*
 * The number of elements in the table.
 */
static inline uindex_t indexed_table_nelems(const indexed_table_t *t) {
  return t->nelems;
}

/*
 * The number of live entries.
 */
static inline uindex_t indexed_table_live_elems(const indexed_table_t *t) {
  return t->live_elems;
}

/*
 * Return the Ith element in TABLE. TYPE is the true type of the
 * elements in the table. The return value is a TYPE *.
 */
#define indexed_table_elem(type, table, i) \
  (&(((type *) (table)->elems)[i]))

/*
 * For each element X on the free list, call F(X, DATA). F is
 * permitted to muate the element.
 */
void indexed_table_for_each_free_elem(indexed_table_t *t,
				      indexed_table_elem_fn f,
				      void *data);

#endif /* !defined(__INDEXED_TABLE_H) */
