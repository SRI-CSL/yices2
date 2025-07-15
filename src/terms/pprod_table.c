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
 * Table for hash-consing of power products
 */

#include <assert.h>

#include "terms/pprod_table.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"


/*
 * Extend the table.
 */
static void extend_pprod_table(indexed_table_t *t) {
  pprod_table_t *pprods = (pprod_table_t *) t;
  pprods->mark = extend_bitvector(pprods->mark, t->size);
}


/*
 * Initialization: create an empty table.
 * - n = initial size. If n=0, the default is used.
 */
void init_pprod_table(pprod_table_t *table, uint32_t n) {
  if (n == 0) {
    n = PPROD_TABLE_DEF_SIZE;
  }

  static const indexed_table_vtbl_t vtbl = {
    .elem_size = sizeof(pprod_table_elem_t),
    .max_elems = PPROD_TABLE_MAX_SIZE,
    .extend = extend_pprod_table
  };
  
  indexed_table_init(&table->pprods, n, &vtbl);
  table->mark = allocate_bitvector(n);

  init_int_htbl(&table->htbl, 0); // default size
  init_pp_buffer(&table->buffer, 10);
}


static inline uint32_t pprod_table_nelems(pprod_table_t *t) {
  return indexed_table_nelems(&t->pprods);
}

static inline pprod_table_elem_t *pprod_table_elem(pprod_table_t *t,
						   uint32_t i) {
  return indexed_table_elem(pprod_table_elem_t, &t->pprods, i);
}

static void clear_pprod(indexed_table_elem_t *elem,
			index_t i,
			void *data) {
  ((pprod_table_elem_t *) elem)->pprod = NULL;
}


/*
 * Remove all products.
 */
static void free_pprods(pprod_table_t *table) {
  pprod_t *p;
  uint32_t i, n;

  indexed_table_for_each_free_elem(&table->pprods,
				   clear_pprod,
				   /*data=*/NULL);
  
  n = pprod_table_nelems(table);
  for (i=0; i<n; i++) {
    p = pprod_table_elem(table, i)->pprod;
    if (p)
      safe_free(p);
  }
}

/*
 * Empty the table
 */
void reset_pprod_table(pprod_table_t *table) {
  free_pprods(table);
  indexed_table_clear(&table->pprods);
  reset_int_htbl(&table->htbl);
  pp_buffer_reset(&table->buffer);
}


/*
 * Delete the table and its content
 */
void delete_pprod_table(pprod_table_t *table) {
  free_pprods(table);
  indexed_table_destroy(&table->pprods);
  delete_bitvector(table->mark);
  table->mark = NULL;

  delete_int_htbl(&table->htbl);
  delete_pp_buffer(&table->buffer);
}



/*
 * Allocate an index i containing PPROD.
 * - clear mark[i]
 */
static int32_t allocate_pprod_id(pprod_table_t *table,
				 pprod_t *pprod) {
  int32_t i;

  i = indexed_table_alloc(&table->pprods);
  pprod_table_elem(table, i)->pprod = pprod;

  clr_bit(table->mark, i);

  return i;
}



/*
 * Erase descriptor i:
 * - free prod[i] and add i to the free list
 */
static void erase_pprod_id(pprod_table_t *table, int32_t i) {
  assert(0 <= i && i < pprod_table_nelems(table));

  safe_free(pprod_table_elem(table, i)->pprod);
  indexed_table_free(&table->pprods, i);
}



/*
 * HASH CONSING
 */

/*
 * Object for hash consing from an array of pairs (variable, exponent).
 * - len = length of the array
 */
typedef struct pprod_hobj_s {
  int_hobj_t m;
  pprod_table_t *tbl;
  varexp_t *array;
  uint32_t len;
} pprod_hobj_t;


/*
 * Hash function
 */
static uint32_t hash_varexp_array(varexp_t *a, uint32_t n) {
  assert(n <= UINT32_MAX/2);
  return jenkins_hash_intarray((int32_t *) a, 2 * n);
}

static uint32_t hash_pprod(pprod_hobj_t *o) {
  return hash_varexp_array(o->array, o->len);
}

/*
 * Equality test
 */
static bool eq_pprod(pprod_hobj_t *o, int32_t i) {
  pprod_table_t *table;
  pprod_t *p;
  uint32_t n;

  table = o->tbl;
  assert(0 <= i && i < pprod_table_nelems(table));

  p = pprod_table_elem(table, i)->pprod;
  n = o->len;
  return (n == p->len) && varexp_array_equal(o->array, p->prod, n);
}


/*
 * Constructor
 */
static int32_t build_pprod(pprod_hobj_t *o) {
  pprod_table_t *table;
  int32_t i;

  table = o->tbl;
  i = allocate_pprod_id(table,
			make_pprod(o->array, o->len));

  return i;
}


/*
 * Hash consing function:
 * - a must be normalized, non empty, and not equal to (x^1)
 * - n = size of array a
 */
static pprod_t *get_pprod(pprod_table_t *table, varexp_t *a, uint32_t n) {
  int32_t i;
  pprod_hobj_t pprod_hobj;

  assert(n > 1 || (n == 1 && a[0].exp > 1));

  pprod_hobj.m.hash = (hobj_hash_t) hash_pprod;
  pprod_hobj.m.eq = (hobj_eq_t) eq_pprod;
  pprod_hobj.m.build = (hobj_build_t) build_pprod;
  pprod_hobj.tbl = table;
  pprod_hobj.array = a;
  pprod_hobj.len = n;

  i = int_htbl_get_obj(&table->htbl, &pprod_hobj.m);

  return pprod_table_elem(table, i)->pprod;
}



/*
 * Top-level constructor:
 * - check whether a is empty or equal to (x^1) if not use hash consing.
 * - a must be normalized
 */
pprod_t *pprod_from_array(pprod_table_t *table, varexp_t *a, uint32_t n) {
  if (n == 0) {
    return empty_pp;
  }
  if (n == 1 && a[0].exp == 1) {
    return var_pp(a[0].var);
  }

  return get_pprod(table, a, n);
}



/*
 * Product (p1 * p2)
 */
pprod_t *pprod_mul(pprod_table_t *table, pprod_t *p1, pprod_t *p2) {
  pp_buffer_t *b;

  b = &table->buffer;
  pp_buffer_set_pprod(b, p1);
  pp_buffer_mul_pprod(b, p2);

  return pprod_from_array(table, b->prod, b->len);
}


/*
 * Exponentiation: (p ^ d)
 */
pprod_t *pprod_exp(pprod_table_t *table, pprod_t *p, uint32_t d) {
  pp_buffer_t *b;

  b = &table->buffer;
  pp_buffer_set_pprod(b, p);
  pp_buffer_exponentiate(b, d);

  return pprod_from_array(table, b->prod, b->len);
}


/*
 * Variable power: (x ^ d)
 */
pprod_t *pprod_varexp(pprod_table_t *table, int32_t x, uint32_t d) {
  pp_buffer_t *b;

  b = &table->buffer;
  pp_buffer_set_varexp(b, x, d);
  pp_buffer_normalize(b);

  return pprod_from_array(table, b->prod, b->len);
}


/*
 * Find the index of p in table
 * - return -1 if p is not in the table
 */
static int32_t find_pprod_id(pprod_table_t *table, pprod_t *p) {
  pprod_hobj_t pprod_hobj;

  assert(p != empty_pp && p != end_pp && !pp_is_var(p));

  // search for p's index using the hash table
  pprod_hobj.m.hash = (hobj_hash_t) hash_pprod;
  pprod_hobj.m.eq = (hobj_eq_t) eq_pprod;
  pprod_hobj.m.build = (hobj_build_t) build_pprod;
  pprod_hobj.tbl = table;
  pprod_hobj.array = p->prod;
  pprod_hobj.len = p->len;

  return int_htbl_find_obj(&table->htbl, &pprod_hobj.m);
}

/*
 * Remove p from the table and free the corresponding pprod_t object.
 * - p must be present in the table (and must be distinct from end_pp,
 *   empty_pp, or any tagged variable).
 */
void delete_pprod(pprod_table_t *table, pprod_t *p) {
  int32_t i;
  uint32_t h;

  assert(p != empty_pp && p != end_pp && !pp_is_var(p));
  assert(p->len > 1 || (p->len == 1 && p->prod[0].exp > 1));

  /*
   * This is suboptimal but that should not matter too much.
   * We search for p's index i in the hash table then
   * we search the hash table again to delete the record (h, i).
   */
  i = find_pprod_id(table, p);
  assert(i >= 0 && pprod_table_elem(table, i)->pprod == p);

  // keep h = hash code of p
  h = hash_varexp_array(p->prod, p->len);

  // delete p and recycle index i
  erase_pprod_id(table, i);  // this deletes p

  // remove the record [h, i] from the hash table
  int_htbl_erase_record(&table->htbl, h, i);
}


/*
 * Set the garbage collection mark for p
 * - p must be present in the table (and must be distinct from end_pp,
 *   empty_pp, or any tagged variable).
 * - once p is marked it will not be deleted on the next call to pprod_table_gc
 */
void pprod_table_set_gc_mark(pprod_table_t *table, pprod_t *p) {
  int32_t i;

  i = find_pprod_id(table, p);
  assert(i >= 0 && pprod_table_elem(table, i)->pprod == p);
  set_bit(table->mark, i);
}

static void pprod_table_mark_free_elem(indexed_table_elem_t *t,
				       int32_t i,
				       void *data) {
  pprod_table_t *table = (pprod_table_t *) data;
  set_bit(table->mark, i);
}

/*
 * Garbage collection: delete all unmarked products
 * clear all the marks
 */
void pprod_table_gc(pprod_table_t *table) {
  pprod_t *p;
  uint32_t i, n, h;

  /* Mark all of the elements on the free list. */
  indexed_table_for_each_free_elem(&table->pprods,
				   pprod_table_mark_free_elem,
				   table);
  
  n = pprod_table_nelems(table);
  for (i=0; i<n; i++) {
    if (! tst_bit(table->mark, i)) {
      // i is not marked
      p = pprod_table_elem(table, i)->pprod;
      h = hash_varexp_array(p->prod, p->len);
      erase_pprod_id(table, i);
      int_htbl_erase_record(&table->htbl, h, i);
    }
  }

  // clear all the marks
  clear_bitvector(table->mark, table->pprods.size);
}
