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
 * Table for hash-consing of sets of variables
 * Adapted from pprod_table
 */

#include <assert.h>

#include "mcsat/l2o/varset_table.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"


/*
 * Extend the table.
 */
static void extend_varset_table(indexed_table_t *t) {
  varset_table_t *varsets = (varset_table_t *) t;
  varsets->mark = extend_bitvector(varsets->mark, t->size);
}


/*
 * Initialization: create an empty table.
 * - n = initial size. If n=0, the default is used.
 */
void init_varset_table(varset_table_t *table, uint32_t n) {
  if (n == 0) {
    n = VARSET_TABLE_DEF_SIZE;
  }

  static const indexed_table_vtbl_t vtbl = {
    .elem_size = sizeof(varset_table_elem_t),
    .max_elems = VARSET_TABLE_MAX_SIZE,
    .extend = extend_varset_table
  };
  
  indexed_table_init(&table->varsets, n, &vtbl);
  table->mark = allocate_bitvector(n);

  init_int_htbl(&table->htbl, 0); // default size
}


static inline uint32_t varset_table_nelems(varset_table_t *t) {
  return indexed_table_nelems(&t->varsets);
}

static inline varset_table_elem_t *varset_table_elem(varset_table_t *t,
						   uint32_t i) {
  return indexed_table_elem(varset_table_elem_t, &t->varsets, i);
}

int_hset_t* get_varset(varset_table_t *table, uint32_t i){
  return varset_table_elem(table, i)->vars_set;
}

static void clear_varset(indexed_table_elem_t *elem,
			index_t i,
			void *data) {
  ((varset_table_elem_t *) elem)->vars_set = NULL;
}


/*
 * Remove all varsets.
 */
static void free_varset(varset_table_t *table) {
  int_hset_t *vars_set;
  uint32_t i, n;

  indexed_table_for_each_free_elem(&table->varsets,
				   clear_varset,
				   /*data=*/NULL);
  
  n = varset_table_nelems(table);
  for (i=0; i<n; i++) {
    vars_set = varset_table_elem(table, i)->vars_set;
    if (vars_set)
      safe_free(vars_set);
  }
}

/*
 * Empty the table
 */
void reset_varset_table(varset_table_t *table) {
  free_varset(table);
  indexed_table_clear(&table->varsets);
  reset_int_htbl(&table->htbl);
}


/*
 * Delete the table and its content
 */
void delete_varset_table(varset_table_t *table) {
  free_varset(table);
  indexed_table_destroy(&table->varsets);
  delete_bitvector(table->mark);
  table->mark = NULL;

  delete_int_htbl(&table->htbl);
}



/*
 * Allocate an index i containing a varset.
 * - clear mark[i]
 */
static int32_t allocate_varset_id(varset_table_t *table,
				 int_hset_t *vars_set) {
  int32_t i;

  i = indexed_table_alloc(&table->varsets);
  varset_table_elem(table, i)->vars_set = vars_set;

  clr_bit(table->mark, i);

  return i;
}



/*
 * Erase descriptor i
 */
static void erase_varset_id(varset_table_t *table, int32_t i) {
  assert(0 <= i && i < varset_table_nelems(table));

  safe_free(varset_table_elem(table, i)->vars_set);
  indexed_table_free(&table->varsets, i);
}



/*
 * HASH CONSING
 */

/*
 * Object for hash consing from a set of term_t
 */
typedef struct varset_hobj_s {
  int_hobj_t m;
  varset_table_t *tbl;
  int_hset_t *array;
  uint32_t nelems;
} varset_hobj_t;


/*
 * Hash function
 */
static uint32_t hash_varset_array(uint32_t *a, uint32_t n) {
  assert(n <= UINT32_MAX/2);
  //return jenkins_hash_intarray((int32_t *) a, 2 * n);
  //return jenkins_hash_intarray((int32_t *) a, n);
  return jenkins_hash_intarray((int32_t *) a, n);
}

static uint32_t hash_varset(varset_hobj_t *o) {
  return hash_varset_array(o->array->data, o->nelems);
}



/*
 * Comparison: two arrays of the same length n
 */
bool vars_set_array_equal(int_hset_t *a, int_hset_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a->data[i] != b->data[i]) {
      return false;
    }
  }
  return true;
}


/*
 * Equality test
 */
static bool eq_varset(varset_hobj_t *o, int32_t i) {
  varset_table_t *table;
  int_hset_t *vars_set;
  uint32_t n;

  table = o->tbl;
  assert(0 <= i && i < varset_table_nelems(table));

  vars_set = varset_table_elem(table, i)->vars_set;
  n = o->nelems;
  if((vars_set == NULL && o->array != NULL) || (vars_set != NULL && o->array == NULL)){
    return false;
  }
  return (n == vars_set->nelems) && vars_set_array_equal(o->array, vars_set, n);
}




/*
 * Empty vars set
 */
#define empty_vars_set ((int_hset_t *) NULL)

/*
 * End marker: all bits are one
 */
#define end_vars_set ((int_hset_t *) ~((uintptr_t) 0))


unsigned int v; // compute the next highest power of 2 of 32-bit v


uint32_t round_up_to_power_of_2(uint32_t v){
  v |= v >> 1;
  v |= v >> 2;
  v |= v >> 4;
  v |= v >> 8;
  v |= v >> 16;
  v++;
  return v;
}


/*
 * Build a var_set object by making a copy of a of length n
 */
int_hset_t *make_vars_set(int_hset_t *a, uint32_t n) {
  int_hset_t *vars_set;
  uint32_t i;

  assert(0 <= n);

  vars_set = (int_hset_t *) safe_malloc( sizeof(int_hset_t));
  uint32_t n_pow2 = round_up_to_power_of_2(n);
  init_int_hset(vars_set, n_pow2);
  for (i=0; i<n; i++) {
    int_hset_add(vars_set, a->data[i]);
  }
  int_hset_close_and_sort(vars_set);

  return vars_set;
}


/*
 * Constructor
 */
static int32_t build_varset(varset_hobj_t *o) {
  varset_table_t *table;
  int32_t i;

  table = o->tbl;
  i = allocate_varset_id(table,
			make_vars_set(o->array, o->nelems));

  //i = allocate_varset_id(table, o->array);

  return i;
}


/*
 * Hash consing function
 */
static int32_t get_allocate_varset(varset_table_t *table, int_hset_t *a) {
  int32_t i;
  varset_hobj_t varset_hobj;

  varset_hobj.m.hash = (hobj_hash_t) hash_varset;
  varset_hobj.m.eq = (hobj_eq_t) eq_varset;
  varset_hobj.m.build = (hobj_build_t) build_varset;
  varset_hobj.tbl = table;
  varset_hobj.array = a;
  varset_hobj.nelems = a->nelems;

  i = int_htbl_get_obj(&table->htbl, &varset_hobj.m);

  return i;
}



int32_t add_varset(varset_table_t *table, int_hset_t *a) {
  return get_allocate_varset(table, a);
}


/*
 * Find the index of vars_set in table
 * - return -1 if vars_set is not in the table
 */
int32_t find_varset_id(varset_table_t *table, int_hset_t *vars_set) {
  varset_hobj_t varset_hobj;

  assert(vars_set != empty_vars_set && vars_set != end_vars_set);

  // search for p's index using the hash table
  varset_hobj.m.hash = (hobj_hash_t) hash_varset;
  varset_hobj.m.eq = (hobj_eq_t) eq_varset;
  varset_hobj.m.build = (hobj_build_t) build_varset;
  varset_hobj.tbl = table;
  varset_hobj.array = vars_set;
  varset_hobj.nelems = vars_set->nelems;

  return int_htbl_find_obj(&table->htbl, &varset_hobj.m);
}

/*
 * Remove vars_set from the table and free the corresponding object.
 * - vars_set must be present in the table (and must be distinct from end_vars_set,
 *   empty_vars_set, or any tagged variable).
 */
void delete_varset(varset_table_t *table, int_hset_t *vars_set) {
  int32_t i;
  uint32_t h;

  assert(vars_set != empty_vars_set && vars_set != end_vars_set);


  /*
   * This is suboptimal but that should not matter too much.
   * We search for vars_set's index i in the hash table then
   * we search the hash table again to delete the record (h, i).
   */
  i = find_varset_id(table, vars_set);
  assert(i >= 0 && varset_table_elem(table, i)->vars_set == vars_set);

  // keep h = hash code of vars_set
  h = hash_varset_array(vars_set->data, vars_set->nelems);

  // delete vars_set and recycle index i
  erase_varset_id(table, i);  // this deletes p

  // remove the record [h, i] from the hash table
  int_htbl_erase_record(&table->htbl, h, i);
}


/*
 * Set the garbage collection mark for vars_set
 * - vars_set must be present in the table  (and must be distinct from end_vars_set,
 *   empty_vars_set, or any tagged variable).
 * - once vars_set is marked it will not be deleted on the next call to varset_table_gc
 */
void varset_table_set_gc_mark(varset_table_t *table, int_hset_t *vars_set) {
  int32_t i;

  i = find_varset_id(table, vars_set);
  assert(i >= 0 && varset_table_elem(table, i)->vars_set == vars_set);
  set_bit(table->mark, i);
}

static void varset_table_mark_free_elem(indexed_table_elem_t *t,
				       int32_t i,
				       void *data) {
  varset_table_t *table = (varset_table_t *) data;
  set_bit(table->mark, i);
}

/*
 * Garbage collection: delete all unmarked varsets
 * clear all the marks
 */
void varset_table_gc(varset_table_t *table) {
  int_hset_t *vars_set;
  uint32_t i, n, h;

  /* Mark all of the elements on the free list. */
  indexed_table_for_each_free_elem(&table->varsets,
				   varset_table_mark_free_elem,
				   table);
  
  n = varset_table_nelems(table);
  for (i=0; i<n; i++) {
    if (! tst_bit(table->mark, i)) {
      // i is not marked
      vars_set = varset_table_elem(table, i)->vars_set;
      h = hash_varset_array(vars_set->data, vars_set->nelems);
      erase_varset_id(table, i);
      int_htbl_erase_record(&table->htbl, h, i);
    }
  }

  // clear all the marks
  clear_bitvector(table->mark, table->varsets.nelems);
}
