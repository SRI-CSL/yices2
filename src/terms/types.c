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
 * Type table and hash consing
 */

#include <string.h>
#include <assert.h>

#include "terms/types.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"
#include "utils/refcount_strings.h"
#include "yices_limits.h"


/*
 * MACRO TABLE
 */

/*
 * Finalizer for names in the symbol table. This is called
 * whenever a record is removed from the symbol table.
 * All names must have a reference counter (cf. refcount_strings.h).
 */
static void macro_name_finalizer(stbl_rec_t *r) {
  string_decref(r->string);
}


/*
 * Allocate and initialize a macro descriptor:
 * - n = arity
 * - vars = array of n type variables
 * - body = type index
 */
static type_macro_t *new_descriptor(char *name, uint32_t n, const type_t *vars, type_t body) {
  type_macro_t *tmp;
  uint32_t i;

  assert(n <= TYPE_MACRO_MAX_ARITY);
  tmp = (type_macro_t *) safe_malloc(sizeof(type_macro_t) + n * sizeof(type_t));
  tmp->name = name; // We don't need to increment the ref counter here.
  tmp->arity = n;
  tmp->body = body;
  for (i=0; i<n; i++) {
    tmp->vars[i] = vars[i];
  }

  return tmp;
}


/*
 * Same thing for an uninterpreted type constructor
 * - n = arity
 */
static type_macro_t *new_constructor(char *name, uint32_t n) {
  type_macro_t *tmp;

  tmp  = (type_macro_t *) safe_malloc(sizeof(type_macro_t));
  tmp->name = name; // no ref count increment required
  tmp->arity = n;
  tmp->body = NULL_TYPE;

  return tmp;
}


/*
 * Delete a descriptor
 */
static inline void delete_descriptor(type_macro_t *d) {
  safe_free(d);
}


/*
 * Initialize the macro table
 * - n = initial size
 * - ttbl = type table
 * - if n is zero, nothing is allocated yet.
 *   an array data of default size will be allocated
 *   on the first addition.
 */
static void init_type_mtbl(type_mtbl_t *table, uint32_t n) {
  void **tmp;

  tmp = NULL;
  if (n > 0) {
    if (n > TYPE_MACRO_MAX_SIZE) {
      out_of_memory();
    }
    tmp = (void **) safe_malloc(n * sizeof(void*));
  }

  table->data = tmp;
  table->size = n;
  table->nelems = 0;
  table->free_idx = -1;

  init_stbl(&table->stbl, 0);
  init_tuple_hmap(&table->cache, 0);

  stbl_set_finalizer(&table->stbl, macro_name_finalizer);
}


/*
 * Delete the table and its content
 */
static void delete_type_mtbl(type_mtbl_t *table) {
  void *p;
  uint32_t i, n;

  n = table->nelems;
  for (i=0; i<n; i++) {
    p = table->data[i];
    if (! has_int_tag(p)) {
      delete_descriptor(p);
    }
  }

  safe_free(table->data);
  table->data = NULL;

  delete_stbl(&table->stbl);
  delete_tuple_hmap(&table->cache);
}


/*
 * Empty the table: delete all macros and macro instances
 */
static void reset_type_mtbl(type_mtbl_t *table) {
  void *p;
  uint32_t i, n;

  n = table->nelems;
  for (i=0; i<n; i++) {
    p = table->data[i];
    if (! has_int_tag(p)) {
      delete_descriptor(p);
    }
  }

  table->nelems = 0;
  table->free_idx = -1;

  reset_stbl(&table->stbl);
  reset_tuple_hmap(&table->cache);
}


/*
 * Make the table larger
 * - if this is the first allocation: allocate a data array of default size
 * - otherwise, make the data array 50% larger
 */
static void extend_type_mtbl(type_mtbl_t *table) {
  void **tmp;
  uint32_t n;

  n = table->size;
  if (n == 0) {
    n = TUPLE_HMAP_DEF_SIZE;
    assert(n <= TYPE_MACRO_MAX_SIZE);
    tmp = (void **) safe_malloc(n * sizeof(void*));
  } else {
    n ++;
    n += n>>1;
    if (n > TYPE_MACRO_MAX_SIZE) {
      out_of_memory();
    }
    tmp = (void **) safe_realloc(table->data, n * sizeof(void*));
  }

  table->data = tmp;
  table->size = n;
}


/*
 * Get a macro index
 */
static int32_t allocate_macro_id(type_mtbl_t *table) {
  int32_t i;

  i = table->free_idx;
  if (i >= 0) {
    assert(i < table->nelems);
    table->free_idx = untag_i32(table->data[i]);
  } else {
    i = table->nelems;
    table->nelems ++;
    if (i >= table->size) {
      extend_type_mtbl(table);
      assert(i < table->size);
    }
  }

  return i;
}


/*
 * Delete descriptor id and add it to the free list
 * - this must be the index of a live descriptor
 */
static void free_macro_id(type_mtbl_t *table, int32_t id) {
  assert(good_type_macro(table, id));
  delete_descriptor(table->data[id]);
  table->data[id] = tag_i32(table->free_idx);
  table->free_idx = id;
}




/*
 * TYPE TABLE
 */

/*
 * Finalizer for typenames in the symbol table. This function is
 * called when record r is deleted from the symbol table.
 * All symbols must be generated by the clone function, and have
 * a reference counter (cf. refcount_strings.h).
 */
static void typename_finalizer(stbl_rec_t *r) {
  string_decref(r->string);
}


/*
 * Initialize table, with initial size = n.
 */
static void type_table_init(type_table_t *table, uint32_t n) {
  // abort if the size is too large
  if (n > YICES_MAX_TYPES) {
    out_of_memory();
  }

  table->kind = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  table->desc = (type_desc_t *) safe_malloc(n * sizeof(type_desc_t));
  table->card = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  table->flags = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  table->name = (char **) safe_malloc(n * sizeof(char *));
  table->depth = (uint32_t *) safe_malloc(n * sizeof(uint32_t));

  table->size = n;
  table->nelems = 0;
  table->free_idx = NULL_TYPE;
  table->live_types = 0;

  init_int_htbl(&table->htbl, 0); // use default size
  init_stbl(&table->stbl, 0);     // default size too

  // install finalizer in the symbol table
  stbl_set_finalizer(&table->stbl, typename_finalizer);

  // don't allocate sup/inf/max tables
  table->sup_tbl = NULL;
  table->inf_tbl = NULL;
  table->max_tbl = NULL;

  // macro table: not allocated yet
  table->macro_tbl = NULL;
}


/*
 * Extend the table: make it 50% larger
 */
static void type_table_extend(type_table_t *table) {
  uint32_t n;

  /*
   * new size = 1.5 * (old_size + 1) approximately
   * this computation can't overflow since old_size < YICES_MAX_TYPE
   * this also ensures that new size > old size (even if old_size <= 1).
   */
  n = table->size + 1;
  n += n >> 1;
  if (n > YICES_MAX_TYPES) {
    out_of_memory();
  }

  table->kind = (uint8_t *) safe_realloc(table->kind, n * sizeof(uint8_t));
  table->desc = (type_desc_t *) safe_realloc(table->desc, n * sizeof(type_desc_t));
  table->card = (uint32_t *) safe_realloc(table->card, n * sizeof(uint32_t));
  table->flags = (uint8_t *) safe_realloc(table->flags, n * sizeof(uint8_t));
  table->name = (char **) safe_realloc(table->name, n * sizeof(char *));
  table->depth = (uint32_t *) safe_realloc(table->depth, n * sizeof(uint32_t));

  table->size = n;
}


/*
 * Get a free type id and initializes its name to NULL.
 * The other fields are not initialized.
 */
static type_t allocate_type_id(type_table_t *table) {
  type_t i;

  i = table->free_idx;
  if (i >= 0) {
    table->free_idx = table->desc[i].next;
  } else {
    i = table->nelems;
    table->nelems ++;
    if (i >= table->size) {
      type_table_extend(table);
    }
  }
  table->name[i] = NULL;
  table->live_types ++;

  return i;
}


/*
 * Erase type i: free its descriptor and add i to the free list
 */
static void erase_type(type_table_t *table, type_t i) {
  switch (table->kind[i]) {
  case UNUSED_TYPE: // already deleted
  case BOOL_TYPE:
  case INT_TYPE:
  case REAL_TYPE:
    return; // never delete predefined types

  case BITVECTOR_TYPE:
  case FF_TYPE: // TODO move down once ptr is in use
  case SCALAR_TYPE:
  case UNINTERPRETED_TYPE:
    break;

  case TUPLE_TYPE:
  case FUNCTION_TYPE:
  case INSTANCE_TYPE:
    safe_free(table->desc[i].ptr);
    break;
  }

  if (table->name[i] != NULL) {
    string_decref(table->name[i]);
    table->name[i] = NULL;
  }

  table->kind[i] = UNUSED_TYPE;
  table->desc[i].next = table->free_idx;
  table->free_idx = i;

  assert(table->live_types > 0);
  table->live_types --;
}




/*
 * INTERNAL CACHES
 */

/*
 * Get the sup_table: create and initialize it if needed
 */
static int_hmap2_t *get_sup_table(type_table_t *table) {
  int_hmap2_t *hmap;

  hmap = table->sup_tbl;
  if (hmap == NULL) {
    hmap = (int_hmap2_t *) safe_malloc(sizeof(int_hmap2_t));
    init_int_hmap2(hmap, 0); // default size
    table->sup_tbl = hmap;
  }

  return hmap;
}


/*
 * Get the inf_table: create and initialize it if needed
 */
static int_hmap2_t *get_inf_table(type_table_t *table) {
  int_hmap2_t *hmap;

  hmap = table->inf_tbl;
  if (hmap == NULL) {
    hmap = (int_hmap2_t *) safe_malloc(sizeof(int_hmap2_t));
    init_int_hmap2(hmap, 0); // default size
    table->inf_tbl = hmap;
  }

  return hmap;
}


/*
 * Get the max_table
 */
static int_hmap_t *get_max_table(type_table_t *table) {
  int_hmap_t *hmap;

  hmap = table->max_tbl;
  if (hmap == NULL) {
    hmap = (int_hmap_t *) safe_malloc(sizeof(int_hmap_t));
    init_int_hmap(hmap, 0);
    table->max_tbl = hmap;
  }

  return hmap;
}



/*
 * INTERNAL MACRO TABLE
 */
static type_mtbl_t *get_macro_table(type_table_t *table) {
  type_mtbl_t *tbl;

  tbl = table->macro_tbl;
  if (tbl == NULL) {
    tbl = (type_mtbl_t *) safe_malloc(sizeof(type_mtbl_t));
    init_type_mtbl(tbl, TYPE_MACRO_DEF_SIZE);
    table->macro_tbl = tbl;
  }

  return tbl;
}





/*
 * SUPPORT FOR CARD/FLAGS COMPUTATION
 */

/*
 * Build the conjunction of flags for types a[0 ... n-1]
 *
 * In the result we have
 * - finite flag = 1 if a[0] ... a[n-1] are all finite
 * - unit   flag = 1 if a[0] ... a[n-1] are all unit types
 * - exact  flag = 1 if a[0] ... a[n-1] are all small or unit types
 * - max    flag = 1 if a[0] ... a[n-1] are all maximal types
 * - min    flag = 1 if a[0] ... a[n-1] are all minimal types
 * - ground flag = 1 if a[0] ... a[n-1] are all ground types
 */
static uint32_t type_flags_conjunct(type_table_t *table, uint32_t n, const type_t *a) {
  uint32_t i, flg;

  flg = UNIT_TYPE_FLAGS;
  for (i=0; i<n; i++) {
    flg &= type_flags(table, a[i]);
  }

  return flg;
}


/*
 * Product of cardinalities of all types in a[0 ... n-1]
 * - return a value > UINT32_MAX if there's an overflow
 */
static uint64_t type_card_product(type_table_t *table, uint32_t n, const type_t *a) {
  uint64_t prod;
  uint32_t i;

  prod = 1;
  for (i=0; i<n; i++) {
    prod *= type_card(table, a[i]);
    if (prod > UINT32_MAX) break;
  }
  return prod;
}


/*
 * Compute the cardinality of function type e[0] ... e[n-1] --> r
 * - all types e[0] ... e[n-1] must be small or unit
 * - r must be small
 * - return a value > UINT32_MAX if there's an overflow
 */
static uint64_t fun_type_card(type_table_t *table, uint32_t n, const type_t *e, type_t r) {
  uint64_t power, dom;
  uint32_t range;

  dom = type_card_product(table, n, e);  // domain size
  if (dom >= 32) {
    // since the range has size 2 or more
    // power = range^dom does not fit in 32bits
    power = UINT32_MAX;
    power ++;
  } else {
    // compute power = range^dom
    // since dom is small we do this the easy way
    range = type_card(table, r);
    assert(2 <= range && dom >= 1);
    power = range;
    while (dom > 1) {
      power *= range;
      if (power > UINT32_MAX) break;
      dom --;
    }
  }

  return power;
}



/*
 * DEPTH COMPUTATION
 */

// for tuple
static uint32_t depth_tuple_type(type_table_t *table, uint32_t n, const type_t *e) {
  uint32_t i, max, d;

  max = 0;
  for (i=0; i<n; i++) {
    d = type_depth(table, e[i]);
    if (d > max) {
      max = d;
    }
  }
  return 1 + max;
}

// for function type
static uint32_t depth_function_type(type_table_t *table, uint32_t n, const type_t *e, type_t r) {
  uint32_t i, max, d;

  max = type_depth(table, r);
  for (i=0; i<n; i++) {
    d = type_depth(table, e[i]);
    if (d > max) {
      max = d;
    }
  }
  return 1 + max;
}

// for instance type: same as tuple
static inline uint32_t depth_instance_type(type_table_t *table, uint32_t n, const type_t *param) {
  return depth_tuple_type(table, n, param);
}


/*
 * TYPE CREATION
 */

/*
 * Add the three predefined types
 */
static void add_primitive_types(type_table_t *table) {
  type_t i;

  i = allocate_type_id(table);
  assert(i == bool_id);
  table->kind[i] = BOOL_TYPE;
  table->desc[i].ptr = NULL;
  table->card[i] = 2;
  table->flags[i] = SMALL_TYPE_FLAGS;
  table->depth[i] = 0;

  i = allocate_type_id(table);
  assert(i == int_id);
  table->kind[i] = INT_TYPE;
  table->desc[i].ptr = NULL;
  table->card[i] = UINT32_MAX;
  table->flags[i] = (INFINITE_TYPE_FLAGS | TYPE_IS_MINIMAL_MASK);
  table->depth[i] = 0;

  i = allocate_type_id(table);
  assert(i == real_id);
  table->kind[i] = REAL_TYPE;
  table->desc[i].ptr = NULL;
  table->card[i] = UINT32_MAX;
  table->flags[i] = (INFINITE_TYPE_FLAGS | TYPE_IS_MAXIMAL_MASK);
  table->depth[i] = 0;
}




/*
 * Add type (bitvector k) and return its id
 * - k must be positive and no more than YICES_MAX_BVSIZE
 */
static type_t new_bitvector_type(type_table_t *table, uint32_t k) {
  type_t i;

  assert(0 < k && k <= YICES_MAX_BVSIZE);

  i = allocate_type_id(table);
  table->kind[i] = BITVECTOR_TYPE;
  table->desc[i].integer = k;
  table->depth[i] = 0;
  if (k < 32) {
    table->card[i] = ((uint32_t) 1) << k;
    table->flags[i] = SMALL_TYPE_FLAGS;
  } else {
    table->card[i] = UINT32_MAX;
    table->flags[i] = LARGE_TYPE_FLAGS;
  }

  return i;
}

/*
 * Add type (FiniteField k) and return its id
 * - k must be positive
 * TODO make k arbitrary big by using rational_t
 */
static type_t new_finite_field_type(type_table_t *table, uint32_t k) {
  type_t i;

  assert(0 < k);

  i = allocate_type_id(table);
  table->kind[i] = FF_TYPE;
  table->desc[i].integer = k;
  table->depth[i] = 0;
  if (k < 32) {
    table->card[i] = ((uint32_t) 1) << k;
    table->flags[i] = SMALL_TYPE_FLAGS;
  } else {
    table->card[i] = UINT32_MAX;
    table->flags[i] = LARGE_TYPE_FLAGS;
  }

  return i;
}

/*
 * Add a scalar type and return its id
 * - k = number of elements in the type
 * - k must be positive.
 */
type_t new_scalar_type(type_table_t *table, uint32_t k) {
  type_t i;

  assert(k > 0);

  i = allocate_type_id(table);
  table->kind[i] = SCALAR_TYPE;
  table->desc[i].integer = k;
  table->card[i] = k;
  table->depth[i] = 0;
  if (k == 1) {
    table->flags[i] = UNIT_TYPE_FLAGS;
  } else {
    table->flags[i] = SMALL_TYPE_FLAGS;
  }

  return i;
}


/*
 * Add a new uninterpreted type and return its id
 * - the type is infinite and both minimal and maximal
 */
type_t new_uninterpreted_type(type_table_t *table) {
  type_t i;

  i = allocate_type_id(table);
  table->kind[i] = UNINTERPRETED_TYPE;
  table->desc[i].ptr = NULL;
  table->card[i] = UINT32_MAX;
  table->flags[i] = (INFINITE_TYPE_FLAGS | TYPE_IS_MAXIMAL_MASK | TYPE_IS_MINIMAL_MASK);
  table->depth[i] = 0;

  return i;
}


/*
 * Add tuple type: e[0], ..., e[n-1]
 */
static type_t new_tuple_type(type_table_t *table, uint32_t n, const type_t *e) {
  tuple_type_t *d;
  uint64_t card;
  type_t i;
  uint32_t j, flag;

  assert(0 < n && n <= YICES_MAX_ARITY);

  d = (tuple_type_t *) safe_malloc(sizeof(tuple_type_t) + n * sizeof(type_t));
  d->nelem = n;
  for (j=0; j<n; j++) d->elem[j] = e[j];

  i = allocate_type_id(table);
  table->kind[i] = TUPLE_TYPE;
  table->desc[i].ptr = d;

  /*
   * set flags and card
   * - type_flags_conjunct sets all the bits correctly
   *   except possibly the exact card bit
   */
  flag = type_flags_conjunct(table, n, e);
  switch (flag) {
  case UNIT_TYPE_FLAGS:
    // all components are unit types
    card = 1;
    break;

  case SMALL_TYPE_FLAGS:
    // all components are unit or small types
    card = type_card_product(table, n, e);
    if (card > UINT32_MAX) {
      // the product does not fit in 32bits
      // change exact card to inexact card
      card = UINT32_MAX;
      flag = LARGE_TYPE_FLAGS;
    }
    break;

  default:
    assert(flag == FREE_TYPE_FLAGS ||
           flag == LARGE_TYPE_FLAGS ||
           (flag & ~MINMAX_FLAGS_MASK) == INFINITE_TYPE_FLAGS);
    card = UINT32_MAX;
    break;
  }

  assert(0 < card && card <= UINT32_MAX);
  table->card[i] = card;
  table->flags[i] = flag;
  table->depth[i] = depth_tuple_type(table, n, e);

  return i;
}


/*
 * Add function type: (e[0], ..., e[n-1] --> r)
 */
static type_t new_function_type(type_table_t *table, uint32_t n, const type_t *e, type_t r) {
  function_type_t *d;
  uint64_t card;
  type_t i;
  uint32_t j, flag, rflag, minmax;

  assert(0 < n && n <= YICES_MAX_ARITY);

  d = (function_type_t *) safe_malloc(sizeof(function_type_t) + n * sizeof(type_t));
  d->range = r;
  d->ndom = n;
  for (j=0; j<n; j++) d->domain[j] = e[j];

  i = allocate_type_id(table);
  table->kind[i] = FUNCTION_TYPE;
  table->desc[i].ptr = d;

  /*
   * Three of the function type's flags are inherited from the range:
   * - fun type is unit iff range is unit (and the domains are ground)
   * - fun type is maximal iff range is maximal
   * - fun type is minimal iff range is minimal
   */
  rflag = type_flags(table, r);
  minmax = rflag & MINMAX_FLAGS_MASK; // save min and max bits
  flag = rflag & type_flags_conjunct(table, n, e);

  /*
   * The function type has the same flags as the range type if
   * flag != FREE_TYPE_FLAGS and the range type is unit
   */
  if (flag != FREE_TYPE_FLAGS && rflag == UNIT_TYPE_FLAGS) {
    flag = rflag;
  }


  switch (flag) {
  case FREE_TYPE_FLAGS:
    // the range or at least one domain is not ground
    card = UINT32_MAX;
    break;

  case UNIT_TYPE_FLAGS:
    // singleton range so the function type is also a singleton
    card = 1;
    break;

  case SMALL_TYPE_FLAGS:
    // the range is small finite
    // all domains are small finite or unit
    card = fun_type_card(table, n, e, r);
    if (card > UINT32_MAX) {
      card = UINT32_MAX;
      flag = LARGE_TYPE_FLAGS;
    }
    // minmax bits are inherited from the range
    flag = minmax | (flag & ~MINMAX_FLAGS_MASK);
    break;

  default:
    // the range or at least one domain is infinite
    // or the range and all domains are finite but at least one
    // of them is large.
    assert(flag == LARGE_TYPE_FLAGS ||
           (flag & ~MINMAX_FLAGS_MASK) == INFINITE_TYPE_FLAGS);
    card = UINT32_MAX;
    flag = minmax | (flag & ~MINMAX_FLAGS_MASK);
    break;
  }

  assert(0 < card && card <= UINT32_MAX);
  table->card[i] = card;
  table->flags[i] = flag;
  table->depth[i] = depth_function_type(table, n, e, r);

  return i;
}


/*
 * Add a new type variable of the given id
 */
static type_t new_type_variable(type_table_t *table, uint32_t id) {
  type_t i;

  i = allocate_type_id(table);
  table->kind[i] = VARIABLE_TYPE;
  table->desc[i].integer = id;
  table->card[i] = UINT32_MAX;         // card is not defined
  table->flags[i] = FREE_TYPE_FLAGS;
  table->depth[i] = 0;

  return i;
}


/*
 * Add a new instance of the given constructor cid
 * - n = arity
 * - param[0 ... n-1] = parameters
 *
 * If param[0] ... param[n-1] are all ground types, then the instance
 * is treated like a new uninterpreted type. Otherwise, we mark it
 * as a type with variables (flag = FREE_TYPE_FLAGS, card = UINT32_MAX).
 */
static type_t new_instance_type(type_table_t *table, int32_t cid, uint32_t n, const type_t *param) {
  instance_type_t *d;
  type_t i;
  uint32_t j, flag;

  assert(0 < n && n <= YICES_MAX_ARITY);
  assert(table->macro_tbl != NULL && type_macro_arity(table->macro_tbl, cid) == n);

  d = (instance_type_t *) safe_malloc(sizeof(instance_type_t) + n * sizeof(type_t));
  d->cid = cid;
  d->arity = n;
  for (j=0; j<n; j++) {
    d->param[j] = param[j];
  }

  i = allocate_type_id(table);
  table->kind[i] = INSTANCE_TYPE;
  table->desc[i].ptr = d;
  table->card[i] = UINT32_MAX;

  flag = type_flags_conjunct(table, n, param);
  assert((flag & TYPE_IS_GROUND_MASK) || flag == FREE_TYPE_FLAGS);
  if (flag & TYPE_IS_GROUND_MASK) {
    // set flags as for uninterpreted types
    flag = (INFINITE_TYPE_FLAGS | TYPE_IS_MAXIMAL_MASK | TYPE_IS_MINIMAL_MASK);
  }
  table->flags[i] = flag;
  table->depth[i] = depth_instance_type(table, n, param);

  return i;
}



/*
 * HASH CONSING
 */

/*
 * Objects for hash-consing
 */
typedef struct bv_type_hobj_s {
  int_hobj_t m;      // methods
  type_table_t *tbl;
  uint32_t size;
} bv_type_hobj_t;

typedef struct ff_type_hobj_s {
  int_hobj_t m;      // methods
  type_table_t *tbl;
  uint32_t size; // TODO change this for bigger int
} ff_type_hobj_t;

typedef struct tuple_type_hobj_s {
  int_hobj_t m;
  type_table_t *tbl;
  uint32_t n;
  const type_t *elem;
} tuple_type_hobj_t;

typedef struct function_type_hobj_s {
  int_hobj_t m;
  type_table_t *tbl;
  type_t range;
  uint32_t n;
  const type_t *dom;
} function_type_hobj_t;

typedef struct type_var_hobj_s {
  int_hobj_t m;
  type_table_t *tbl;
  uint32_t id;
} type_var_hobj_t;

typedef struct instance_type_hobj_s {
  int_hobj_t m;
  type_table_t *tbl;
  int32_t cid;
  uint32_t arity;
  const type_t *param;
} instance_type_hobj_t;


/*
 * Hash functions
 */
static uint32_t hash_bv_type(bv_type_hobj_t *p) {
  return jenkins_hash_pair(p->size, 0, 0x7838abe2);
}

static uint32_t hash_ff_type(bv_type_hobj_t *p) {
  return jenkins_hash_pair(p->size, 0, 0x78210bea);
}

static uint32_t hash_tuple_type(tuple_type_hobj_t *p) {
  return jenkins_hash_intarray2(p->elem, p->n, 0x8193ea92);
}

static uint32_t hash_function_type(function_type_hobj_t *p) {
  uint32_t h;

  h = jenkins_hash_intarray2(p->dom, p->n, 0x5ad7b72f);
  return jenkins_hash_pair(p->range, 0, h);
}

static uint32_t hash_type_var(type_var_hobj_t *p) {
  return jenkins_hash_pair(p->id, 0, 0x823a33ad);
}

static uint32_t hash_instance_type(instance_type_hobj_t *p) {
  uint32_t h;

  h = jenkins_hash_intarray2(p->param, p->arity, 0xabe3d76F);
  return jenkins_hash_pair(p->cid, 0, h);
}


/*
 * Hash functions used during garbage collection.
 * Make sure they are consistent with the ones above.
 */
static uint32_t hash_bvtype(int32_t size) {
  return jenkins_hash_pair(size, 0, 0x7838abe2);
}

static uint32_t hash_fftype(int32_t size) {
  return jenkins_hash_pair(size, 0, 0x78210bea);
}

static uint32_t hash_tupletype(tuple_type_t *p) {
  return jenkins_hash_intarray2(p->elem, p->nelem, 0x8193ea92);
}

static uint32_t hash_funtype(function_type_t *p) {
  uint32_t h;

  h = jenkins_hash_intarray2(p->domain, p->ndom, 0x5ad7b72f);
  return jenkins_hash_pair(p->range, 0, h);
}

static uint32_t hash_typevar(uint32_t id) {
  return jenkins_hash_pair(id, 0, 0x823a33ad);
}

static uint32_t hash_instancetype(instance_type_t *p) {
  uint32_t h;

  h = jenkins_hash_intarray2(p->param, p->arity, 0xabe3d76F);
  return jenkins_hash_pair(p->cid, 0, h);
}


/*
 * Comparison functions for hash consing
 */
static bool eq_bv_type(bv_type_hobj_t *p, type_t i) {
  type_table_t *table;

  table = p->tbl;
  return table->kind[i] == BITVECTOR_TYPE && table->desc[i].integer == p->size;
}

static bool eq_ff_type(bv_type_hobj_t *p, type_t i) {
  type_table_t *table;

  table = p->tbl;
  return table->kind[i] == FF_TYPE && table->desc[i].integer == p->size; // TODO change this for big int
}

static bool eq_tuple_type(tuple_type_hobj_t *p, type_t i) {
  type_table_t *table;
  tuple_type_t *d;
  int32_t j;

  table = p->tbl;
  if (table->kind[i] != TUPLE_TYPE) return false;

  d = (tuple_type_t *) table->desc[i].ptr;
  if (d->nelem != p->n) return false;

  for (j=0; j<p->n; j++) {
    if (d->elem[j] != p->elem[j]) return false;
  }

  return true;
}

static bool eq_function_type(function_type_hobj_t *p, type_t i) {
  type_table_t *table;
  function_type_t *d;
  int32_t j;

  table = p->tbl;
  if (table->kind[i] != FUNCTION_TYPE) return false;

  d = (function_type_t *) table->desc[i].ptr;
  if (d->range != p->range || d->ndom != p->n) return false;

  for (j=0; j<p->n; j++) {
    if (d->domain[j] != p->dom[j]) return false;
  }

  return true;
}

static bool eq_type_var(type_var_hobj_t *p, type_t i) {
  type_table_t *table;

  table = p->tbl;
  return table->kind[i] == VARIABLE_TYPE && table->desc[i].integer == p->id;
}

static bool eq_instance_type(instance_type_hobj_t *p, type_t i) {
  type_table_t *table;
  instance_type_t *d;
  uint32_t j;

  table = p->tbl;
  if (table->kind[i] != INSTANCE_TYPE) return false;

  d = (instance_type_t *) table->desc[i].ptr;
  if (d->cid != p->cid || d->arity != p->arity) return false;

  for (j=0; j<p->arity; j++) {
    if (d->param[j] != p->param[j]) return false;
  }

  return true;
}


/*
 * Builder functions
 */
static type_t build_bv_type(bv_type_hobj_t *p) {
  return new_bitvector_type(p->tbl, p->size);
}

static type_t build_ff_type(ff_type_hobj_t *p) {
  return new_finite_field_type(p->tbl, p->size);
}

static type_t build_tuple_type(tuple_type_hobj_t *p) {
  return new_tuple_type(p->tbl, p->n, p->elem);
}

static type_t build_function_type(function_type_hobj_t *p) {
  return new_function_type(p->tbl, p->n, p->dom, p->range);
}

static type_t build_type_var(type_var_hobj_t *p) {
  return new_type_variable(p->tbl, p->id);;
}

static type_t build_instance_type(instance_type_hobj_t *p) {
  return new_instance_type(p->tbl, p->cid, p->arity, p->param);
}


/*
 * TABLE MANAGEMENT + EXPORTED TYPE CONSTRUCTORS
 *
 * NOTE: The constructors for uninterpreted and scalar types
 * are defined above. They don't use hash consing.
 */

/*
 * Initialize table: add the predefined types
 */
void init_type_table(type_table_t *table, uint32_t n) {
  type_table_init(table, n);
  add_primitive_types(table);
}

/*
 * Delete table: free all allocated memory
 */
void delete_type_table(type_table_t *table) {
  uint32_t i;

  // decrement refcount for all names
  for (i=0; i<table->nelems; i++) {
    if (table->name[i] != NULL) {
      string_decref(table->name[i]);
    }
  }

  // delete all allocated descriptors
  for (i=0; i<table->nelems; i++) {
    switch (table->kind[i]) {
    case TUPLE_TYPE:
    case FUNCTION_TYPE:
    case INSTANCE_TYPE:
      safe_free(table->desc[i].ptr);
      break;

    default:
      break;
    }
  }

  safe_free(table->kind);
  safe_free(table->desc);
  safe_free(table->card);
  safe_free(table->flags);
  safe_free(table->name);
  safe_free(table->depth);

  table->kind = NULL;
  table->desc = NULL;
  table->card = NULL;
  table->flags = NULL;
  table->name = NULL;
  table->depth = NULL;

  delete_int_htbl(&table->htbl);
  delete_stbl(&table->stbl);

  if (table->sup_tbl != NULL) {
    delete_int_hmap2(table->sup_tbl);
    safe_free(table->sup_tbl);
    table->sup_tbl = NULL;
  }

  if (table->inf_tbl != NULL) {
    delete_int_hmap2(table->inf_tbl);
    safe_free(table->inf_tbl);
    table->inf_tbl = NULL;
  }

  if (table->max_tbl != NULL) {
    delete_int_hmap(table->max_tbl);
    safe_free(table->max_tbl);
    table->max_tbl = NULL;
  }

  if (table->macro_tbl != NULL) {
    delete_type_mtbl(table->macro_tbl);
    safe_free(table->macro_tbl);
    table->macro_tbl = NULL;
  }
}


/*
 * Full reset: delete everything except the primitive types
 */
void reset_type_table(type_table_t *table) {
  uint32_t i;

  // decrement ref counts
  for (i=0; i<table->nelems; i++) {
    if (table->name[i] != NULL) {
      string_decref(table->name[i]);
    }
  }

  // delete descriptors
  for (i=0; i<table->nelems; i++) {
    switch (table->kind[i]) {
    case TUPLE_TYPE:
    case FUNCTION_TYPE:
    case INSTANCE_TYPE:
      safe_free(table->desc[i].ptr);
      break;

    default:
      break;
    }
  }

  reset_int_htbl(&table->htbl);
  reset_stbl(&table->stbl);

  if (table->sup_tbl != NULL) {
    reset_int_hmap2(table->sup_tbl);
  }
  if (table->inf_tbl != NULL) {
    reset_int_hmap2(table->inf_tbl);
  }
  if (table->max_tbl != NULL) {
    int_hmap_reset(table->max_tbl);
  }
  if (table->macro_tbl != NULL) {
    reset_type_mtbl(table->macro_tbl);
  }

  table->nelems = 0;
  table->free_idx = NULL_TYPE;
  table->live_types = 0;
  add_primitive_types(table);
}


/*
 * Bitvector type
 */
type_t bv_type(type_table_t *table, uint32_t size) {
  bv_type_hobj_t bv_hobj;
  
  assert(size > 0);

  bv_hobj.m.hash = (hobj_hash_t) hash_bv_type;
  bv_hobj.m.eq = (hobj_eq_t) eq_bv_type;
  bv_hobj.m.build = (hobj_build_t) build_bv_type;
  bv_hobj.tbl = table;
  bv_hobj.size = size;
  return int_htbl_get_obj(&table->htbl, &bv_hobj.m);
}

/*
 * FiniteField type
 */
type_t ff_type(type_table_t *table, uint32_t size) {
  ff_type_hobj_t ff_hobj;

  assert(size > 0);

  ff_hobj.m.hash = (hobj_hash_t) hash_ff_type;
  ff_hobj.m.eq = (hobj_eq_t) eq_ff_type;
  ff_hobj.m.build = (hobj_build_t) build_ff_type;
  ff_hobj.tbl = table;
  ff_hobj.size = size;
  return int_htbl_get_obj(&table->htbl, &ff_hobj.m);
}

/*
 * Tuple type
 */
type_t tuple_type(type_table_t *table, uint32_t n, const type_t elem[]) {
  tuple_type_hobj_t tuple_hobj;
  
  assert(0 < n && n <= YICES_MAX_ARITY);

  tuple_hobj.m.hash = (hobj_hash_t) hash_tuple_type;
  tuple_hobj.m.eq = (hobj_eq_t) eq_tuple_type;
  tuple_hobj.m.build = (hobj_build_t) build_tuple_type;
  tuple_hobj.tbl = table;
  tuple_hobj.n = n;
  tuple_hobj.elem = elem;
  return int_htbl_get_obj(&table->htbl, &tuple_hobj.m);
}

/*
 * Function type
 */
type_t function_type(type_table_t *table, type_t range, uint32_t n, const type_t dom[]) {
  function_type_hobj_t function_hobj;
  
  assert(0 < n && n <= YICES_MAX_ARITY);

  function_hobj.m.hash = (hobj_hash_t) hash_function_type;
  function_hobj.m.eq = (hobj_eq_t) eq_function_type;
  function_hobj.m.build = (hobj_build_t) build_function_type;
  function_hobj.tbl = table;
  function_hobj.range = range;
  function_hobj.n = n;
  function_hobj.dom = dom;
  return int_htbl_get_obj(&table->htbl, &function_hobj.m);
}


/*
 * Type variable
 */
type_t type_variable(type_table_t *table, uint32_t id) {
  type_var_hobj_t var_hobj;

  var_hobj.m.hash = (hobj_hash_t) hash_type_var;
  var_hobj.m.eq = (hobj_eq_t) eq_type_var;
  var_hobj.m.build = (hobj_build_t) build_type_var;
  var_hobj.tbl = table;
  var_hobj.id = id;
  return int_htbl_get_obj(&table->htbl, &var_hobj.m);
}


/*
 * Type instance
 */
type_t instance_type(type_table_t *table, int32_t cid, uint32_t n, const type_t tau[]) {
  instance_type_hobj_t instance_hobj;
  
  assert(0 < n && n <= YICES_MAX_ARITY);

  instance_hobj.m.hash = (hobj_hash_t) hash_instance_type;
  instance_hobj.m.eq = (hobj_eq_t) eq_instance_type;
  instance_hobj.m.build = (hobj_build_t) build_instance_type;
  instance_hobj.tbl = table;
  instance_hobj.cid = cid;
  instance_hobj.arity = n;
  instance_hobj.param = tau;
  return int_htbl_get_obj(&table->htbl, &instance_hobj.m);
}


/*
 * SUBSTITUTION
 */

#ifndef NDEBUG
/*
 * Check that the elements of v are distinct variables
 */
static bool all_distinct_vars(type_table_t *table, uint32_t n, const type_t v[]) {
  uint32_t i, j;

  for (i=0; i<n; i++) {
    if (! is_type_variable(table, v[i])) {
      return false;
    }
  }

  for (i=0; i<n; i++) {
    for (j=i+1; j<n; j++) {
      if (v[i] == v[j]) {
        return false;
      }
    }
  }

  return true;
}

#endif


/*
 * Apply substitution to tau:
 * - hmap defines the substitution and stores substitution of already visited types
 */
static type_t type_subst_recur(type_table_t *table, int_hmap_t *hmap, type_t tau);

/*
 * Build the tuple type (tuple (subst tau[0]) ... (subst tau[n-1]))
 */
static type_t tuple_type_subst(type_table_t *table, int_hmap_t *hmap, const type_t *tau, uint32_t n) {
  type_t buffer[8];
  type_t *s;
  type_t result;
  uint32_t i;

  s = buffer;
  if (n > 8) {
    s = (type_t *) safe_malloc(n * sizeof(type_t));
  }

  for (i=0; i<n; i++) {
    s[i] = type_subst_recur(table, hmap, tau[i]);
  }
  result = tuple_type(table, n, s);

  if (n > 8) {
    safe_free(s);
  }

  return result;
}

/*
 * Build the function type (-> (subst tau[0]) ... (subst tau[n-1]) (subst sigma))
 */
static type_t function_type_subst(type_table_t *table, int_hmap_t *hmap, type_t sigma, const type_t *tau, uint32_t n) {
  type_t buffer[8];
  type_t *s;
  type_t result;
  uint32_t i;

  s = buffer;
  if (n > 8) {
    s = (type_t *) safe_malloc(n * sizeof(type_t));
  }

  for (i=0; i<n; i++) {
    s[i] = type_subst_recur(table, hmap, tau[i]);
  }
  sigma = type_subst_recur(table, hmap, sigma);
  result = function_type(table, sigma, n, s);

  if (n > 8) {
    safe_free(s);
  }

  return result;
}


/*
 * Build the instance (cid (subst tau[0]) ... (sust tau[n-1]))
 */
static type_t instance_type_subst(type_table_t *table, int_hmap_t *hmap, int32_t cid, type_t *tau, uint32_t n) {
  type_t buffer[8];
  type_t *s;
  type_t result;
  uint32_t i;

  s = buffer;
  if (n > 8) {
    s = (type_t *) safe_malloc(n * sizeof(type_t));
  }

  for (i=0; i<n; i++) {
    s[i] = type_subst_recur(table, hmap, tau[i]);
  }

  result = instance_type(table, cid, n, s);

  if (n > 8) {
    safe_free(s);
  }

  return result;
}


static type_t type_subst_recur(type_table_t *table, int_hmap_t *hmap, type_t tau) {
  int_hmap_pair_t *p;
  tuple_type_t *tup;
  function_type_t *fun;
  instance_type_t *inst;
  type_t result;

  // if tau is ground, then it's unchanged
  result = tau;
  if (! ground_type(table, tau)) {
    p = int_hmap_find(hmap, tau);
    if (p != NULL) {
      result = p->val;
    } else {
      switch (type_kind(table, tau)) {
      case TUPLE_TYPE:
        tup = tuple_type_desc(table, tau);
        result = tuple_type_subst(table, hmap, tup->elem, tup->nelem);
        p = int_hmap_get(hmap, tau);
        assert(p->val < 0);
        p->val = result;
        break;

      case FUNCTION_TYPE:
        fun = function_type_desc(table, tau);
        result = function_type_subst(table, hmap, fun->range, fun->domain, fun->ndom);
        p = int_hmap_get(hmap, tau);
        assert(p->val < 0);
        p->val = result;
        break;

      case INSTANCE_TYPE:
        inst = instance_type_desc(table, tau);
        result = instance_type_subst(table, hmap, inst->cid, inst->param, inst->arity);
        p = int_hmap_get(hmap, tau);
        assert(p->val < 0);
        p->val = result;
        break;

      default:
        assert(is_type_variable(table, tau));
        result = tau;
        break;
      }

    }
  }

  return result;
}


/*
 * Apply a type substitution:
 *   v[0 ... n-1] = distinct type variables
 *   s[0 ... n-1] = types
 * the function replaces v[i] by s[i] in tau and returns
 * the result.
 */
type_t type_substitution(type_table_t *table, type_t tau, uint32_t n, const type_t v[], const type_t s[]) {
  int_hmap_t hmap;
  int_hmap_pair_t *p;
  uint32_t i;
  type_t result;

  assert(all_distinct_vars(table, n, v));

  result = tau;
  if (! ground_type(table, tau)) {
    init_int_hmap(&hmap, 0);
    for (i=0; i<n; i++) {
      p = int_hmap_get(&hmap, v[i]);
      assert(p->key == v[i] && p->val < 0);
      p->val = s[i];
    }
    result = type_subst_recur(table, &hmap, tau);
    delete_int_hmap(&hmap);
  }

  return result;
}



/*
 * MATCHING
 */

/*
 * Initialize matcher
 */
void init_type_matcher(type_matcher_t *matcher, type_table_t *types) {
  uint32_t n;

  matcher->types = types;
  init_int_hmap(&matcher->tc, 0); // used default size

  n = DEF_TYPE_MATCHER_SIZE;
  assert(n <= MAX_TYPE_MATCHER_SIZE);
  matcher->var = (type_t *) safe_malloc(n * sizeof(type_t));
  matcher->map = (type_t *) safe_malloc(n * sizeof(type_t));
  matcher->nvars = 0;
  matcher->varsize = n;
}


/*
 * Make room for more variables
 */
static void type_matcher_extend(type_matcher_t *matcher) {
  uint32_t n;

  n = matcher->varsize;
  n += (n >> 1); // 50% larger
  n ++;
  if (n > MAX_TYPE_MATCHER_SIZE) {
    out_of_memory();
  }

  matcher->var = (type_t *) safe_realloc(matcher->var, n * sizeof(type_t));
  matcher->map = (type_t *) safe_realloc(matcher->map, n * sizeof(type_t));
  matcher->varsize = n;
}


/*
 * Add a type variable x to matcher->var
 * - x is mapped to NULL_TYPE
 */
static void type_matcher_addvar(type_matcher_t *matcher, type_t x) {
  uint32_t i;

  assert(is_type_variable(matcher->types, x));
  i = matcher->nvars;
  if (i == matcher->varsize) {
    type_matcher_extend(matcher);
  }
  assert(i < matcher->varsize);
  matcher->var[i] = x;
  matcher->map[i] = NULL_TYPE;
  matcher->nvars = i + 1;
}


/*
 * Reset to the empty set
 */
void reset_type_matcher(type_matcher_t *matcher) {
  int_hmap_reset(&matcher->tc);
  matcher->nvars = 0;
}


/*
 * Delete all
 */
void delete_type_matcher(type_matcher_t *matcher) {
  delete_int_hmap(&matcher->tc);
  safe_free(matcher->var);
  safe_free(matcher->map);
}



/*
 * Constraint code for (sigma, eq):
 * - low-order bit = 1 --> equality constraint
 * - low-order bit = 0 --> type inclusion constraint
 * - rest of the 32bit integer is sigma
 */
static inline int32_t mk_constraint_code(type_t sigma, bool eq) {
  int32_t k;

  assert(0 <= sigma);
  k = (sigma << 1) | eq;
  assert(k >= 0);

  return k;
}


/*
 * Check the type of constraint encoded by k
 */
static inline bool is_eq_constraint(int32_t k) {
  assert(k >= 0);
  return (k & 1) != 0;
}

#ifndef NDEBUG
static inline bool is_subtype_constraint(int32_t k) {
  assert(k >= 0);
  return (k & 1) == 0;
}
#endif

static inline type_t arg_of_constraint(int32_t k) {
  assert(k >= 0);
  return k >> 1;
}



/*
 * Check whether constraint codes k1 and k2 are compatible
 * - at least one of k1 and k2 must be non-negative
 * - if so return the code for the conjunction of k1 and k2
 * - otherwise return -1
 */
static int32_t merge_constraints(type_matcher_t *matcher, int32_t k1, int32_t k2) {
  type_t sigma1, sigma2, sigma;

  assert(k1 >= 0 || k2 >= 0);

  if (k1 < 0) return k2;
  if (k2 < 0) return k1;
  if (k1 == k2) return k1;

  sigma1 = arg_of_constraint(k1);
  sigma2 = arg_of_constraint(k2);

  if (is_eq_constraint(k1) && is_eq_constraint(k2)) {
    // k1 says [tau == sigma1]
    // k2 says [tau == sigma2]
    assert(sigma1 != sigma2);
    return -1;
  }

  if (is_eq_constraint(k1)) {
    assert(is_subtype_constraint(k2));
    // k1 says [tau == sigma1]
    // k2 says [tau is a supertype of sigma2]
    if (is_subtype(matcher->types, sigma2, sigma1)) {
      return k1;
    }
    return -1;
  }

  if (is_eq_constraint(k2)) {
    assert(is_subtype_constraint(k1));
    // k1 says [tau is a supertype of sigma1]
    // k2 says [tau == sigma2]
    if (is_subtype(matcher->types, sigma1, sigma2)) {
      return k2;
    }
    return -1;
  }

  assert(is_subtype_constraint(k1) && is_subtype_constraint(k2));
  // k1 says [tau is a supertype of sigma1]
  // k2 says [tau is a supertype of sigma2]
  sigma = super_type(matcher->types, sigma1, sigma2);
  if (sigma != NULL_TYPE) {
    return mk_constraint_code(sigma, false); // [tau is a supertype of sigma]
  }

  return -1;
}


/*
 * Get the constraint code for tau
 * -1 means no constraint on tau yet
 */
static int32_t type_matcher_get_constraint(type_matcher_t *matcher, type_t tau) {
  int_hmap_pair_t *p;
  int32_t k;

  k = -1;
  p = int_hmap_find(&matcher->tc, tau);
  if (p != NULL) {
    k = p->val;
  }
  return k;
}


/*
 * Set the constraint code for tau to k
 *  k must be a valid constraint code(not -1)
 */
static void type_matcher_set_constraint(type_matcher_t *matcher, type_t tau, int32_t k) {
  int_hmap_pair_t *p;

  assert(k >= 0 && good_type(matcher->types, arg_of_constraint(k)));

  p = int_hmap_get(&matcher->tc, tau);
  assert(p->key == tau);
  p->val = k;
}




/*
 * Add a set of constraints:
 * - a and b must be array of types of the same size
 * - n = size of these arrays
 * - eq = constraint type
 *
 * Each a[i] should be a type to be matched with b[i]
 * - if eq is true, we want exact matching
 * - if eq is false, we want b[i] \subtype of a[i]
 *
 * - return false if the matching fails, true otherwise
 */
static bool match_type_arrays(type_matcher_t *matcher, type_t *a, type_t *b, uint32_t n, bool eq) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (!type_matcher_add_constraint(matcher, a[i], b[i], eq)) {
      return false;
    }
  }
  return true;
}

// check matching between two tuple types
static bool match_tuple_types(type_matcher_t *matcher, tuple_type_t *tau, tuple_type_t *sigma, bool eq) {
  uint32_t n;

  n = tau->nelem;
  return n == sigma->nelem && match_type_arrays(matcher, tau->elem, sigma->elem, n, eq);
}

/*
 * Check matching between two function types:
 * - we add equality constraints for the domain types
 * - we propagate 'eq' for the range
 */
static bool match_function_types(type_matcher_t *matcher, function_type_t *tau, function_type_t *sigma, bool eq) {
  uint32_t n;

  n = tau->ndom;
  return n == sigma->ndom
    && match_type_arrays(matcher, tau->domain, sigma->domain, n, true)
    && type_matcher_add_constraint(matcher, tau->range, sigma->range, eq);
}


/*
 * For instance types: we force equality
 * - e.g., List[X] is a subtype of List[Y] iff (List[X] == List[Y]) iff (X == Y)
 */
static bool match_instance_types(type_matcher_t *matcher, instance_type_t *tau, instance_type_t *sigma) {
  assert(tau->cid != sigma->cid || tau->arity == sigma->arity);
  return tau->cid == sigma->cid && match_type_arrays(matcher, tau->param, sigma->param, tau->arity, true);
}


/*
 * Add a type constraint:
 * - both tau and sigma must be valid types defined in matcher->types
 *   (and tau should contain type variables)
 * - if eq is true the constraint is "tau = sigma"
 *   otherwise it's "tau is a supertype of sigma"
 * - return false if the set of constraints is inconsistent
 * - return true otherwise and update the solution
 */
bool type_matcher_add_constraint(type_matcher_t *matcher, type_t tau, type_t sigma, bool eq) {
  type_table_t *table;
  int32_t k1, k2;

  table = matcher->types;

  assert(good_type(table, tau) && good_type(table, sigma));

  if (eq && ground_type(table, tau)) {
    return tau == sigma;
  }

  switch (type_kind(table, tau)) {
  case UNUSED_TYPE:
    assert(false); // should not happen
    break;

  case BOOL_TYPE:
  case INT_TYPE:
  case BITVECTOR_TYPE:
  case FF_TYPE:
  case SCALAR_TYPE:
  case UNINTERPRETED_TYPE:
    // tau is a minimal type to (sigma subtype of tau) is the same as tau == sigma
    assert(! eq);
    return tau == sigma;

  case REAL_TYPE:
    // (sigma subtype of tau) IFF (sigma is int or real)
    assert(! eq && tau == real_id);
    return sigma == int_id || sigma == real_id;

  case VARIABLE_TYPE:
    k1 = type_matcher_get_constraint(matcher, tau);
    k2 = merge_constraints(matcher, k1, mk_constraint_code(sigma, eq));
    if (k2 >= 0) {
      // no conflict
      if (k1 != k2) {
	type_matcher_set_constraint(matcher, tau, k2);
	if (k1 < 0) {
	  type_matcher_addvar(matcher, tau);
	}
      }
      return true;
    }
    break;


  case TUPLE_TYPE:
    if (type_kind(table, sigma) == TUPLE_TYPE) {
      k1 = type_matcher_get_constraint(matcher, tau);
      k2 = merge_constraints(matcher, k1, mk_constraint_code(sigma, eq));
      if (k2 >= 0) {
	if (k2 == k1) return true;
	// new constraint on tau encoded in k2
	sigma = arg_of_constraint(k2);
	eq = is_eq_constraint(eq);
	if (match_tuple_types(matcher, tuple_type_desc(table, tau), tuple_type_desc(table, sigma), eq)) {
	  type_matcher_set_constraint(matcher, tau, k2);
	  return true;
	}
      }
    }
    break;

  case FUNCTION_TYPE:
    if (type_kind(table, sigma) == FUNCTION_TYPE) {
      k1 = type_matcher_get_constraint(matcher, tau);
      k2 = merge_constraints(matcher, k1, mk_constraint_code(sigma, eq));
      if (k2 >= 0) {
	if (k1 == k2) return true;
	// new constraint on tau encoded in k2
	sigma = arg_of_constraint(k2);
	eq = is_eq_constraint(eq);
	if (match_function_types(matcher, function_type_desc(table, tau), function_type_desc(table, sigma), eq)) {
	  type_matcher_set_constraint(matcher, tau, k2);
	  return true;
	}
      }
    }
    break;

  case INSTANCE_TYPE:
    if (type_kind(table, sigma) == INSTANCE_TYPE) {
      // we ignore eq here (i.e., do as if eq is true)
      k1 = type_matcher_get_constraint(matcher, tau);
      k2 = merge_constraints(matcher, k1, mk_constraint_code(sigma, true));
      if (k2 >= 0) {
	if (k1 == k2) return true;
	// new constraint on tau
	sigma = arg_of_constraint(k2);
	if (match_instance_types(matcher, instance_type_desc(table, tau), instance_type_desc(table, sigma))) {
	  type_matcher_set_constraint(matcher, tau, k2);
	  return true;
	}
      }
    }
    break;
  }


  return false;
}



/*
 * Collect the substitution stored in matcher
 * - this is defined only if the matching worked (i.e., add_constraint did not return false)
 */
void type_matcher_build_subst(type_matcher_t *matcher) {
  uint32_t i, n;
  int32_t k;

  n = matcher->nvars;
  for (i=0; i<n; i++) {
    k = type_matcher_get_constraint(matcher, matcher->var[i]);
    assert(k >= 0);
    matcher->map[i] = arg_of_constraint(k);
  }
}



/*
 * Apply the matcher's substitution to tau
 */
type_t apply_type_matching(type_matcher_t *matcher, type_t tau) {
  return type_substitution(matcher->types, tau, matcher->nvars, matcher->var, matcher->map);
}






#if 0

/*
 * Check whether tau matches sigma
 * - if so build a substitution S, such that S(tau) = sigma
 * - S is stored in the hash_map subst
 *
 * - both tau and sigma must be defined in table.
 * - subst must be initialized.
 *
 * If subst is not empty, then the matching test is relative to the
 * current S (i.e., the search is for a substitution S' that extends S)
 */
bool types_match(type_table_t *table, type_t tau, type_t sigma, int_hmap_t *subst) {
  int_hmap_pair_t *p;
  type_kind_t sigma_kind;
  type_kind_t tau_kind;

  assert(good_type(table, tau) && good_type(table, sigma));

  if (ground_type(table, tau)) {
    return tau == sigma;
  }

  p = int_hmap_get(subst, tau);
  assert(p->key == tau);
  if (p->val >= 0) {
    assert(good_type(table, p->val));
    // tau is already mapped to p->val by subst
    return p->val == sigma;
  }

  tau_kind = type_kind(table, tau);
  if (tau_kind == VARIABLE_TYPE) {
    // success: add [tau := sigma] to hmap
    p->val = sigma;
    return true;
  }

  sigma_kind = type_kind(table, sigma);
  if (sigma_kind != tau_kind) {
    return false;
  }

  // recursively check whether the children match
  switch (type_kind(table, tau)) {
  case TUPLE_TYPE:
    if (! match_tuple_types(table, tuple_type_desc(table, tau), tuple_type_desc(table, sigma), subst)) {
      return false;
    }
    break;

  case FUNCTION_TYPE:
    if (! match_function_types(table, function_type_desc(table, tau), function_type_desc(table, sigma), subst)) {
      return false;
    }
    break;

  case INSTANCE_TYPE:
    if (! match_instance_types(table, instance_type_desc(table, tau), instance_type_desc(table, sigma), subst)) {
      return false;
    }
    break;

  default:
    assert(false);
    break;
  }


  /*
   * tau matches sigma: store [tau --> sigma] in subst
   * we can't reuse p here since the recursive calls may have modified the hash_map
   */
  p = int_hmap_get(subst, tau);
  assert(p->key == tau && p->val < 0);
  p->val = sigma;

  return true;
}


#endif


/*
 * TYPE NAMES
 */

/*
 * Assign name to type i.
 * - the previous mapping of name to other types (if any) is hidden.
 * - name must have a reference counter attached to it (cf. clone_string
 *   in memalloc.h).
 */
void set_type_name(type_table_t *table, type_t i, char *name) {
  if (table->name[i] == NULL) {
    table->name[i] = name;
    string_incref(name);
  }
  stbl_add(&table->stbl, name, i);
  string_incref(name);
}

/*
 * Get type mapped to the name (or NULL_TYPE)
 */
type_t get_type_by_name(type_table_t *table, const char *name) {
  // NULL_TYPE = -1 and stbl_find returns -1 if name is absent
  return stbl_find(&table->stbl, name);
}

/*
 * Remove a type name.
 */
void remove_type_name(type_table_t *table, const char *name) {
  stbl_remove(&table->stbl, name);
}


/*
 * Remove the name of t
 */
void clear_type_name(type_table_t *table, type_t t) {
  char *name;

  name = table->name[t];
  if (name != NULL) {
    if (stbl_find(&table->stbl, name) == t) {
      stbl_remove(&table->stbl, name);
    }
    table->name[t] = NULL;
    string_decref(name);
  }
}




/*
 * CARDINALITY
 */

/*
 * Approximate cardinality of tau[0] x ... x tau[n-1]
 * - returns the same value as card_of(tuple_type(tau[0] ... tau[n-1])) but does not
 *   construct the tuple type.
 */
uint32_t card_of_type_product(type_table_t *table, uint32_t n, const type_t *tau) {
  uint64_t card;

  card = type_card_product(table, n, tau);
  if (card > UINT32_MAX) {
    card = UINT32_MAX;
  }
  assert(1 <= card && card <= UINT32_MAX);

  return (uint32_t) card;
}



/*
 * Approximate cardinality of the domain and range of a function type tau
 */
uint32_t card_of_domain_type(type_table_t *table, type_t tau) {
  function_type_t *d;

  d = function_type_desc(table, tau);
  return card_of_type_product(table, d->ndom, d->domain);
}

uint32_t card_of_range_type(type_table_t *table, type_t tau) {
  return type_card(table, function_type_range(table, tau));
}



/*
 * Check whether a function type has a finite domain or range
 * - tau must be a function type.
 */
bool type_has_finite_domain(type_table_t *table, type_t tau) {
  function_type_t *fun;
  uint32_t flag;

  fun = function_type_desc(table, tau);
  flag = type_flags_conjunct(table, fun->ndom, fun->domain);
  return flag & TYPE_IS_FINITE_MASK;
}

bool type_has_finite_range(type_table_t *table, type_t tau) {
  return is_finite_type(table, function_type_range(table, tau));
}






/*
 * COMMON SUPERTYPE
 */

/*
 * Try to compute sup(tau1, tau2) cheaply
 * - return UNKNOWN_TYPE if that fails
 */
#define UNKNOWN_TYPE (-2)

static type_t cheap_sup(type_table_t *table, type_t tau1, type_t tau2) {
  assert(good_type(table, tau1) && good_type(table, tau2));

  if (tau1 == tau2) {
    return tau1;
  }

  if ((tau1 == int_id && tau2 == real_id) ||
      (tau1 == real_id && tau2 == int_id)) {
    return real_id;
  }

  switch (table->kind[tau1]) {
  case TUPLE_TYPE:
    if (table->kind[tau2] != TUPLE_TYPE ||
        tuple_type_arity(table, tau1) != tuple_type_arity(table, tau2)) {
      return NULL_TYPE;
    }
    break;

  case FUNCTION_TYPE:
    if (table->kind[tau2] != FUNCTION_TYPE ||
        function_type_arity(table, tau1) != function_type_arity(table, tau2)) {
      return NULL_TYPE;
    }
    break;

  default:
    return NULL_TYPE;
  }

  return UNKNOWN_TYPE;
}



/*
 * Construct sup of two tuple types of equal arity n:
 * - first tuple components are a[0] .... a[n-1]
 * - second tuple components are b[0] ... b[n-1]
 * The result is either NULL_TYPE or (tuple s[0] ... s[n-1])
 * where s[i] = sup(a[i], b[i]).
 */
static type_t sup_tuple_types(type_table_t *table, uint32_t n, type_t *a, type_t *b) {
  type_t buffer[8];
  type_t *s;
  type_t aux;
  uint32_t i;

  /*
   * For intermediate results, we use a buffer of 8 types.
   * That should be enough in most cases. Otherwise
   * we allocate a larger buffer s.
   */
  s = buffer;
  if (n > 8) {
    s = (type_t *) safe_malloc(n * sizeof(type_t));
  }

  for (i=0; i<n; i++) {
    aux = super_type(table, a[i], b[i]);
    if (aux == NULL_TYPE) goto done;
    s[i] = aux;
  }
  aux = tuple_type(table, n, s);

 done:
  if (n > 8) {
    safe_free(s);
  }
  return aux;
}


/*
 * Check whether a[0 ... n-1] and b[0 ... n-1]
 * are equal (i.e., same function domain).
 */
static bool equal_type_arrays(uint32_t n, type_t *a, type_t *b) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i] != b[i]) return false;
  }
  return true;
}


/*
 * Construct sup of two function types sigma1 and sigma2 of
 * equal domain and arity.
 * - n = arity
 * - a[0] ... a[n-1] = domain type
 * - tau1 = range of sigma1
 * - tau2 = range of sigma2
 *
 * The result is either the function type [a[0] ... a[n-1] --> sup(tau1, tau2)]
 * or NULL_TYPE.
 */
static type_t sup_fun_types(type_table_t *table, uint32_t n, type_t *a, type_t tau1, type_t tau2) {
  type_t aux;

  aux = super_type(table, tau1, tau2);
  if (aux != NULL_TYPE) {
    aux = function_type(table, aux, n, a);
  }
  return aux;
}


/*
 * Compute the smallest supertype of tau1 and tau2.  Use the cheap
 * method first. If that fails, compute the result and keep the result
 * in the internal sup_tbl cache.
 */
type_t super_type(type_table_t *table, type_t tau1, type_t tau2) {
  tuple_type_t *tup1, *tup2;
  function_type_t *fun1, *fun2;
  int_hmap2_t *sup_tbl;
  int_hmap2_rec_t *r;
  type_t aux;

  assert(good_type(table, tau1) && good_type(table, tau2));

  aux = cheap_sup(table, tau1, tau2);
  if (aux == UNKNOWN_TYPE) {
    /*
     * Cheap_sup failed.
     * Check whether sup(tau1, tau2) is already in the cache.
     * If it's not do the computation and add the
     * result to the cache.
     */

    // Normalize. We want tau1 < tau2
    if (tau1 > tau2) {
      aux = tau1; tau1 = tau2; tau2 = aux;
    }
    assert(tau1 < tau2);

    sup_tbl = get_sup_table(table);
    r = int_hmap2_find(sup_tbl, tau1, tau2);
    if (r != NULL) {
      aux = r->val;
    } else {
      /*
       * The result is not in the cache.
       */
      if (table->kind[tau1] == TUPLE_TYPE) {
        tup1 = tuple_type_desc(table, tau1);
        tup2 = tuple_type_desc(table, tau2);
        assert(tup1->nelem == tup2->nelem);
        aux = sup_tuple_types(table, tup1->nelem, tup1->elem, tup2->elem);

      } else {
        fun1 = function_type_desc(table, tau1);
        fun2 = function_type_desc(table, tau2);
        assert(fun1->ndom == fun2->ndom);
        aux = NULL_TYPE;
        if (equal_type_arrays(fun1->ndom, fun1->domain, fun2->domain)) {
          aux = sup_fun_types(table, fun1->ndom, fun1->domain, fun1->range, fun2->range);
        }
      }

      int_hmap2_add(sup_tbl, tau1, tau2, aux);
    }
  }

  assert(aux == NULL_TYPE || good_type(table, aux));

  return aux;
}



/*
 * COMMON SUBTYPE
 */

/*
 * Try to compute inf(tau1, tau2) cheaply.
 * Return UNKNOWN_TYPE if that fails.
 */
static type_t cheap_inf(type_table_t *table, type_t tau1, type_t tau2) {
  assert(good_type(table, tau1) && good_type(table, tau2));

  if (tau1 == tau2) {
    return tau1;
  }

  if ((tau1 == int_id && tau2 == real_id) ||
      (tau1 == real_id && tau2 == int_id)) {
    return int_id;
  }

  switch (table->kind[tau1]) {
  case TUPLE_TYPE:
    if (table->kind[tau2] != TUPLE_TYPE ||
        tuple_type_arity(table, tau1) != tuple_type_arity(table, tau2)) {
      return NULL_TYPE;
    }
    break;

  case FUNCTION_TYPE:
    if (table->kind[tau2] != FUNCTION_TYPE ||
        function_type_arity(table, tau1) != function_type_arity(table, tau2)) {
      return NULL_TYPE;
    }
    break;

  default:
    return NULL_TYPE;
  }

  return UNKNOWN_TYPE;
}



/*
 * Construct inf of two tuple types of equal arity n:
 * - first tuple components are a[0] .... a[n-1]
 * - second tuple components are b[0] ... b[n-1]
 * The result is either NULL_TYPE or (tuple s[0] ... s[n-1])
 * where s[i] = inf(a[i], b[i]).
 */
static type_t inf_tuple_types(type_table_t *table, uint32_t n, type_t *a, type_t *b) {
  type_t buffer[8];
  type_t *s;
  type_t aux;
  uint32_t i;

  /*
   * For intermediate results, we use a buffer of 8 types.
   * That should be enough in most cases. Otherwise
   * we allocate a larger buffer s.
   */
  s = buffer;
  if (n > 8) {
    s = (type_t *) safe_malloc(n * sizeof(type_t));
  }

  for (i=0; i<n; i++) {
    aux = inf_type(table, a[i], b[i]);
    if (aux == NULL_TYPE) goto done;
    s[i] = aux;
  }
  aux = tuple_type(table, n, s);

 done:
  if (n > 8) {
    safe_free(s);
  }
  return aux;
}


/*
 * Construct inf of two function types sigma1 and sigma2 of
 * equal domain and arity.
 * - n = arity
 * - a[0] ... a[n-1] = domain type
 * - tau1 = range of sigma1
 * - tau2 = range of sigma2
 *
 * The result is either the function type [a[0] ... a[n-1] --> inf(tau1, tau2)]
 * or NULL_TYPE.
 */
static type_t inf_fun_types(type_table_t *table, uint32_t n, type_t *a, type_t tau1, type_t tau2) {
  type_t aux;

  aux = inf_type(table, tau1, tau2);
  if (aux != NULL_TYPE) {
    aux = function_type(table, aux, n, a);
  }
  return aux;
}


/*
 * Compute the largest common subtype of tau1 and tau2.  Use the cheap
 * method first. If that fails, compute the result and keep the result
 * in the internal inf_tbl cache.
 */
type_t inf_type(type_table_t *table, type_t tau1, type_t tau2) {
  tuple_type_t *tup1, *tup2;
  function_type_t *fun1, *fun2;
  int_hmap2_t *inf_tbl;
  int_hmap2_rec_t *r;
  type_t aux;

  assert(good_type(table, tau1) && good_type(table, tau2));

  aux = cheap_inf(table, tau1, tau2);
  if (aux == UNKNOWN_TYPE) {
    /*
     * Cheap_inf failed.
     * Check whether inf(tau1, tau2) is already in the cache.
     * If it's not do the computation and add the
     * result to the cache.
     */

    // Normalize. We want tau1 < tau2
    if (tau1 > tau2) {
      aux = tau1; tau1 = tau2; tau2 = aux;
    }
    assert(tau1 < tau2);

    inf_tbl = get_inf_table(table);
    r = int_hmap2_find(inf_tbl, tau1, tau2);
    if (r != NULL) {
      aux = r->val;
    } else {
      /*
       * The result is not in the cache.
       */
      if (table->kind[tau1] == TUPLE_TYPE) {
        tup1 = tuple_type_desc(table, tau1);
        tup2 = tuple_type_desc(table, tau2);
        assert(tup1->nelem == tup2->nelem);
        aux = inf_tuple_types(table, tup1->nelem, tup1->elem, tup2->elem);

      } else {
        fun1 = function_type_desc(table, tau1);
        fun2 = function_type_desc(table, tau2);
        assert(fun1->ndom == fun2->ndom);
        aux = NULL_TYPE;
        if (equal_type_arrays(fun1->ndom, fun1->domain, fun2->domain)) {
          aux = inf_fun_types(table, fun1->ndom, fun1->domain, fun1->range, fun2->range);
        }
      }

      int_hmap2_add(inf_tbl, tau1, tau2, aux);
    }
  }

  assert(aux == NULL_TYPE || good_type(table, aux));

  return aux;
}




/*
 * MAXIMAL SUPERTYPE
 */

/*
 * Try to cheaply compute the maximal super type of tau
 * - return NULL_TYPE if that fails
 */
static type_t cheap_max_super_type(type_table_t *table, type_t tau) {
  type_t sigma;

  sigma = NULL_TYPE;
  if (is_maxtype(table, tau)) {
    sigma = tau;
  } else if (tau == int_id) {
    sigma = real_id;
  }

  return sigma;
}


/*
 * Maximal supertype of a tuple type
 */
static type_t max_tuple_super_type(type_table_t *table, tuple_type_t *tup) {
  type_t buffer[8];
  type_t *s;
  uint32_t i, n;
  type_t tau;

  n = tup->nelem;
  s = buffer;
  if (n > 8) {
    s = safe_malloc(n * sizeof(type_t));
  }

  for (i=0; i<n; i++) {
    s[i] = max_super_type(table, tup->elem[i]);
  }

  tau = tuple_type(table, n, s);

  if (n > 8) {
    safe_free(s);
  }

  return tau;
}


/*
 * Maximal supertype of a function type
 */
static type_t max_function_super_type(type_table_t *table, function_type_t *fun) {
  type_t tau;

  tau = max_super_type(table, fun->range);
  return function_type(table, tau, fun->ndom, fun->domain);
}


/*
 * Build the largest type that's a supertype of tau
 */
type_t max_super_type(type_table_t *table, type_t tau) {
  int_hmap_t *max_tbl;
  int_hmap_pair_t *r;
  type_t aux;

  assert(good_type(table, tau));

  aux = cheap_max_super_type(table, tau);
  if (aux == NULL_TYPE) {
    max_tbl = get_max_table(table);
    r = int_hmap_find(max_tbl, tau);
    if (r != NULL) {
      aux = r->val;
    } else {
      // max is not in the cache
      if (table->kind[tau] == TUPLE_TYPE) {
        aux = max_tuple_super_type(table, tuple_type_desc(table, tau));
      } else {
        aux = max_function_super_type(table, function_type_desc(table,tau));
      }
      int_hmap_add(max_tbl, tau, aux);
    }
  }

  assert(good_type(table, aux));

  return aux;
}




/*
 * SUBTYPE AND COMPATIBILITY
 */

/*
 * Check whether tau1 is a subtype if tau2.
 *
 * Side effects: this is implemented using super_type so this may create
 * new types in the table.
 */
bool is_subtype(type_table_t *table, type_t tau1, type_t tau2) {
  return super_type(table, tau1, tau2) == tau2;
}


/*
 * Check whether tau1 and tau2 are compatible.
 *
 * Side effects: use the super_type function. So this may create new
 * types in the table.
 */
bool compatible_types(type_table_t *table, type_t tau1, type_t tau2) {
  return super_type(table, tau1, tau2) != NULL_TYPE;
}




/*
 * MACRO CONSTRUCTORS
 */

/*
 * NOTES
 *
 * 1) macro names have the same scoping mechanism as
 *    term and type names. If a macro of a given name is
 *    added to the table, and name refers to an existing
 *    macro then the current mapping is hidden. It will be
 *    restored after a call to remove_type_macro_name.
 *
 * 2) the implementation uses character strings with reference
 *    counting (cf. refcount_strings.h). The parameter 'name'
 *    in add_type_macro and add_type_constructor must be
 *    the result of 'clone_string'.
 */

/*
 * Add a macro descriptor:
 * - name = macro name
 * - n = arity. It must be no more than TYPE_MACRO_MAX_ARITY
 * - vars = array of n type variables (must be all distinct)
 * - body = type
 */
int32_t add_type_macro(type_table_t *table, char *name, uint32_t n, const type_t *vars, type_t body) {
  type_mtbl_t *mtbl;
  type_macro_t *d;
  int32_t i;

  mtbl = get_macro_table(table);

  assert(body != NULL_TYPE);

  i = allocate_macro_id(mtbl);
  d = new_descriptor(name, n, vars, body);
  assert(! has_int_tag(d));
  mtbl->data[i] = d;

  stbl_add(&mtbl->stbl, name, i);
  string_incref(name);

  return i;
}


/*
 * Add an uninterpreted type constructor:
 * - name = macro name
 * - n = arity. It must be no more than TYPE_MACRO_MAX_ARITY
 */
int32_t add_type_constructor(type_table_t *table, char *name, uint32_t n) {
  type_mtbl_t *mtbl;
  type_macro_t *d;
  int32_t i;

  mtbl = get_macro_table(table);

  i = allocate_macro_id(mtbl);
  d = new_constructor(name, n);
  assert(! has_int_tag(d));
  mtbl->data[i] = d;

  stbl_add(&mtbl->stbl, name, i);
  string_incref(name);

  return i;
}


/*
 * Get a macro id of the given name
 * - return -1 if there's no macro with this name
 */
int32_t get_type_macro_by_name(type_table_t *table, const char *name) {
  type_mtbl_t *mtbl;
  int32_t id;

  id = -1;
  mtbl = table->macro_tbl;
  if (mtbl != NULL) {
    id = stbl_find(&mtbl->stbl, name);
  }

  return id;
}


/*
 * Get the descriptor for the given id
 * - return NULL if id is not valid (including if it refers to a deleted macro)
 */
type_macro_t *type_macro(type_table_t *table, int32_t id) {
  type_mtbl_t *mtbl;
  type_macro_t *macro;

  mtbl = table->macro_tbl;
  macro = NULL;
  if (mtbl != NULL && good_type_macro(mtbl, id)) {
    macro = mtbl->data[id];
  }

  return macro;
}


/*
 * Remove the current mapping of 'name' to a macro id
 * - no change if 'name' does not refer to any macro
 * - otherwise, the current reference for 'name' is removed
 *   and the previous mapping is restored (if any).
 */
void remove_type_macro_name(type_table_t *table, const char *name) {
  type_mtbl_t *mtbl;

  mtbl = table->macro_tbl;
  if (mtbl != NULL) {
    stbl_remove(&mtbl->stbl, name);
  }
}



/*
 * Keep alive function used in delete_type_macro:
 * - aux is a pointer to an integer variable and
 *   *aux = id of the macro to delete
 * - r is a record in the tuple cache
 * - r must be deleted if its first element r->key[0] is equal to id
 */
static bool keep_cached_tuple_alive(void *aux, tuple_hmap_rec_t *r) {
  assert(r->arity > 1);
  return r->key[0] != *((int32_t *) aux);
}


/*
 * Remove macro of the given id
 * - id must be a valid macro index
 * - the macro name is deleted (from the symbol table)
 * - all instances of this macro are also deleted.
 */
void delete_type_macro(type_table_t *table, int32_t id) {
  type_mtbl_t *mtbl;
  type_macro_t *macro;

  mtbl = table->macro_tbl;

  assert(mtbl != NULL && good_type_macro(mtbl, id));

  macro = mtbl->data[id];
  stbl_remove(&mtbl->stbl, macro->name);
  tuple_hmap_gc(&mtbl->cache, &id, keep_cached_tuple_alive);
  free_macro_id(mtbl, id);
}



/*
 * Macro instance: apply a macro to the given actual parameters
 * - id = macro id
 * - n = number of actuals
 * - actual = array of n types (actual parameters)
 * - each parameter must be a valid type
 * - n must be equal to the macro arity.
 *
 * If the macro is a type constructor (i.e., body = NULL_TYPE) then
 * a new instance is constructed.
 *
 * If the macro is a not a type constructor:
 * - Check whether this instance already exists in mtbl->hmap.
 * - If so, the instance is returned, otherwise, the
 *   instance is constructed by substituting variables in body with
 *   the actuals. The result is stored in mtbl->hmap.
 */
type_t instantiate_type_macro(type_table_t *table, int32_t id, uint32_t n, const type_t *actual) {
  type_mtbl_t *mtbl;
  int32_t aux[10];
  int32_t *key;
  tuple_hmap_rec_t *r;
  type_macro_t *d;
  bool new;
  uint32_t i;
  type_t result;


  // id is a good macro with arity n
  assert(type_macro(table, id)->arity == n);

  /*
   * By default, we use a buffer of 10 integers to store id + actuals
   * If more is needed, a larger array is allocated here.
   */
  key = aux;
  if (n > 9) {
    key = (int32_t *) safe_malloc((n+1) * sizeof(int32_t));
  }

  key[0] = id;
  for (i=0; i<n; i++) {
    key[1 + i] = actual[i];
  }

  mtbl = table->macro_tbl;
  assert(mtbl != NULL);
  d = mtbl->data[id];
  assert(d->arity == n);
  if (d->body == NULL_TYPE) {
    // type constructor: new instance
    result = instance_type(table, id, n, actual);
  } else {
    // check the cache
    r = tuple_hmap_get(&mtbl->cache, n+1, key, &new);
    result = r->value;
    if (new) {
      result = type_substitution(table, d->body, n, d->vars, actual);
      assert(tuple_hmap_find(&mtbl->cache, n+1, key) == r); // i.e. r is still valid
      r->value = result;
    }
  }

  if (n > 9) {
    safe_free(key);
  }

  return result;
}







/*
 * GARBAGE COLLECTION
 */

/*
 * Remove type i from the hash-consing table
 */
static void erase_hcons_type(type_table_t *table, type_t i) {
  uint32_t k;

  switch (table->kind[i]) {
  case BITVECTOR_TYPE:
    k = hash_bvtype(table->desc[i].integer);
    break;

  case FF_TYPE:
    k = hash_fftype(table->desc[i].integer);
    break;

  case VARIABLE_TYPE:
    k = hash_typevar(table->desc[i].integer);
    break;

  case TUPLE_TYPE:
    k = hash_tupletype(table->desc[i].ptr);
    break;

  case FUNCTION_TYPE:
    k = hash_funtype(table->desc[i].ptr);
    break;

  case INSTANCE_TYPE:
    k = hash_instancetype(table->desc[i].ptr);
    break;

  default:
    return;
  }

  int_htbl_erase_record(&table->htbl, k, i);
}




/*
 * Mark all descendants of i whose ids are less than ptr.
 * - i must be a marked type (and not already deleted)
 *
 * NOTE: we use a recursive function to propagate the marks.
 * That should be safe as there's little risk of stack overflow.
 */
static void mark_reachable_types(type_table_t *table, type_t ptr, type_t i);

// mark i if it's not marked already then explore its children if i < ptr
static void mark_and_explore(type_table_t *table, type_t ptr, type_t i) {
  if (! type_is_marked(table, i)) {
    type_table_set_gc_mark(table, i);
    if (i < ptr) {
      mark_reachable_types(table, ptr, i);
    }
  }
}

static void mark_reachable_types(type_table_t *table, type_t ptr, type_t i) {
  tuple_type_t *tup;
  function_type_t *fun;
  instance_type_t *inst;
  uint32_t n, j;

  assert(type_is_marked(table, i) &&  table->kind[i] != UNUSED_TYPE);

  switch (table->kind[i]) {
  case TUPLE_TYPE:
    tup = table->desc[i].ptr;
    n = tup->nelem;
    for (j=0; j<n; j++) {
      mark_and_explore(table, ptr, tup->elem[j]);
    }
    break;

  case FUNCTION_TYPE:
    fun = table->desc[i].ptr;
    mark_and_explore(table, ptr, fun->range);
    n = fun->ndom;
    for (j=0; j<n; j++) {
      mark_and_explore(table, ptr, fun->domain[j]);
    }
    break;

  case INSTANCE_TYPE:
    inst = table->desc[i].ptr;
    n = inst->arity;
    for (j=0; j<n; j++) {
      mark_and_explore(table, ptr, inst->param[j]);
    }
    break;

  default:
    break;
  }
}


/*
 * Propagate the marks:
 * - on entry: all roots are marked
 * - on exit: every type reachable from a root is marked
 */
static void mark_live_types(type_table_t *table) {
  uint32_t i, n;

  n = table->nelems;
  for (i=0; i<n; i++) {
    if (type_is_marked(table, i)) {
      mark_reachable_types(table, i, i);
    }
  }
}


/*
 * Iterator to mark types present in the symbol table
 * - aux must be a pointer to the type table
 * - r = live record in the symbol table so r->value
 *   is the id of a type to preserve.
 */
static void mark_symbol(void *aux, const stbl_rec_t *r) {
  type_table_set_gc_mark(aux, r->value);
}


/*
 * Filter to remove dead types from the symbol table.
 * - aux must be a pointer to the type table
 * - r = record in the symbol table: if the function returns true,
 *   r will be finalized then removed from the symbol table.
 */
static bool dead_type_symbol(void *aux, const stbl_rec_t *r) {
  return !type_is_marked(aux, r->value);
}

/*
 * Keep-alive function for the sup/inf caches
 * - record (k0, k1 --> x) is kept in the caches
 *   if k0, k1, and x haven't been deleted
 * - aux is a pointer to the type table
 */
static bool keep_in_cache(void *aux, int_hmap2_rec_t *r) {
  return good_type(aux, r->k0) && good_type(aux, r->k1) &&
    good_type(aux, r->val);
}


/*
 * Keep-alive function for the max cache
 * - record (k --> x) is kept if k and x haven't been deleted
 */
static bool keep_in_max_table(void *aux, const int_hmap_pair_t *r) {
  return good_type(aux, r->key) && good_type(aux, r->val);
}


/*
 * Keep-alive function for the macro instance cache
 * - aux is a pointer to the type table
 * - record r->key is an array of n integers
 *   r->key[0] = macro id
 *   r->key[1 ... n] = types
 *   r->val = type
 * - the record is kept if all types are good
 */
static bool keep_in_tuple_cache(void *aux, tuple_hmap_rec_t *r) {
  uint32_t i, n;

  if (! good_type(aux, r->value)) return false;

  n = r->arity;
  assert(n > 1);
  for (i=1; i<n; i++) {
    if (! good_type(aux, r->key[i])) return false;
  }

  return true;
}


/*
 * Call the garbage collector:
 * - delete every type not reachable from a root
 * - if keep_named is true, all named types (reachable from the symbol table)
 *   are preserved. Otherwise, all live types are marked and all references
 *   to dead types are remove from the symbol table.
 * - cleanup the caches
 * - then clear all the marks
 */
void type_table_gc(type_table_t *table, bool keep_named)  {
  uint32_t i, n;

  // mark every type present in the symbol table
  if (keep_named) {
    stbl_iterate(&table->stbl, table, mark_symbol);
  }

  // mark the three predefined types
  type_table_set_gc_mark(table, bool_id);
  type_table_set_gc_mark(table, int_id);
  type_table_set_gc_mark(table, real_id);

  // propagate the marks
  mark_live_types(table);

  // remove unmarked types from the symbol table
  if (!keep_named) {
    stbl_remove_records(&table->stbl, table, dead_type_symbol);
  }

  // delete every unmarked type
  n = table->nelems;
  for (i=0; i<n; i++) {
    if (! type_is_marked(table, i)) {
      erase_hcons_type(table, i);
      erase_type(table, i);
    }
    type_table_clr_gc_mark(table, i);
  }

  // cleanup the inf/sup caches if they exist
  if (table->sup_tbl != NULL) {
    int_hmap2_gc(table->sup_tbl, table, keep_in_cache);
  }

  if (table->inf_tbl != NULL) {
    int_hmap2_gc(table->inf_tbl, table, keep_in_cache);
  }

  // cleanup the max cache
  if (table->max_tbl != NULL) {
    int_hmap_remove_records(table->max_tbl, table, keep_in_max_table);
  }

  // cleanup the macro table cache too
  if (table->macro_tbl != NULL) {
    tuple_hmap_gc(&table->macro_tbl->cache, table, keep_in_tuple_cache);
  }

}
