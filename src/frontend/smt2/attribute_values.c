/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <string.h>

#include "utils/memalloc.h"
#include "frontend/smt2/attribute_values.h"


/*
 * Allocate a bit-vector descriptor:
 * - n = number of bits
 */
static bvconst_attr_t *alloc_bvconst_attr(uint32_t n) {
  uint32_t w;

  w = (n + 31) >> 5; // ceil(n/32);
  return (bvconst_attr_t *) safe_malloc(sizeof(bvconst_attr_t) + w * sizeof(uint32_t));
}

/*
 * Allocate an array descriptor:
 * - n = number of elements
 */
static attr_list_t *alloc_attr_list(uint32_t n) {
  if (n > MAX_ATTR_LIST_SIZE) {
    out_of_memory();
  }
  return (attr_list_t *) safe_malloc(sizeof(attr_list_t) + n * sizeof(aval_t));
}


/*
 * Initialize table: use default initial size
 */
void init_attr_vtbl(attr_vtbl_t *table) {
  uint32_t n;

  n = ATTR_VTBL_DEF_SIZE;
  assert(n <= ATTR_VTBL_MAX_SIZE);

  table->tag = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  table->desc = (attr_desc_t *) safe_malloc(n * sizeof(attr_desc_t));
  table->refcount = (uint32_t *) safe_malloc(n * sizeof(uint32_t));

  table->size = n;
  table->nelems = 0;
  table->free_idx = -1;
}


/*
 * Make the table 50% larger
 */
static void extend_attr_vtbl(attr_vtbl_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  if (n > ATTR_VTBL_MAX_SIZE) {
    out_of_memory();
  }

  table->tag = (uint8_t *) safe_realloc(table->tag, n * sizeof(uint8_t));
  table->desc = (attr_desc_t *) safe_realloc(table->desc, n * sizeof(attr_desc_t));
  table->refcount = (uint32_t *) safe_realloc(table->refcount, n * sizeof(uint32_t));

  table->size = n;
}


/*
 * Allocate a element: return its index
 */
static int32_t alloc_aval(attr_vtbl_t *table) {
  int32_t i;

  i = table->free_idx;
  if (i >= 0) {
    assert(i < table->nelems && table->tag[i] == ATTR_DELETED);
    table->free_idx = table->desc[i].next;
  } else {
    i = table->nelems;
    table->nelems = i+1;
    if (i == table->size) {
      extend_attr_vtbl(table);
    }
  }
  return i;
}


/*
 * Delete descriptor of element i
 */
static void free_descriptor(attr_vtbl_t *table, int32_t i) {
  assert(0 <= i && i < table->nelems);
  switch (table->tag[i]) {
  case ATTR_DELETED:
    break;
  case ATTR_RATIONAL:
    q_clear(&table->desc[i].rational);
    break;
  case ATTR_BV:
  case ATTR_STRING:
  case ATTR_SYMBOL:
  case ATTR_LIST:
    safe_free(table->desc[i].ptr);
    break;
  default:
    assert(false);
    break;
  }
}

/*
 * Delete element i and add it to the free list
 */
static void delete_aval(attr_vtbl_t *table, int32_t i) {
  assert(good_aval(table, i));
  free_descriptor(table, i);
  table->tag[i] = ATTR_DELETED;
  table->desc[i].next = table->free_idx;
  table->free_idx = i;
}

/*
 * Empty the table
 */
void reset_attr_vtbl(attr_vtbl_t *table) {
  uint32_t i, n;

  n = table->nelems;
  for (i=0; i<n; i++) {
    free_descriptor(table, i);
  }
  table->nelems = 0;
  table->free_idx = -1;
}


/*
 * Delete the table
 */
void delete_attr_vtbl(attr_vtbl_t *table) {
  uint32_t i, n;

  n = table->nelems;
  for (i=0; i<n; i++) {
    free_descriptor(table, i);
  }
  safe_free(table->tag);
  safe_free(table->desc);
  safe_free(table->refcount);
}


/*
 * Copy q in the table
 */
aval_t attr_vtbl_rational(attr_vtbl_t *table, rational_t *q) {
  int32_t i;

  i = alloc_aval(table);
  table->tag[i] = ATTR_RATIONAL;
  q_init(&table->desc[i].rational);
  q_set(&table->desc[i].rational, q);
  table->refcount[i] = 0;

  return i;
}

/*
 * Copy bitvector constant c.
 * n = number of bits (must be no more than 64)
 */
aval_t attr_vtbl_bv64(attr_vtbl_t *table, uint32_t n, uint64_t c) {
  bvconst_attr_t *tmp;
  int32_t i;

  tmp = alloc_bvconst_attr(n);
  tmp->nbits = n;
  tmp->data[0] = c & 0xFFFFFFFF;
  if (n > 32) {
    tmp->data[1] = c>>32;
  }

  i = alloc_aval(table);
  table->tag[i] = ATTR_BV;
  table->desc[i].ptr = tmp;
  table->refcount[i] = 0;

  return i;
}

/*
 * Same thing for constant c = array of 32bit words
 */
aval_t attr_vtbl_bv(attr_vtbl_t *table, uint32_t n, uint32_t *c) {
  bvconst_attr_t *tmp;
  uint32_t j;
  int32_t i;

  tmp = alloc_bvconst_attr(n);
  tmp->nbits = n;
  n = (n + 31) >> 5; // number of words
  for (j=0; j<n; j++) {
    tmp->data[j] = c[j];
  }

  i = alloc_aval(table);
  table->tag[i] = ATTR_BV;
  table->desc[i].ptr = tmp;
  table->refcount[i] = 0;

  return i;
}


/*
 * String or symbol
 */
aval_t attr_vtbl_str(attr_vtbl_t *table, const char *s, aval_type_t tag) {
  char *tmp;
  int32_t i;

  assert(tag == ATTR_STRING || tag == ATTR_SYMBOL);
  // we ignore the risk of overflow here
  tmp = (char *) safe_malloc(strlen(s) + 1);
  strcpy(tmp, s);

  i = alloc_aval(table);
  table->tag[i] = tag;
  table->desc[i].ptr = tmp;
  table->refcount[i] = 0;

  return i;
}


/*
 * List a[0 ... n-1]
 */
aval_t attr_vtbl_list(attr_vtbl_t *table, uint32_t n, aval_t a[]) {
  attr_list_t *tmp;
  uint32_t j;
  int32_t i;

  tmp = alloc_attr_list(n);
  tmp->nelems = n;
  for (j=0; j<n; j++) {
    tmp->data[j] = a[j];
    aval_incref(table, a[j]);
  }

  i = alloc_aval(table);
  table->tag[i] = ATTR_LIST;
  table->desc[i].ptr = tmp;
  table->refcount[i] = 0;

  return i;
}


/*
 * Auxiliary function: call decref on all elements of d
 */
static void list_decref(attr_vtbl_t *table, attr_list_t *d) {
  uint32_t i, n;

  n = d->nelems;
  for (i=0; i<n; i++) {
    aval_decref(table, d->data[i]);
  }
}

/*
 * Decrement the reference counter on object i
 */
void aval_decref(attr_vtbl_t *table, aval_t i) {
  assert(good_aval(table, i) && table->refcount[i] > 0);
  table->refcount[i] --;
  if (table->refcount[i] == 0) {
    if (table->tag[i] == ATTR_LIST) {
      list_decref(table, table->desc[i].ptr);
    }
    delete_aval(table, i);
  }
}
