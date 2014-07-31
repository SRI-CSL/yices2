/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SUPPORT FOR SMT-LIB 2: ATTRIBUTE VALUES
 */

#ifndef __ATTRIBUTE_VALUES_H
#define __ATTRIBUTE_VALUES_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "terms/rationals.h"

/*
 * Attributes and attribute values are used in
 *   (set-option <keyword> <attribute-value>)
 *   (set-info <keyword> <attribute-value>)
 *   (! <term> <attributes>+ )
 *
 * An attribute value can be
 * - rational   (for  <numeral> or  <decimal>)
 * - a bitvector constant (<hexadecimal> or <binary>)
 * - a string (for <string>, <symbol>, and <keyword>)
 * - a non-empty list of attribute values.
 *
 * We store them in a table, and use integer indices
 * to refer to them. Index -1  denotes nil.
 */

typedef int32_t aval_t;

typedef enum aval_type {
  ATTR_DELETED,
  ATTR_RATIONAL,
  ATTR_BV,
  ATTR_STRING,
  ATTR_SYMBOL,
  ATTR_LIST,
} aval_type_t;

#define AVAL_NULL (-1)

/*
 * Descriptors:
 *  numeral/decimal --> rational
 *  hexa/binary     --> bvconst: number of bits + word array
 *  string/symbol   --> string
 *  list            --> array + size
 */
typedef struct bvconst_attr_s {
  uint32_t nbits;
  uint32_t data[0];
} bvconst_attr_t;

typedef struct attr_list_s {
  uint32_t nelems;
  aval_t data[0];
} attr_list_t;

typedef union {
  void *ptr;
  rational_t rational;
  int32_t next; // for free list
} attr_desc_t;

#define MAX_ATTR_LIST_SIZE ((UINT32_MAX-sizeof(attr_list_t))/sizeof(aval_t))

/*
 * Table:
 * - array of tags + descriptors + ref counter
 * - deleted elements are marked with ATTR_DELETED
 *   then the descriptor is used as an index = successor
 *   in the free list
 */
typedef struct attr_vtbl_s {
  uint8_t *tag;
  attr_desc_t *desc;
  uint32_t *refcount;
  uint32_t size;
  uint32_t nelems;
  int32_t free_idx;
} attr_vtbl_t;

#define ATTR_VTBL_MAX_SIZE (UINT32_MAX/sizeof(attr_desc_t))
#define ATTR_VTBL_DEF_SIZE 20

/*
 * Initialize table to the default size
 */
extern void init_attr_vtbl(attr_vtbl_t *table);

/*
 * Delete
 */
extern void delete_attr_vtbl(attr_vtbl_t *table);

/*
 * Reset: empty the table
 */
extern void reset_attr_vtbl(attr_vtbl_t *table);

/*
 * Constant constructors return a new index
 * For bitvectors: two constructors can be used
 * - attr_vtbl_bv64(table, n, c): n = number of bits, c = constant
 * - attr_vtbl_bv(table, n, c): n = number of bits, c = word array
 *
 * Warning: the new element has refcount 0
 */
extern aval_t attr_vtbl_rational(attr_vtbl_t *table, rational_t *q);
extern aval_t attr_vtbl_bv64(attr_vtbl_t *table, uint32_t n, uint64_t c);
extern aval_t attr_vtbl_bv(attr_vtbl_t *table, uint32_t n, uint32_t *c);

// string/symbol constructor with the given tag
extern aval_t attr_vtbl_str(attr_vtbl_t *table, const char *s, aval_type_t tag);

static inline aval_t attr_vtbl_string(attr_vtbl_t *table, const char *s) {
  return attr_vtbl_str(table, s, ATTR_STRING);
}

static inline aval_t attr_vtbl_symbol(attr_vtbl_t *table, const char *s) {
  return attr_vtbl_str(table, s, ATTR_SYMBOL);
}


/*
 * List a[0 ... n-1]
 */
extern aval_t attr_vtbl_list(attr_vtbl_t *table, uint32_t n, aval_t a[]);

/*
 * Increment/decrement the reference counter
 */
static inline void aval_incref(attr_vtbl_t *table, aval_t i) {
  assert(0 <= i && i < table->nelems);
  table->refcount[i] ++;
}

extern void aval_decref(attr_vtbl_t *table, aval_t i);


/*
 * Access to the components
 */
static inline bool valid_aval(attr_vtbl_t *table, aval_t i) {
  return 0 <= i && i < table->nelems;
}

static inline bool good_aval(attr_vtbl_t *table, aval_t i) {
  return valid_aval(table, i) && table->tag[i] != ATTR_DELETED;
}

static inline aval_type_t aval_tag(attr_vtbl_t *table, aval_t i) {
  assert(valid_aval(table, i));
  return table->tag[i];
}

static inline uint32_t aval_refcount(attr_vtbl_t *table, aval_t i) {
  assert(valid_aval(table, i));
  return table->refcount[i];
}

static inline attr_desc_t *aval_descriptor(attr_vtbl_t *table, aval_t i) {
  assert(good_aval(table, i));
  return table->desc + i;
}

// use with care: pointer can become invalid after creation of new aval
static inline rational_t *aval_rational(attr_vtbl_t *table, aval_t i) {
  assert(aval_tag(table, i) == ATTR_RATIONAL);
  return &table->desc[i].rational;
}

static inline bvconst_attr_t *aval_bvconst(attr_vtbl_t *table, aval_t i) {
  assert(aval_tag(table, i) == ATTR_BV);
  return table->desc[i].ptr;
}

static inline char *aval_string(attr_vtbl_t *table, aval_t i) {
  assert(aval_tag(table, i) == ATTR_STRING);
  return table->desc[i].ptr;
}

static inline char *aval_symbol(attr_vtbl_t *table, aval_t i) {
  assert(aval_tag(table, i) == ATTR_SYMBOL);
  return table->desc[i].ptr;
}

static inline attr_list_t *aval_list(attr_vtbl_t *table, aval_t i) {
  assert(aval_tag(table, i) == ATTR_LIST);
  return table->desc[i].ptr;
}


#endif /* __ATTRIBUTE_VALUES_H */
