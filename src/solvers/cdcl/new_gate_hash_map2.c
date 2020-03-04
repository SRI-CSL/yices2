/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2020 SRI International.
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
 * HASH TABLE FOR BOOLEAN GATES (ANOTHER VARIANT)
 */

#include <assert.h>

#include "solvers/cdcl/new_gate_hash_map2.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"

/*
 * TABLE ELEMENTS
 */

/*
 * Allocate a new element with key v[3]
 * - set nelems to 0.
 */
static gmap_elem_t *new_gmap_elem(const bvar_t v[3]) {
  gmap_elem_t *e;
  uint32_t n;

  n = GMAP_ELEM_DEF_SIZE;
  assert(n <= GMAP_ELEM_MAX_SIZE);
  e = (gmap_elem_t *) safe_malloc(sizeof(gmap_elem_t) + n * sizeof(gmap_entry_t));
  e->var[0] = v[0];
  e->var[1] = v[1];
  e->var[2] = v[2];
  e->size = n;
  e->nelems = 0;

  return e;
}

/*
 * Increase the size of e and return the new element
 */
static gmap_elem_t *extend_gmap_elem(gmap_elem_t *e) {
  uint32_t n;

  n = e->size;
  if (n == GMAP_ELEM_MAX_SIZE) {
    out_of_memory();
  }

  // increase the size by roughly 50%
  n += (n >> 1) + 2;
  if (n > GMAP_ELEM_MAX_SIZE) {
    n = GMAP_ELEM_MAX_SIZE;
  }

  e = safe_realloc(e, sizeof(gmap_elem_t) + n * sizeof(gmap_entry_t));
  e->size = n;

  return e;
}

/*
 * Add pair <ttbl, l> to element e:
 * - return a pointer to the result
 */
static gmap_elem_t *gmap_elem_add(gmap_elem_t *e, uint32_t ttbl, literal_t l) {
  uint32_t i;

  i = e->nelems;
  if (i == e->size) {
    e = extend_gmap_elem(e);
  }
  assert(i < e->size);
  e->data[i].ttbl = ttbl;
  e->data[i].lit = l;
  e->nelems = i+1;

  return e;
}


/*
 * Search for a pair <tt, lit> such that tt matches ttbl.
 * - return the corresponding literal is such a pair is found in e
 * - return null_literal otherwise.
 *
 * A pair <tt, lit> matches b either if tt == ttbl or tt == ~ttbl.
 * In the first case, the matching literal is lit. In the other
 * case, the matching literal is not(lit).
 */
static literal_t gmap_elem_find_ttbl(gmap_elem_t *e, uint32_t ttbl) {
  uint32_t i, n;
  uint32_t flipped;

  flipped = (~ttbl) & 0xff;

  n = e->nelems;
  for (i=0; i<n; i++) {
    if (e->data[i].ttbl == ttbl) return e->data[i].lit;
    if (e->data[i].ttbl == flipped) return not(e->data[i].lit);
  }
  return null_literal;
}



/*
 * HASH TABLE
 */

/*
 * For debugging: check whether n is 0 or a power of 2
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif

/*
 * Hash a key: array of 4 variables
 * The key must be normalized as follows:
 * - 2 element key: var[0] < var[1], var[2] = null_bvar
 * - 3 element key: var[0] < var[1] < var[2]
 */
static uint32_t hash_gmap_key(const bvar_t var[3]) {
  return jenkins_hash_triple(var[0], var[1], var[2], 0xd33421da);
}

/*
 * Check equality between two keys: v and u
 */
static bool equal_gmap_keys(const bvar_t v[3], const bvar_t u[3]) {
  return v[0] == u[0] && v[1] == u[1] && v[2] == u[2];
}



/*
 * Initialization:
 * - n: initial size. Must be 0 or a power of 2.
 * - if n is 0, the default is used.
 */
void init_gmap(gmap_t *gmap, uint32_t n) {
  gmap_elem_t **tmp;
  uint32_t i;

  if (n == 0) {
    n = GMAP_DEF_SIZE;
  }
  if (n > GMAP_MAX_SIZE) {
    out_of_memory();
  }
  assert(is_power_of_two(n));

  tmp = (gmap_elem_t **) safe_malloc(n * sizeof(gmap_elem_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  gmap->data = tmp;
  gmap->size = n;
  gmap->nelems = 0;
  gmap->resize_threshold = (uint32_t) (GMAP_RESIZE_RATIO * n);
}

/*
 * Delete: free memory
 */
void delete_gmap(gmap_t *gmap) {
  uint32_t i, n;
  gmap_elem_t *e;

  n = gmap->size;
  for (i=0; i<n; i++) {
    e = gmap->data[i];
    if (e != NULL) safe_free(e);
  }
  safe_free(gmap->data);
  gmap->data = NULL;
}


/*
 * Reset: empty the table
 */
void reset_gmap(gmap_t *gmap) {
  uint32_t i, n;
  gmap_elem_t *e;

  n = gmap->size;
  for (i=0; i<n; i++) {
    e = gmap->data[i];
    if (e != NULL) {
      safe_free(e);
      gmap->data[i] = NULL;
    }
  }
  gmap->nelems = 0;
}


/*
 * Clean copy: store e into array a
 * - a's size must be a power of two and mask = this size - 1.
 * - a must have room (some elements are NULL)
 */
static void gmap_clean_copy(gmap_elem_t **a, gmap_elem_t *e, uint32_t mask) {
  uint32_t i;

  i = hash_gmap_key(e->var) & mask;
  while (a[i] != NULL) {
    i ++;
    i &= mask;
  }
  a[i] = e;
}

/*
 * Double the size of the hash table and keep its content
 */
static void extend_gmap(gmap_t *gmap) {
  uint32_t i, n, new_n, mask;
  gmap_elem_t **tmp;
  gmap_elem_t *e;

  assert(is_power_of_two(gmap->size));

  n = gmap->size;
  new_n = 2 * n;
  if (new_n > GMAP_MAX_SIZE) {
    out_of_memory();
  }

  tmp = (gmap_elem_t **) safe_malloc(new_n * sizeof(gmap_elem_t *));
  for (i=0; i<new_n; i++) {
    tmp[i] = NULL;
  }

  assert(is_power_of_two(new_n));
  mask = new_n - 1;
  for (i=0; i<n; i++) {
    e = gmap->data[i];
    if (e != NULL) {
      gmap_clean_copy(tmp, e, mask);
    }
  }

  safe_free(gmap->data);

  gmap->data = tmp;
  gmap->size = new_n;
  gmap->resize_threshold = (uint32_t) (GMAP_RESIZE_RATIO * new_n);  
}


/*
 * Search for an entry that matches v and ttbl.
 * Return the corresponding literal if such an entry exists.
 * Return null_literal otherwise.
 */
static literal_t gmap_find_match(const gmap_t *gmap, const bvar_t v[3], uint32_t ttbl) {
  uint32_t i, mask;
  gmap_elem_t *e;

  assert(gmap->nelems < gmap->size && is_power_of_two(gmap->size));

  mask = gmap->size - 1;
  i = hash_gmap_key(v) & mask;
  for (;;) {
    e = gmap->data[i];
    if (e == NULL) {
      return null_literal;
    }
    if (equal_gmap_keys(e->var, v)) {
      return gmap_elem_find_ttbl(e, ttbl);
    }
    i ++;
    i &= mask;
  }
}


/*
 * Search for an entry that matches v and ttbl.
 * Return the corresponding liteeral is such an entry exists.
 * Otherwiw, add a new entry (v, ttbl) mapped to l and return l.
 */
static literal_t gmap_get_match(gmap_t *gmap, const bvar_t v[3], uint32_t ttbl, literal_t l) {
  uint32_t i, mask;
  literal_t l0;
  gmap_elem_t *e;

  assert(gmap->nelems < gmap->size && is_power_of_two(gmap->size));

  mask = gmap->size - 1;
  i = hash_gmap_key(v) & mask;
  for (;;) {
    e = gmap->data[i];
    if (e == NULL) goto add_fresh;
    if (equal_gmap_keys(e->var, v)) goto found;
    i ++;
    i &= mask;
  }

  // Found a maching element at index i
  // Search for a matching ttbl in e.
  // If nothing found, add the pair (tbbl, l) to e
 found:
  assert(gmap->data[i] == e && equal_gmap_keys(e->var, v));
  l0 = gmap_elem_find_ttbl(e, ttbl);
  if (l0 == null_literal) {
    e = gmap_elem_add(e, ttbl, l);
    gmap->data[i] = e;
    l0 = l;
  }
  return l0;

  // No matching element found.
  // add a new element at index i
 add_fresh:
  assert(gmap->data[i] == NULL);
  e = new_gmap_elem(v);
  e = gmap_elem_add(e, ttbl, l);
  gmap->data[i] = e;
  gmap->nelems ++;
  if (gmap->nelems > gmap->resize_threshold) {
    extend_gmap(gmap);
  }

  return l;
}


/*
 * Search for a gate g and return the literal mapped to g.
 * If g is not in the table, return null_literal.
 */
literal_t gmap_find(const gmap_t *gmap, const bgate_t *g) {
  return gmap_find_match(gmap, g->var, g->ttbl);
}

/*
 * Search for a gate g and return the literal mappd to g.
 * If g is not in the table and the gate and map it o l then return l/
 */
literal_t gmap_get(gmap_t *gmap, const bgate_t *g, literal_t l) {
  return gmap_get_match(gmap, g->var, g->ttbl, l);
}

/*
 * Search for an entry that  matches a truth-table tt
 */
literal_t gmap_find_ttbl(const gmap_t *gmap, const ttbl_t *tt) {
  return gmap_find_match(gmap, tt->label, tt->mask);
}

/*
 * Search for an entry that  matches a truth-table tt.
 * If not found add an entry based on tt and return l.
 */
literal_t gmap_get_ttbl(gmap_t *gmap, const ttbl_t *tt, literal_t l) {
  return gmap_get_match(gmap, tt->label, tt->mask, l);
}

