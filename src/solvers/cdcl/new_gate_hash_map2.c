
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
 * Allocate a new element with key v[4]
 * - set nelems to 0.
 */
static gmap_elem_t *new_gmap_elem(const bvar_t v[4]) {
  gmap_elem_t *e;
  uint32_t n;

  n = GMAP_ELEM_DEF_SIZE;
  assert(n <= GMAP_ELEM_MAX_SIZE);
  e = (gmap_elem_t *) safe_malloc(sizeof(gmap_elem_t) + n * sizeof(gmap_entry_t));
  e->var[0] = v[0];
  e->var[1] = v[1];
  e->var[2] = v[2];
  e->var[3] = v[3];
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

  // 16bits are relevant
  flipped = (~ttbl) & 0xffff;

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
 * - 2 element key: var[0] < var[1], var[2] = var[3] = null_bvar
 * - 3 element key: var[0] < var[1] < var[2], var[3] = null_bvar
 * - 4 element key: var[0] < var[1] < var[2] < var[3]
 */
static uint32_t hash_gmap_key(const bvar_t var[4]) {
  return jenkins_hash_quad(var[0], var[1], var[2], var[3], 0xd33421da);
}

/*
 * Check equality between two keys: v and u
 */
static bool equal_gmap_keys(const bvar_t v[4], const bvar_t u[4]) {
  return v[0] == u[0] && v[1] == u[1] && v[2] == u[2]  && v[3] == u[3];
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
static literal_t gmap_find_match(const gmap_t *gmap, const bvar_t v[4], uint32_t ttbl) {
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
 * Otherwise, add a new entry (v, ttbl) mapped to l and return l.
 */
static literal_t gmap_get_match(gmap_t *gmap, const bvar_t v[4], uint32_t ttbl, literal_t l) {
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
 * Convert and 8-bit truth table (as in truth-tables.h) to 16-bit
 * The 8-bit looks like this [ b7 b6 b5 b4 b3 b2 b1 b0 ] (where b0 = low-order bit of u)
 * This is converted to [ b7 b7 b6 b6 b5 b5 b4 b4 b3 b3 b2 b2 b1 b1 b0 b0 ]
 *
 * We use a conversion table for a block of four bits:
 * for an index i = [ b3 b2 b1 b0 ] the convert4[i] = [ b3 b3 b2 b2 b1 b1 b0 b0 ]
 */
static const uint32_t convert4[16] = {
  0x00, 0x03, 0x0c, 0x0f,
  0x30, 0x33, 0x3c, 0x3f,
  0xc0, 0xc3, 0xcc, 0xcf,
  0xf0, 0xf3, 0xfc, 0xff
};

static uint32_t convert_ttbl(uint8_t u) {
  return convert4[u & 0x0f] | (convert4[u >> 4] << 8);
}

/*
 * Copy variables of u into v[4] and set v[3] to null_bvar
 */
static void convert_vars(bvar_t v[4], const bvar_t u[3]) {
  v[0] = u[0];
  v[1] = u[1];
  v[2] = u[2];
  v[3] = null_bvar;
}

/*
 * Find/get for a three-var function
 */
static literal_t gmap_find_match3(const gmap_t *gmap, const bvar_t u[3], uint8_t stbl) {
  bvar_t v[4];
  uint32_t ttbl;

  convert_vars(v, u);
  ttbl = convert_ttbl(stbl);
  return gmap_find_match(gmap, v, ttbl);
}

static literal_t gmap_get_match3(gmap_t *gmap, const bvar_t u[3], uint8_t stbl, literal_t l) {
  bvar_t v[4];
  uint32_t ttbl;

  convert_vars(v, u);
  ttbl = convert_ttbl(stbl);
  return gmap_get_match(gmap, v, ttbl, l);
}


/*
 * Search for a gate g and return the literal mapped to g.
 * If g is not in the table, return null_literal.
 */
literal_t gmap_find(const gmap_t *gmap, const bgate_t *g) {
  return gmap_find_match3(gmap, g->var, g->ttbl);
}

/*
 * Search for a gate g and return the literal mappd to g.
 * If g is not in the table and the gate and map it o l then return l/
 */
literal_t gmap_get(gmap_t *gmap, const bgate_t *g, literal_t l) {
  return gmap_get_match3(gmap, g->var, g->ttbl, l);
}

/*
 * Search for an entry that  matches a truth-table tt
 */
literal_t gmap_find_ttbl(const gmap_t *gmap, const ttbl_t *tt) {
  return gmap_find_match3(gmap, tt->label, tt->mask);
}

/*
 * Search for an entry that  matches a truth-table tt.
 * If not found add an entry based on tt and return l.
 */
literal_t gmap_get_ttbl(gmap_t *gmap, const ttbl_t *tt, literal_t l) {
  return gmap_get_match3(gmap, tt->label, tt->mask, l);
}


#ifndef NDEBUG
/*
 * Check that all elements in w->val are 0 or 1
 */
static bool good_wide_ttbl_values(const wide_ttbl_t *w) {
  uint32_t i, n;

  assert(w->nvars < 32);
  n = ((uint32_t) 1) << w->nvars; // 2^nvars
  for (i=0; i<n; i++) {
    if (w->val[i] != 0 && w->val[i] != 1) return false;
  }
  return true;
}
#endif

/*
 * Multiply m by bit
 * - return 0 if bit == 0 or mask if bit == 1
 */
static inline uint32_t mask(uint32_t m, uint8_t bit) {
  assert(bit == 0 || bit == 1);
  return  m & (- (uint32_t) bit);
}


/*
 * Convert a wide truth table w to key/ttbl
 * - store four variables in v[0 ... v3] (copied from w->var)
 * - return a 16bit encoding of w->val as ttbl
 * - w must not have more than four variables
 *
 * Warning: if w stores a table for f(x0, .., x3) then
 * the value of f(b0, b1, b2, b3) is stored in w->val[i]
 * where i = b0 + 2 b1 + 4 b2 + 8 b3.
 * In the gmap, we store the same value in bit j of the ttbl
 * where j = 8 b0 + 4 b1 + 2 b2 + b3.
 */
static uint32_t convert_wide_ttbl(bvar_t v[4], const wide_ttbl_t *w) {
  uint32_t ttbl;

  assert(good_wide_ttbl_values(w));

  switch (w->nvars) {
  case 0:
    v[0] = null_bvar;
    v[1] = null_bvar;
    v[2] = null_bvar;
    v[3] = null_bvar;
    ttbl = mask(0xFFFF, w->val[0]);
    break;

  case 1:
    v[0] = w->var[0];
    v[1] = null_bvar;
    v[2] = null_bvar;
    v[3] = null_bvar;
    ttbl = mask(0x00FF, w->val[0]) | mask(0xFF00, w->val[1]);
    break;

  case 2:
    v[0] = w->var[0];
    v[1] = w->var[1];
    v[2] = null_bvar;
    v[3] = null_bvar;
    ttbl = mask(0x000F, w->val[0]) | mask(0x00F0, w->val[2])
      | mask(0x0F00, w->val[1]) | mask(0xF000, w->val[3]);
    break;

  case 3:
    v[0] = w->var[0];
    v[1] = w->var[1];
    v[2] = w->var[2];
    v[3] = null_bvar;
    ttbl = mask(0x0003, w->val[0]) | mask(0x000C, w->val[4])
      | mask(0x0030, w->val[2]) | mask(0x00C0, w->val[6])
      | mask(0x0300, w->val[1]) | mask(0x0C00, w->val[5])
      | mask(0x3000, w->val[3]) | mask(0xC000, w->val[7]);
    break;

  default:
    assert(w->nvars == 4);
    v[0] = w->var[0];
    v[1] = w->var[1];
    v[2] = w->var[2];
    v[3] = w->var[3];
    ttbl = mask(0x0001, w->val[0]) | mask(0x0002, w->val[8])
      | mask(0x0004, w->val[4]) | mask(0x0008, w->val[12])
      | mask(0x0010, w->val[2]) | mask(0x0020, w->val[10])
      | mask(0x0040, w->val[6]) | mask(0x0080, w->val[14])
      | mask(0x0100, w->val[1]) | mask(0x0200, w->val[9])
      | mask(0x0400, w->val[5]) | mask(0x0800, w->val[13])
      | mask(0x1000, w->val[3]) | mask(0x2000, w->val[11])
      | mask(0x4000, w->val[7]) | mask(0x8000, w->val[15]);
    break;
  }

  return ttbl;
}

/*
 * Search using a wide truth table
 * - w must be normalized and have no more than four variables
 */
literal_t gmap_find_wide_ttbl(const gmap_t *gmap, const wide_ttbl_t *w) {
  bvar_t v[4];
  uint32_t ttbl;

  ttbl = convert_wide_ttbl(v, w);
  return gmap_find_match(gmap, v, ttbl);
}

literal_t gmap_get_wide_ttbl(gmap_t *gmap, const wide_ttbl_t *w, literal_t l) {
  bvar_t v[4];
  uint32_t ttbl;

  ttbl = convert_wide_ttbl(v, w);
  return gmap_get_match(gmap, v, ttbl, l);
}
