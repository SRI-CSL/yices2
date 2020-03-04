/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2018 SRI International.
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
 * EXPERIMENTAL: HASH TABLE FOR BOOLEAN GATES
 */

#include <assert.h>

#include "solvers/cdcl/new_gate_hash_map.h"
#include "utils/bit_tricks.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"


/*
 * For debugging: check whether n is 0 or a power of 2
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Check whether two gates are equal
 */
static bool equal_gates(const bgate_t *g1, const bgate_t *g2) {
  return g1->ttbl == g2->ttbl && g1->var[0] == g2->var[0] &&
    g1->var[1] == g2->var[1] && g1->var[2] == g2->var[2];
}

/*
 * Hash code for a gate
 */
static uint32_t hash_bgate(const bgate_t *g) {
  return jenkins_hash_quad(g->ttbl, g->var[0], g->var[1], g->var[2], 0xae01781a);
}

/*
 * Check whether an entry k in the key table is used
 */
static inline bool key_is_live(const bgate_t *k) {
  return k->ttbl < 256;
}

static inline bool key_is_dead(const bgate_t *k) {
  return k->ttbl >= 256;
}


/*
 * Initialization:
 * - n: initial size. Must be 0 or a power of 2.
 * - if n is 0, the default is used.
 */
void init_gate_hmap(gate_hmap_t *hmap, uint32_t n) {
  bgate_t *keys;
  uint32_t i;

  if (n == 0) {
    n = GATE_HMAP_DEF_SIZE;
  }
  if (n > GATE_HMAP_MAX_SIZE) {
    out_of_memory();
  }
  assert(is_power_of_two(n));

  // key[i] is marked as not used
  // val[i] is not initialized

  keys = (bgate_t *) safe_malloc(n * sizeof(bgate_t));
  for (i=0; i<n; i++) {
    keys[i].ttbl = 256;
  }

  hmap->key = keys;
  hmap->value = (literal_t *) safe_malloc(n * sizeof(literal_t));
  hmap->size = n;
  hmap->nelems = 0;
  hmap->resize_threshold = (uint32_t) (GATE_HMAP_RESIZE_RATIO * n);
}


/*
 * Delete: free memory
 */
void delete_gate_hmap(gate_hmap_t *hmap) {
  safe_free(hmap->key);
  safe_free(hmap->value);
  hmap->key = NULL;
  hmap->value = NULL;
}

/*
 * Empty the table
 */
void reset_gate_hmap(gate_hmap_t *hmap) {
  uint32_t i, n;

  n = hmap->size;
  for (i=0; i<n; i++) {
    hmap->key[i].ttbl = 256;
  }
  hmap->nelems = 0;
}

/*
 * Find a slot for k in array a
 * - mask = size of a - 1 (the size is a power of 2)
 * - copy k at some position i in a and return i
 */
static uint32_t gate_hmap_clean_copy(bgate_t *a, const bgate_t *k, uint32_t mask) {
  uint32_t i;

  i = hash_bgate(k) & mask;
  while (key_is_live(a + i)) {
    i ++;
    i &= mask;
  }
  a[i] = *k;

  return i;
}

/*
 * Make the table twice as large
 */
static void extend_gate_hmap(gate_hmap_t *hmap) {
  bgate_t *keys;
  literal_t *values;
  uint32_t n, i, j, n2, mask;
  
  n = hmap->size;
  n2 = n << 1;
  if (n2 > GATE_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n2));

  // new key & value arrays
  keys = (bgate_t *) safe_malloc(n2 * sizeof(bgate_t));
  values = (literal_t *) safe_malloc(n2 * sizeof(literal_t));
  for (i=0; i<n2; i++) {
    keys[i].ttbl = 256;
  }

  // copy the entries
  mask = n2 - 1;
  for (i=0; i<n; i++) {
    if (key_is_live(hmap->key + i)) {
      j = gate_hmap_clean_copy(keys, hmap->key + i, mask);
      values[j] = hmap->value[i];
    }
  }

  safe_free(hmap->key);
  safe_free(hmap->value);
  hmap->key = keys;
  hmap->value = values;
  hmap->size = n2;
  hmap->resize_threshold = (uint32_t) (GATE_HMAP_RESIZE_RATIO * n2);
}

/*
 * Two gates g1 and g2 may be complement of each other:
 * - they have the same variables x, y, z but complementary table,.
 * - this means that g1(x, y, z) == NOT g2(x, y, z)
 *
 * The mapping: l = g1(x, y, z) is then equivalent to ~l = g2(x, y, z).
 * We normalize the keys to ensure that there's only one key in
 * this case (either g1 or g2). Let b = g1->ttbl then g2->ttbl = ~b:
 *
 * The normal form is either b or ~b:
 * - we pick the one that has more bits set to '1'
 * - if b and ~b have four bits set to '1' then we pick the one
 *   that has '0' has lower bit.
 *
 * The following function returns true if b must be negated (i.e., the
 * normal form is ~b):
 */
static inline bool flip_gate(uint32_t b) {
  uint32_t n;

  n = popcount32(b);
  assert(0 <= n && n <= 8);
  return n < 4 || (n == 4 && ((b & 1) == 1));
}


/*
 * Search for key k: assumes the key is normalized.
 * - polarity is either 0 or 1.
 * - if k is mapped to some l then we return either l or not(l) depending
 *   on polarity.
 */
static literal_t gate_hmap_find_key(const gate_hmap_t *hmap, const bgate_t *k, int32_t polarity) {
  uint32_t i, mask;
  literal_t l;

  assert(is_power_of_two(hmap->size) && hmap->nelems < hmap->size);

  l = null_literal;
  mask = hmap->size - 1;
  i = hash_bgate(k) & mask;
  for (;;) {
    if (key_is_dead(hmap->key + i)) break;
    if (equal_gates(k, hmap->key + i)) {
      l = hmap->value[i] ^ polarity;
      assert(l != null_literal);
      break;
    }
    i ++;
    i &= mask;
  }

  return l;
}


/*
 * Search for a gate g and return the literal mapped to g.
 * If g is not in the table, return null_literal.
 */
literal_t gate_hmap_find(const gate_hmap_t *hmap, const bgate_t *g) {
  bgate_t key;
  int32_t polarity;

  key = *g;
  polarity = 0;
  if (flip_gate(key.ttbl)) {
    key.ttbl = (~key.ttbl) & 0xff;
    polarity = 1;
  }
  return gate_hmap_find_key(hmap, &key, polarity);  
}


/*
 * Search for a gate that matches ttbl
 */
literal_t gate_hmap_find_ttbl(const gate_hmap_t *hmap, const ttbl_t *tt) {
  bgate_t key;
  int32_t polarity;

  if (flip_gate(tt->mask)) {
    key.ttbl = (~tt->mask) & 0xff;
    polarity = 1;
  } else {
    key.ttbl = tt->mask;
    polarity = 0;
  }
  key.var[0] = tt->label[0];
  key.var[1] = tt->label[1];
  key.var[2] = tt->label[2];

  return gate_hmap_find_key(hmap, &key, polarity);
}



/*
 * Add pair (key, l) to the map.
 * - key is normalized
 */
static void gate_hmap_add_entry(gate_hmap_t *hmap, const bgate_t *k, literal_t l) {
  uint32_t i, mask;

  assert(is_power_of_two(hmap->size) && hmap->nelems < hmap->size);

  mask = hmap->size - 1;
  i = hash_bgate(k) & mask;
  while (key_is_live(hmap->key + i)) {
    i ++;
    i &= mask;
  }

  hmap->key[i] = *k;
  hmap->value[i] = l;
  hmap->nelems ++;
  if (hmap->nelems > hmap->resize_threshold) {
    extend_gate_hmap(hmap);
  }
}


/*
 * Add an entry to the map: the key is g, the value is l.
 * The key g must not be present in hmap.
 */
void gate_hmap_add(gate_hmap_t *hmap, const bgate_t *g, literal_t l) {
  bgate_t key;

  key = *g;
  if (flip_gate(key.ttbl)) {
    key.ttbl = (~key.ttbl) & 0xff;
    l = not(l);
  }
  gate_hmap_add_entry(hmap, &key, l);
}


void gate_hmap_add_ttbl(gate_hmap_t *hmap, const ttbl_t *tt, literal_t l) {
  bgate_t key;

  if (flip_gate(tt->mask)) {
    key.ttbl = (~tt->mask) & 0xff;
    l = not(l);
  } else {
    key.ttbl = tt->mask;
  }
  key.var[0] = tt->label[0];
  key.var[1] = tt->label[1];
  key.var[2] = tt->label[2];

  gate_hmap_add_entry(hmap, &key, l);
}


/*
 * First valid gate/literal starting from index i
 * - return hmap->size if there's no more gate
 */
static uint32_t gate_hmap_get_next(const gate_hmap_t *hmap, uint32_t i) {
  uint32_t n;

  n = hmap->size;
  while (i < n) {
    if (key_is_live(hmap->key + i)) break;
    i ++;
  }
  return i;
}

/*
 * First gate in the table (or NULL if the table is empty)
 */
bgate_t *gate_hmap_first_gate(const gate_hmap_t *hmap, literal_t *lit) {
  uint32_t i;

  i = gate_hmap_get_next(hmap, 0);
  if (i < hmap->size) {
    *lit = hmap->value[i];
    return hmap->key + i;
  }
  return NULL;
}

/*
 * Gate that follows *g or NULL if there's no such gate
 */
bgate_t *gate_hmap_next_gate(const gate_hmap_t *hmap, const bgate_t *g, literal_t *lit) {
  uint32_t i;

  i = g - hmap->key;
  assert(i < hmap->size);
  i = gate_hmap_get_next(hmap, i+1);
  if (i < hmap->size) {
    *lit = hmap->value[i];
    return hmap->key + i;
  }
  return NULL;
}
