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
 * EXPERIMENTAL
 */

#ifndef __BDDS_H
#define __BDDS_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "solvers/cdcl/smt_core_base_types.h"

/*
 * BDD node:
 * - var = a Boolean variable in the core
 * - left/right: two BDD ids
 * - map = literal representing this BDD (or null_literal)
 *
 * A bdd id is an integer with the usual one bit polarity:
 * - pos_bdd(i) = 2i
 * - neg_bdd(u) = 2i + 1
 * - where i is a node index
 *
 * The special index 0 denotes the leaf node "true"
 * So pos_bdd(0) = true_bdd = 0 and neg_bdd(0) = false_bdd = 1.
 */
typedef uint32_t bdd_t;
typedef uint32_t bdd_node_t;

typedef struct bnode_s {
  bvar_t var;
  bdd_t left, right;
  literal_t map;
} bnode_t;


/*
 * Cache: for binary operations
 * - maps pairs of bdd ids <x, y> to result
 */
typedef struct {
  bdd_t x, y;
  bdd_t result;
} cache_record_t;


typedef struct {
  cache_record_t *records;
  uint32_t size;
  uint32_t misses;
  uint32_t hits;
} bdd_cache_t;


/*
 * Size
 */
#define DEF_BDD_CACHE_SIZE 64
#define MAX_BDD_CACHE_SIZE (UINT32_MAX/sizeof(cache_record_t))

/*
 * Parameters that control resizing
 * 1) if cache_size < SMALL_THRESHOLD: double the size on any collision
 * 2) if cache_size >= RESIZE_LIMIT: never resize
 * 3) otherwise: resize if hit ratio >= 30& (collisions)
 * 4) cache->size * RESIZE_LOOK_UP_THRESHOLD = number of collisions
 *    before we consider resizing
 */
#define CACHE_RESIZE_SMALL_THRESHOLD 256
#define CACHE_RESIZE_LIMIT (1<<16)
#define CACHE_RESIZE_MINHIT_RATIO 0.3
#define CACHE_RESIZE_LOOKUP_THRESHOLD 0.9


/*
 * Node table for hash consing and construction of BDDs
 * - data = array of nodes
 * - size = size of the data array
 * - nelems = number of nodes in the array data
 *
 * - hash = hash table (maps hash_code for a node to its index in the data array)
 * - hash_size = size of the hash array (a power of two)
 * - threshold to trigger resize of the hash array
 *
 * - map = hash table to map boolean variables to node id:
 *   we ensure map[x] = id => node id is mapped to either pos_lit(x) or neg_lit(x)
 * - map_size = size of map (a power of two)
 * - map_entries = number of elements in the map
 * - threshold to trigger resize of the map array
 *
 * - caches for or and xor
 */
typedef struct bdd_table_s {
  bnode_t *data;
  uint32_t size;
  uint32_t nelems;
  uint32_t *hash;
  uint32_t hash_size;
  uint32_t resize_threshold;
  uint32_t *map;
  uint32_t map_size;
  uint32_t map_entries;
  uint32_t map_threshold;
  bdd_cache_t or_cache;
  bdd_cache_t xor_cache;
} bdd_table_t;

/*
 * Default and nax sizes
 */
#define BDD_TABLE_DEF_SIZE 1024
#define BDD_TABLE_MAX_SIZE (UINT32_MAX/sizeof(bnode_t))

#define BDD_HASH_DEF_SIZE 1024
#define BDD_HASH_MAX_SIZE (UINT32_MAX/sizeof(uint32_t))

#define BDD_MAP_DEF_SIZE 1024
#define BDD_MAP_MAX_SIZE (UINT32_MAX/sizeof(uint32_t))

/*
 * Resize ratio for the hash tables
 */
#define BDD_RESIZE_RATIO 0.7

/*
 * Initialization:
 * - create an empty table with default size
 */
extern void init_bdd_table(bdd_table_t *table);

/*
 * Delete: free memory
 */
extern void delete_bdd_table(bdd_table_t *table);

/*
 * Reset: empty the table
 */
extern void reset_bdd_table(bdd_table_t *table);

/*
 * Constants
 */
enum constant_bdds {
  true_bdd = 0,
  false_bdd = 1,
  null_bdd = UINT32_MAX
};


/*
 * Operations on bdd ids:
 */
static inline bdd_t pos_bdd(bdd_node_t i) {
  return i << 1;
}

static inline bdd_t neg_bdd(bdd_node_t i) {
  return (i << 1) | 1;
}

static inline bdd_t mk_bdd(bdd_node_t i, uint32_t polarity) {
  assert(polarity <= 1);
  return (i << 1) | polarity;
}

static inline bdd_node_t node_of_bdd(bdd_t x) {
  return x>>1;
}

static inline uint32_t polarity_of_bdd(bdd_t x) {
  return x & 1;
}

static inline  bool is_pos_bdd(bdd_t x) {
  return (x >> 1) == 0;
}

static inline bool is_neg_bdd(bdd_t x) {
  return (x >> 1) == 1;
}

static inline bool is_true_bdd(bdd_t x) {
  return x == true_bdd;
}

static inline bool is_false_bdd(bdd_t x) {
  return x == false_bdd;
}

static inline bool is_null_bdd(bdd_t x) {
  return x == null_bdd;
}

static inline bdd_t not_bdd(bdd_t x) {
  return x ^ 1;
}


/*
 * MAP literal -> bdds
 */

/*
 * Get the literal mapped to bdd i:
 * - return null_literal if nothing is mapped
 */
extern literal_t get_bdd_map(bdd_table_t *table, bdd_t i);

/*
 * Attach literal l to bdd i
 * - there must not be am existing literal for this bdd
 */
extern void set_bdd_map(bdd_table_t *table, bdd_t i, literal_t l);

/*
 * Find a bdd that maps to literal l
 * - return null_bdd if there's no such bdd
 */
extern bdd_t bdd_for_literal(bdd_table_t *table, literal_t l);


/*
 * BDD Construction and Function simplification
 */

/*
 * Get the bdd (ite x left right):
 * - normalize to ensure that left has positive polarity
 * - create a new node if this node is not present in table
 * - return the bdd id
 */
extern bdd_t mk_bdd_node(bdd_table_t *table, bvar_t x, bdd_t left, bdd_t right);

/*
 * Create a bdd node to represent literal l:
 * - this creates the bdd (ite x true false) where x = var_of(l)
 *   and stores the entry [x -> bdd] in the internal map.
 * - if there's already a node mapped to x, return it.
 */
extern bdd_t mk_bdd_for_literal(bdd_table_t *table, literal_t l);

/*
 * Create a bdd node to represent (ite c a b)
 * - this creates the bdd (ite x bdd_for(a) bdd_for(b))
 *   where x = var_of(c).
 * - if there's already such a bdd, return it.
 */
extern bdd_t mk_bdd_for_ite(bdd_table_t *table, literal_t c, literal_t a, literal_t b);

/*
 * Create a bdd node for (xor a b)
 * - return null_bdd if that's too expensive
 */
extern bdd_t mk_bdd_for_xor(bdd_table_t *table, literal_t a, literal_t b);

/*
 * Create a bdd node for (or a b)
 * - return null_bdd if that's too expensive
 */
extern bdd_t mk_bdd_for_or(bdd_table_t *table, literal_t a, literal_t b);

/*
 * Simplifications with bdds
 * - these functions try to simplify a Boolean function f(x, y)
 *   using the internal bdds
 * - they return null_literal if f(x, y) does not simplify
 *   or some literal l if the BDD table can show that f(x, y) = l
 */
extern literal_t bdd_xor_simplify(bdd_table_t *table, bdd_t x, bdd_t y);
extern literal_t bdd_or_simplify (bdd_table_t *table, bdd_t x, bdd_t y);
extern literal_t bdd_ite_simplify(bdd_table_t *table, literal_t c, bdd_t x, bdd_t y); // (ite c x y)


#endif /** __BDDS_H */
