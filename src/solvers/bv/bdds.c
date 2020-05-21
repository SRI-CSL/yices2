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

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>

#include "solvers/bv/bdds.h"
#include "utils/memalloc.h"
#include "utils/hash_functions.h"

#ifndef NDEBUG
/*
 * For debugging: check whether n is 0 or a power of 2
 */
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}

/*
 * Check that a node_id is within bounds for table
 */
static bool good_bdd_node(const bdd_table_t *table, bdd_node_t i) {
  return i < table->nelems;
}

static bool good_bdd(const bdd_table_t *table, bdd_t i) {
  return good_bdd_node(table, node_of_bdd(i));
}

#endif


/************
 *  CACHES  *
 ***********/

/*
 * Initialize cache of size n
 */
static void init_bdd_cache(bdd_cache_t *cache) {
  cache_record_t *tmp;
  uint32_t i, n;

  n = DEF_BDD_CACHE_SIZE;

  assert(n <= MAX_BDD_CACHE_SIZE);
  assert(is_power_of_two(n));

  tmp = (cache_record_t *) safe_malloc(n * sizeof(cache_record_t));
  for (i=0; i<n; i++) {
    tmp[i].x = null_bdd;
  }

  cache->records = tmp;
  cache->size = n;
  cache->misses = 0;
  cache->hits = 0;
}


/*
 * Delete cache
 */
static void delete_bdd_cache(bdd_cache_t *cache) {
  safe_free(cache->records);
  cache->records = NULL;
}


/*
 * Empty
 */
static void reset_bdd_cache(bdd_cache_t *cache) {
  delete_bdd_cache(cache);
  init_bdd_cache(cache);
}

/*
 * Hash of a pair of bdd-ids x, y
 */
static inline uint32_t hash_bdd_pair(bdd_t x, bdd_t y) {
  return jenkins_hash_pair((int32_t) x, (int32_t) y, 0x8328dae7);
}


/*
 * Find what's mapped to pair <x, y> in cache.
 * - x (and y) must be different from NULL_BDD_NODE.
 * Return null_bdd if the pair is not in the cache.
 * Update the hit or miss counters.
 */
static bdd_t cache_find(bdd_cache_t *cache, bdd_t x, bdd_t y) {
  uint32_t h;
  cache_record_t *r;

  h = hash_bdd_pair(x, y) & (cache->size - 1);
  r = cache->records + h;

  if (r->x == x && r->y == y) {
    cache->hits ++;
    return r->result;
  } else {
    cache->misses ++;
    return null_bdd;
  }
}


/*
 * Expand the cache: make it twice as large. Keep the same content.
 */
static void expand_cache(bdd_cache_t *cache) {
  uint32_t i, n, old_n, h, mask;
  cache_record_t *tmp, *ptr;

  old_n = cache->size;
  if (old_n >= MAX_BDD_CACHE_SIZE/2) {
    out_of_memory();
  }
  n = old_n << 1;

  tmp = (cache_record_t *) safe_malloc(n * sizeof(cache_record_t));
  for (i=0; i<n; i++) {
    tmp[i].x = null_bdd;
  }

  mask = n - 1;
  ptr = cache->records;
  for (i=0; i<old_n; i++) {
    if (ptr->x != null_bdd) {
      h = hash_bdd_pair(ptr->x, ptr->y) & mask;
      tmp[h] = *ptr;      
    }
    ptr ++;
  }

  safe_free(cache->records);
  cache->size = n;
  cache->records = tmp;
  // reset hits and misses counters
  cache->hits = 0;
  cache->misses = 0;
}


/*
 * Store mapping from <x, y> to v in cache.
 * - x, y, v must be different from NULL_BDD_NODE.
 */
static void cache_store(bdd_cache_t *cache, bdd_t x, bdd_t y, bdd_t v) {
  uint32_t h, i, lookups;
  cache_record_t *r;
  
  h = hash_bdd_pair(x, y);
  i = h & (cache->size - 1);
  r = cache->records + i;

  if (r->x != null_bdd && cache->size < CACHE_RESIZE_LIMIT) {
    /*
     * This is a collision. Try resizing.
     */
    lookups = cache->hits + cache->misses; // number of lookups since last resize
    if (lookups >= cache->size * CACHE_RESIZE_LOOKUP_THRESHOLD 
	&& (cache->size < CACHE_RESIZE_SMALL_THRESHOLD 
	    || cache->hits > lookups * CACHE_RESIZE_MINHIT_RATIO)) {

      expand_cache(cache);
      i = h & (cache->size - 1);
      r = cache->records + i;
    }
  }
  r->x = x;
  r->y = y;
  r->result = v;
}



/***************
 *  BDD TABLE  *
 **************/

/*
 * Initialization:
 * - create an empty table with default size
 */
void init_bdd_table(bdd_table_t *table) {
  bnode_t *tmp;
  uint32_t *hash;
  uint32_t i, n;

  n = BDD_TABLE_DEF_SIZE;
  tmp = (bnode_t *) safe_malloc(n * sizeof(bnode_t));
  // store the node 0 descriptor for true_bdd
  tmp[0].var = null_bvar;
  tmp[0].left = 0;
  tmp[0].right = 0;
  tmp[0].map = true_literal;

  table->data = tmp;
  table->size = n;
  table->nelems = 1; // one node

  n = BDD_HASH_DEF_SIZE;
  assert(is_power_of_two(n));
  hash = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  for (i=0; i<n; i++) {
    hash[i] = 0;
  }
  table->hash = hash;
  table->hash_size = n;
  table->resize_threshold = (uint32_t) (n * BDD_RESIZE_RATIO);

  n = BDD_MAP_DEF_SIZE;
  assert(is_power_of_two(n));
  hash = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  for (i=0; i<n; i++) {
    hash[i] = 0;
  }
  table->map = hash;
  table->map_size = n;
  table->map_entries = 0;
  table->map_threshold = (uint32_t) (n * BDD_RESIZE_RATIO);

  init_bdd_cache(&table->or_cache);
  init_bdd_cache(&table->xor_cache);
}


/*
 * Delete: free memory
 */
void delete_bdd_table(bdd_table_t *table) {
  safe_free(table->data);
  safe_free(table->hash);
  safe_free(table->map);
  table->data = NULL;
  table->hash = NULL;
  table->map = NULL;
  delete_bdd_cache(&table->or_cache);
  delete_bdd_cache(&table->xor_cache);
}

/*
 * Reset: empty the table
 */
void reset_bdd_table(bdd_table_t *table) {
  uint32_t i, n;

  table->nelems = 1;

  n = table->hash_size;
  for (i=0; i<n; i++) {
    table->hash[i] = 0;
  }
  n = table->map_size;
  for (i=0; i<n; i++) {
    table->map[i] = 0;
  }
  table->map_entries = 0;

  reset_bdd_cache(&table->or_cache);
  reset_bdd_cache(&table->xor_cache);
}


/*
 * Make the node table bigger.
 */
static void extend_bdd_table(bdd_table_t *table) {
  uint32_t n;

  n = table->size;
  n += n>>1;
  if (n > BDD_TABLE_MAX_SIZE) {
    out_of_memory();
  }
  assert(n > table->size);

  table->data = (bnode_t *) safe_realloc(table->data, n * sizeof(bnode_t));
  table->size = n;
}

/*
 * Add node (x, left, right) to the table and return its id
 */
static bdd_node_t add_bdd_node(bdd_table_t *table, bvar_t x, uint32_t left, uint32_t right) {
  bdd_node_t i;

  i = table->nelems;
  if (i == table->size) {
    extend_bdd_table(table);
  }
  assert(i < table->size);
  table->data[i].var = x;
  table->data[i].left = left;
  table->data[i].right = right;
  table->data[i].map = null_literal;
  table->nelems = i + 1;

  return i;
}


/*
 * Hash code for node (x, left, right)
 */
static uint32_t hash_bdd_triple(bvar_t x, uint32_t left, uint32_t right) {
  return jenkins_hash_triple(x, left, right, 0x282ac9ff);
}

static uint32_t hash_bdd_node(const bnode_t *node) {
  return hash_bdd_triple(node->var, node->left, node->right);
}

/*
 * Add index j to array hash:
 * - mask = size of hash - 1 where the size is a power of two
 */
static void add_to_clean_hash(uint32_t *hash, uint32_t mask, uint32_t i, const bnode_t *node) {
  uint32_t j;

  j = hash_bdd_node(node) & mask;
  while (hash[j] != 0) {
    j ++;
    j &= mask;
  }
  hash[j] = i;
}

/*
 * Resize the hash table: double its size
 */
static void resize_bdd_hash_table(bdd_table_t *table) {
  uint32_t i, n, m, mask;
  uint32_t *hash;

  assert(is_power_of_two(table->hash_size));

  m = table->hash_size << 1;
  if (m > BDD_HASH_MAX_SIZE) {
    out_of_memory();
  }
  safe_free(table->hash);

  hash = (uint32_t *) safe_malloc(m * sizeof(uint32_t));
  for (i=0; i<m; i++) {
    hash[i] = 0;
  }

  // add all nodes except 0 to the hash table
  mask = m - 1;
  n = table->nelems;
  for (i=1; i<n; i++) {
    add_to_clean_hash(hash, mask, i, table->data + i);
  }
  
  table->hash = hash;
  table->hash_size = m;
  table->resize_threshold = (uint32_t) (m * BDD_RESIZE_RATIO);
}

/*
 * Check whether node i is equal to (x, left, right)
 */
static bool equal_bdd_node(const bnode_t *node, bvar_t x, uint32_t left, uint32_t right) {
  return node->var == x && node->left == left && node->right == right;
}

/*
 * Search for a node (x, left, right)
 * - return its index if present or 0 otherwise
 */
static bdd_node_t find_bdd_node(bdd_table_t *table, bvar_t x, uint32_t left, uint32_t right) {
  uint32_t i, mask;
  bdd_node_t j;

  assert(is_power_of_two(table->hash_size) && table->nelems + 1 < table->hash_size);

  mask = table->hash_size - 1;
  i = hash_bdd_triple(x, left, right) & mask;
  for (;;) {
    j = table->hash[i];
    if (j == 0 || equal_bdd_node(table->data + j, x, left, right)) break;
    i ++;
    i &= mask;
  }

  return j;
}


/*
 * Search for node (x, left, right). Add it as a new node if it's not present
 */
static bdd_node_t get_bdd_node(bdd_table_t *table, bvar_t x, uint32_t left, uint32_t right) {
  uint32_t i, mask;
  bdd_node_t j;

  assert(is_power_of_two(table->hash_size) && table->nelems + 1 < table->hash_size);

  mask = table->hash_size - 1;
  i = hash_bdd_triple(x, left, right) & mask;
  for (;;) {
    j = table->hash[i];
    if (j == 0) break;
    if (equal_bdd_node(table->data + j, x, left, right)) goto done;
    i ++;
    i &= mask;
  }

  // create and add a new node
  j = add_bdd_node(table, x, left, right);
  table->hash[i] = j;

  if (table->nelems + 1 > table->resize_threshold) {
    resize_bdd_hash_table(table);
  }

 done:
  return j;
}


/*
 * MAP: Boolean var to node id
 */

/*
 * Hash code for a Boolean variable x
 */
static uint32_t hash_bool_var(bvar_t x) {
  return jenkins_hash_int32(x);
}

/*
 * Check whether the literal mapped to node is either pos_lit(x) or neg_lit(x)
 */
static bool node_maps_to_bvar(const bnode_t *node, bvar_t x) {
  return var_of(node->map) == x;
}

/*
 * Search for the node i attached to variable x
 * - return 0 if there's no such node
 */
static bdd_node_t find_mapped_node(bdd_table_t *table, bvar_t x) {
  uint32_t i, mask;
  bdd_node_t j;

  assert(is_power_of_two(table->map_size) && table->map_entries < table->map_size);

  mask = table->map_size - 1;
  i = hash_bool_var(x) & mask;
  for (;;) {
    j = table->map[i];
    if (j == 0 || node_maps_to_bvar(table->data + j, x)) break;
    i ++;
    i &= mask;
  }

  return j;
}

/*
 * Store entry x -> i into array map
 * - mask = size of the array - 1. The size must be a power of two.
 */
static void add_to_clean_map(uint32_t *map, uint32_t mask, bvar_t x, bdd_node_t i) {
  uint32_t j;

  j = hash_bool_var(x) & mask;
  while (map[j] != 0) {
    j ++;
    j &= mask;
  }

  map[j] = i;
}

/*
 * Make the map table larger (double its size)
 */
static void resize_bdd_map(bdd_table_t *table) {
  uint32_t i, n, m, mask;
  literal_t l;
  uint32_t *map;

  m = table->map_size << 1;
  assert(is_power_of_two(m));
  if (m > BDD_MAP_MAX_SIZE) {
    out_of_memory();
  }
  safe_free(table->map);

  map = (uint32_t *) safe_malloc(m * sizeof(uint32_t));
  for (i=0; i<m; i++) {
    map[i] = 0;
  }

  // remap all the nodes
  mask = m -1;
  n = table->nelems;
  for (i=1; i<n; i++) {
    l = table->data[i].map;
    if (l != null_literal) {
      add_to_clean_map(map, mask, var_of(l), i);
    }
  }

  table->map = map;
  table->map_size = m;
  table->map_threshold = (uint32_t) (m * BDD_RESIZE_RATIO);
}


/*
 * Add entry x -> k to the map
 * - don't do anything if there's already a node mapped to x
 */
static void add_node_map_entry(bdd_table_t *table, bvar_t x, bdd_node_t k) {
  uint32_t i, mask;
  bdd_node_t j;

  assert(good_bdd_node(table, k) && node_maps_to_bvar(table->data + k, x));
  assert(is_power_of_two(table->map_size) && table->map_entries < table->map_size);

  mask = table->map_size - 1;
  i = hash_bool_var(x) & mask;
  for (;;) {
    j = table->map[i];
    if (j == 0) break;
    if (node_maps_to_bvar(table->data + j, x)) return; // x -> j in the map
    i ++;
    i &= mask;
  }

  table->map[i] = k;
  table->map_entries ++;
  if (table->map_entries > table->map_threshold) {
    resize_bdd_map(table);
  }
}


/*
 * Get the literal mapped to bdd i:
 * - return null_literal if nothing mapped
 */
literal_t get_bdd_map(bdd_table_t *table, bdd_t i) {
  literal_t l;

  assert(good_bdd(table, i));

  l = table->data[node_of_bdd(i)].map;
  if (l != null_literal) {
    l ^= polarity_of_bdd(i);
  }
  return l;
}


/*
 * Attach literal l to bdd i
 * - there must not be an existing literal for this bdd
 */
void set_bdd_map(bdd_table_t *table, bdd_t i, literal_t l) {
  bdd_node_t j;

  assert(good_bdd(table, i));

  j = node_of_bdd(i);
  l ^= polarity_of_bdd(i);
  table->data[j].map = l;

  add_node_map_entry(table, var_of(l), j);
}


/*
 * Find a bdd that maps to literal l
 * - return null_bdd if there's no such bdd
 */
bdd_t bdd_for_literal(bdd_table_t *table, literal_t l) {
  bdd_node_t i;
  uint32_t polarity;

  if (l == true_literal) return true_bdd;
  if (l == false_literal) return false_bdd;

  i = find_mapped_node(table, var_of(l));
  if (i == 0) return null_bdd; // not in the table

  assert(table->data[i].map == l || table->data[i].map == not(l));
  polarity = table->data[i].map ^ l;
  // polarity 0 means table->data[i].map = l
  // polarity 1 means table->data[i].map = not(l)

  return mk_bdd(i, polarity);
}



/*
 * Access to bdd variable and children
 */
static bvar_t var_of_node(const bdd_table_t *table, bdd_node_t i) {
  assert(good_bdd_node(table, i) && i>0);
  return table->data[i].var;
}

static bdd_t left_of_node(const bdd_table_t *table, bdd_node_t i) {
  assert(good_bdd_node(table, i) && i>0);
  return table->data[i].left;
}

static bdd_t right_of_node(const bdd_table_t *table, bdd_node_t i) {
  assert(good_bdd_node(table, i) && i > 0);
  return table->data[i].right;
}

static bvar_t var_of_bdd(const bdd_table_t *table, bdd_t i) {
  return var_of_node(table, node_of_bdd(i));
}

static bdd_t left_of_bdd(const bdd_table_t *table, bdd_t i) {
  return left_of_node(table, node_of_bdd(i)) ^ polarity_of_bdd(i);
}

static bdd_t right_of_bdd(const bdd_table_t *table, bdd_t i) {
  return right_of_node(table, node_of_bdd(i)) ^ polarity_of_bdd(i);
}


/*
 * BDD Construction and Function simplification
 */

/*
 * Create the bdd (ite x left right):
 * - normalize to ensure that left has positive polarity
 * - return the id of the bdd
 */
bdd_t mk_bdd_node(bdd_table_t *table, bvar_t x, bdd_t left, bdd_t right) {
  uint32_t polarity;
  bdd_node_t j;

  assert(good_bdd(table, left) && good_bdd(table, right) && x != null_bvar);

  if (left == right) return left;

  /* 
   * normalize: (ite x left right) to not (ite x (not left) (not right))
   * if left has negative polarity.
   */
  polarity = polarity_of_bdd(left);
  left ^= polarity;
  right ^= polarity;
  j = get_bdd_node(table, x, left, right);

  return mk_bdd(j, polarity);
}


/*
 * Search for the bdd (ite x left right)
 * - normalize first
 * - return null_bdd if the bdd iis not in the table.
 */
bdd_t try_bdd_node(bdd_table_t *table, bvar_t x, bdd_t left, bdd_t right) {
  uint32_t polarity;
  bdd_node_t j;

  assert(good_bdd(table, left) && good_bdd(table, right) && x != null_bvar && x != const_bvar);

  if (left == right) return left;

  /* 
   * normalize: (ite x left right) to not (ite x (not left) (not right))
   * if left has negative polarity.
   */
  polarity = polarity_of_bdd(left);
  left ^= polarity;
  right ^= polarity;
  j = find_bdd_node(table, x, left, right);

  return j == 0 ? null_bdd : mk_bdd(j, polarity);  
}


/*
 * Create a bdd node to represent literal l:
 * - this creates the bdd (ite x true false) where x = var_of(l)
 *   and stores the entry [x -> bdd] in the internal map.
 * - if there's already a node mapped to x, return it.
 */
bdd_t mk_bdd_for_literal(bdd_table_t *table, literal_t l) {
  bdd_node_t j;
  bvar_t x;

  if (l == true_literal) return true_bdd;
  if (l == false_literal) return false_bdd;

  x = var_of(l);
  j = get_bdd_node(table, x, true_bdd, false_bdd);
  if (table->data[j].map == null_literal) {
    table->data[j].map = pos_lit(x);
    add_node_map_entry(table, x, j);
  }

  return mk_bdd(j, sign_of_lit(l));
}


/*
 * Get or create a bdd node to represent literal l
 */
static bdd_t get_bdd_for_literal(bdd_table_t *table, literal_t l) {
  bdd_t i;

  i = bdd_for_literal(table, l);
  if (i == null_bdd) i = mk_bdd_for_literal(table, l);

  return i;
}

/*
 * Create a bdd node to represent (ite c a b) 
 * - this creates the bdd (ite x bdd_for(a) bdd_for(b))
 *   where x = var_of(c).
 * - if there's already such a bdd, return it.
 */
bdd_t mk_bdd_for_ite(bdd_table_t *table, literal_t c, literal_t a, literal_t b) {
  bvar_t x;
  literal_t aux;
  bdd_t left, right;

  x = var_of(c);
  if (is_neg(c)) {
    // (ite ~x a b) --> (ite x b a)
    aux = a; a = b; b = aux;
  }

  left = get_bdd_for_literal(table, a);
  right = get_bdd_for_literal(table, b);

  return mk_bdd_node(table, x, left, right);
}


/*
 * Cache lookup and store
 */
static bdd_t xor_cache_find(bdd_table_t *table, bdd_t x, bdd_t y) {
  bdd_t aux;

  assert(good_bdd(table, x) && good_bdd(table, y));

  if (x > y) {
    aux = x; x = y; y = aux;
  }
  assert(x <= y);
  return cache_find(&table->xor_cache, x, y);
}

static bdd_t or_cache_find(bdd_table_t *table, bdd_t x, bdd_t y) {
  bdd_t aux;

  assert(good_bdd(table, x) && good_bdd(table, y));

  if (x > y) {
    aux = x; x = y; y = aux;
  }
  assert(x <= y);
  return cache_find(&table->or_cache, x, y);
}

static void xor_cache_store(bdd_table_t *table, bdd_t x, bdd_t y, bdd_t r) {
  bdd_t aux;

  assert(good_bdd(table, x) && good_bdd(table, y) && good_bdd(table, r));

  if (x > y) {
    aux = x; x = y; y = aux;
  }
  assert(x <= y);
  cache_store(&table->xor_cache, x, y, r);
}

static void or_cache_store(bdd_table_t *table, bdd_t x, bdd_t y, bdd_t r) {
  bdd_t aux;

  assert(good_bdd(table, x) && good_bdd(table, y) && good_bdd(table, r));

  if (x > y) {
    aux = x; x = y; y = aux;
  }
  assert(x <= y);
  cache_store(&table->or_cache, x, y, r);
}


/*
 * BDD for (xor x y):
 */
static bdd_t make_xor_bdd(bdd_table_t *table, bdd_t x, bdd_t y) {
  bvar_t vx, vy;
  bdd_t left, right, r;

  assert(good_bdd(table, x) && good_bdd(table, y));

  if (x == y) return false_bdd;
  if (x == not_bdd(y)) return true_bdd;
  if (x == false_bdd) return y;
  if (x == true_bdd)  return not_bdd(y);
  if (y == false_bdd) return x;
  if (y == true_bdd) return not_bdd(x);

  //  printf("call to make_xor_bdd(%"PRIu32", %"PRIu32")\n", x, y);

  vx = var_of_bdd(table, x);
  vy = var_of_bdd(table, y);
  if (vx != vy) return null_bdd; // stop here

  r = xor_cache_find(table, x, y);
  if (r == null_bdd) {
    left = make_xor_bdd(table, left_of_bdd(table, x), left_of_bdd(table, y));
    if (left == null_bdd) return null_bdd;

    right = make_xor_bdd(table, right_of_bdd(table, x), right_of_bdd(table, y));
    if (right == null_bdd) return null_bdd;

    r = mk_bdd_node(table, vx, left, right);
    xor_cache_store(table, x, y, r);
  }

  return r;
}


/*
 * BDD for (or x y):
 */
static bdd_t make_or_bdd(bdd_table_t *table, bdd_t x, bdd_t y) {
  bvar_t vx, vy;
  bdd_t left, right, r;

  assert(good_bdd(table, x) && good_bdd(table, y));

  if (x == y) return x;
  if (x == not_bdd(y)) return true_bdd;
  if (x == false_bdd) return y;
  if (x == true_bdd)  return true_bdd;
  if (y == false_bdd) return x;
  if (y == true_bdd) return true_bdd;

  //  printf("call to make_or_bdd(%"PRIu32", %"PRIu32")\n", x, y);

  vx = var_of_bdd(table, x);
  vy = var_of_bdd(table, y);
  if (vx != vy) return null_bdd; // stop here

  r = or_cache_find(table, x, y);
  if (r == null_bdd) {
    left = make_or_bdd(table, left_of_bdd(table, x), left_of_bdd(table, y));
    if (left == null_bdd) return null_bdd;

    right = make_or_bdd(table, right_of_bdd(table, x), right_of_bdd(table, y));
    if (right == null_bdd) return null_bdd;

    r = mk_bdd_node(table, vx, left, right);
    or_cache_store(table, x, y, r);
  }

  return r;
}


/*
 * Create a bdd node for (xor a b)
 */
bdd_t mk_bdd_for_xor(bdd_table_t *table, literal_t a, literal_t b) {
  bdd_t x, y;

  x = bdd_for_literal(table, a);
  y = bdd_for_literal(table, b);

  if (x == null_bdd || y == null_bdd) return null_bdd;

  return make_xor_bdd(table, x, y);
}

/*
 * Create a bdd node for (or a b)
 */
bdd_t mk_bdd_for_or(bdd_table_t *table, literal_t a, literal_t b) {
  bdd_t x, y;

  x = bdd_for_literal(table, a);
  y = bdd_for_literal(table, b);

  if (x == null_bdd || y == null_bdd) return null_bdd;

  return make_or_bdd(table, x, y);
}




/*
 * SIMPLIFICATIONS
 */

/*
 * BDD for (xor x y):
 */
static bdd_t simplify_xor_bdd(bdd_table_t *table, bdd_t x, bdd_t y) {
  bvar_t vx, vy;
  bdd_t left, right, r;

  assert(good_bdd(table, x) && good_bdd(table, y));

  if (x == y) return false_bdd;
  if (x == not_bdd(y)) return true_bdd;
  if (x == false_bdd) return y;
  if (x == true_bdd)  return not_bdd(y);
  if (y == false_bdd) return x;
  if (y == true_bdd) return not_bdd(x);

  //  printf("call to simplify_xor_bdd(%"PRIu32", %"PRIu32")\n", x, y);

  vx = var_of_bdd(table, x);
  vy = var_of_bdd(table, y);
  if (vx != vy) return null_bdd; // stop here

  r = xor_cache_find(table, x, y);
  if (r != null_bdd) return r;

  left = simplify_xor_bdd(table, left_of_bdd(table, x), left_of_bdd(table, y));
  if (left == null_bdd) return null_bdd;

  right = simplify_xor_bdd(table, right_of_bdd(table, x), right_of_bdd(table, y));
  if (right == null_bdd) return null_bdd;

  r = try_bdd_node(table, vx, left, right);
  if (r != null_bdd) xor_cache_store(table, x, y, r);

  return r;
}


/*
 * BDD for (or x y):
 */
static bdd_t simplify_or_bdd(bdd_table_t *table, bdd_t x, bdd_t y) {
  bvar_t vx, vy;
  bdd_t left, right, r;

  assert(good_bdd(table, x) && good_bdd(table, y));

  if (x == y) return x;
  if (x == not_bdd(y)) return true_bdd;
  if (x == false_bdd) return y;
  if (x == true_bdd)  return true_bdd;
  if (y == false_bdd) return x;
  if (y == true_bdd) return true_bdd;

  //  printf("call to simplify_or_bdd(%"PRIu32", %"PRIu32")\n", x, y);

  vx = var_of_bdd(table, x);
  vy = var_of_bdd(table, y);
  if (vx != vy) return null_bdd; // stop here

  r = or_cache_find(table, x, y);
  if (r != null_bdd) return r;

  left = simplify_or_bdd(table, left_of_bdd(table, x), left_of_bdd(table, y));
  if (left == null_bdd) return null_bdd;

  right = simplify_or_bdd(table, right_of_bdd(table, x), right_of_bdd(table, y));
  if (right == null_bdd) return null_bdd;

  r = try_bdd_node(table, vx, left, right);
  if (r != null_bdd) or_cache_store(table, x, y, r);

  return r;
}


/*
 * Attempt to simplify xor(x, y)
 */
literal_t bdd_xor_simplify(bdd_table_t *table, bdd_t x, bdd_t y) {
  bdd_t simp;

  //  printf("\n==== bdd_xor_simplify(%"PRIu32", %"PRIu32") ====\n", x, y);
  simp = simplify_xor_bdd(table, x, y);
  //  printf("done\n\n");
  if (simp == null_bdd) return null_literal;  

  return get_bdd_map(table, simp);
}


/*
 * Attempt to simplify or(x, y)
 */
literal_t bdd_or_simplify(bdd_table_t *table, bdd_t x, bdd_t y) {
  bdd_t simp;

  //  printf("\n==== bdd_or_simplify(%"PRIu32", %"PRIu32") ====\n", x, y);
  simp = simplify_or_bdd(table, x, y);
  //  printf("done\n\n");
  if (simp == null_bdd) return null_literal;
  
  return get_bdd_map(table, simp);
}


