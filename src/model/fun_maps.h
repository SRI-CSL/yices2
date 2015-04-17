/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Maps used as models by the function-theory solver
 * - a map is a finite list or pairs [index -> value]
 * - indices and values are represented as particles (see abstract_values.h)
 * - the indices in the list must be pairwise distinct
 * - the domain of a maps is the set of indices in the list
 * - each map may also be given a default value (i.e., what it maps to for
 *   indices outside its domain).
 */

#ifndef __FUN_MAPS_H
#define __FUN_MAPS_H

#include <stdint.h>
#include <assert.h>

#include "model/abstract_values.h"
#include "solvers/egraph/egraph_base_types.h"
#include "utils/int_vectors.h"

/*
 * Map object = array of pairs
 * - size = size of the array
 * - nelems = number of elements in the array
 * - def = default value (null_particle if no default is given)
 * - data = the array proper
 */
typedef struct map_elem_s {
  particle_t index;
  particle_t value;
} map_elem_t;

typedef struct map_s {
  uint32_t size;
  uint32_t nelems;
  particle_t def;
  map_elem_t *data;
} map_t;


#define DEF_MAP_SIZE 10
#define MAX_MAP_SIZE (UINT32_MAX/sizeof(map_elem_t))




/************************
 *  OPERATIONS ON MAPS  *
 ***********************/

/*
 * Create a map object of size n
 * - if n == 0, the default size is used
 * - the map is empty and has no default
 */
extern map_t *new_map(uint32_t n);


/*
 * Delete map
 */
extern void free_map(map_t *map);


/*
 * Set v as default value for map
 * - v must be non null
 */
static inline void set_map_default(map_t *map, particle_t v) {
  assert(v != null_particle);
  map->def = v;
}


/*
 * Add pair [index -> value] to map
 * - index must not occur in the map
 * - index and value must be non_null
 */
extern void add_elem_to_map(map_t *map, particle_t index, particle_t value);


/*
 * Normalize map:
 * - sort elements in increasing index order
 */
extern void normalize_map(map_t *map);


/*
 * Add pair [index -> value] to map and keep map normalized
 * - index must not occur in the map
 * - index and value must be non-null
 * - map must be normalized
 */
extern void add_elem_to_normal_map(map_t *map, particle_t index, particle_t value);



/*
 * Get the default value of map
 * - return null_particle if no default is specified
 */
static inline particle_t map_default_value(map_t *map) {
  return map->def;
}

/*
 * Get the number of pairs [index -> value] in map
 */
static inline uint32_t map_num_elems(map_t *map) {
  return map->nelems;
}


/*
 * Evaluate map at index k
 * - map must be normalized and k must be non-null
 * - if k is an index in map, return the corresponding value
 * - otherwise, if map has a default value return it
 * - otherwise return null_particle
 */
extern particle_t eval_map(map_t *map, particle_t k);



/*
 * Check whether map1 and map2 are equal
 * - the maps are considered equal if they have the same
 *   default value (or both have no default)
 *   and the same set of pairs [idx->value]
 * - both maps must be normalized
 */
extern bool equal_maps(map_t *map1, map_t *map2);


/*
 * Search for a point where map1 and map2 disagree.
 * - both maps must be normalized
 * - search for k in the domain of map1 and map2 such that
 *   eval_map(map1, k) != eval_map(map2, k)
 * - return k if it's found or null_particle otherwise
 */
extern particle_t disagreement_point(map_t *map1, map_t *map2);


/*
 * Search for a point that's in domain of map1 or map2
 * but not in both.
 * - both maps must be normalized
 * - return null_particle if map1 and map2 have the same domain
 */
extern particle_t distinguishing_point(map_t *map1, map_t *map2);


/*
 * Add all indices in the domain of map into vector v
 */
extern void collect_map_indices(map_t *map, ivector_t *v);


/*
 * Check whether index k is in the domain of map
 * - map must be normalized
 * - k must be non-null
 */
extern bool index_in_map_domain(map_t *map, particle_t k);




/*
 * Force maps map[0 ... n-1] to be all distinct by updating them.
 * - pstore = particle store to create fresh indices
 * - f = type descriptor for all the maps in the array
 *
 * Technique used:
 * - create fresh indices i_1,..,i_k in the domain of f
 * - create c values a_1,..., a_c in the range of f
 * such that (c ^ k) >= n.
 * Update map[t] by adding [i_1 -> a_t1, ..., i_k -> a_tk]
 * in such a way that (t1, ...., tk) differ from (u1, ..., uk) when u/=t.
 *
 * Return false if that's not possible (i.e., the number of functions
 * of the type f is finite and smaller than n).
 */
extern bool force_maps_to_differ(pstore_t *store, function_type_t *f, uint32_t n, map_t **map);


#endif /* __FUN_MAPS_H */
