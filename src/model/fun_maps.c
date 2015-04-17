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
 * - a pair [-1 -> x] means that x is the default value
 */

#include <stdbool.h>
#include <assert.h>

#include "model/fun_maps.h"
#include "utils/int_powers.h"
#include "utils/memalloc.h"
#include "utils/prng.h"


/************************
 *  OPERATIONS ON MAPS  *
 ***********************/

/*
 * Create a map object of size n
 * - if n == 0, the default size is used
 */
map_t *new_map(uint32_t n) {
  map_t *map;

  if (n == 0) {
    n = DEF_MAP_SIZE;
  }
  if (n >= MAX_MAP_SIZE) {
    out_of_memory();
  }

  map = (map_t *) safe_malloc(sizeof(map_t));
  map->size = n;
  map->nelems = 0;
  //  map->id = x;
  map->def = null_particle; // no default given
  map->data = (map_elem_t *) safe_malloc(n * sizeof(map_elem_t));

  return map;
}


/*
 * Delete map
 */
void free_map(map_t *map) {
  safe_free(map->data);
  safe_free(map);
}


/*
 * Make map 50% larger
 */
static void extend_map(map_t *map) {
  uint32_t n;

  n = map->size + 1;
  n += n>>1;
  if (n >= MAX_MAP_SIZE) {
    out_of_memory();
  }

  map->data = (map_elem_t *) safe_realloc(map->data, n * sizeof(map_elem_t));
  map->size = n;
}





/*
 * ARRAYS OF MAP ELEMENTS
 */

/*
 * Sort array of map elements in index order
 * - a = array of n map_elements
 */
static void qsort_map_array(map_elem_t *a, uint32_t n);

// insertion sort
static void isort_map_array(map_elem_t *a, uint32_t n) {
  uint32_t i, j;
  map_elem_t x, y;

  for (i=1; i<n; i++) {
    x = a[i];
    j = 0;
    while (a[j].index < x.index) j ++;
    while (j < i) {
      y = a[j]; a[j] = x; x = y;
      j ++;
    }
    a[j] = x;
  }
}


static inline void sort_map_array(map_elem_t *a, uint32_t n) {
  if (n < 10) {
    isort_map_array(a, n);
  } else {
    qsort_map_array(a, n);
  }
}


// quick sort: requires n>1
static void qsort_map_array(map_elem_t *a, uint32_t n) {
  uint32_t i, j;
  map_elem_t x, y;

  // x = random pivot
  i = random_uint(n);
  x = a[i];

  // swap a[i] and a[0]
  a[i] = a[0];
  a[0] = x;

  i = 0;
  j = n;

  do { j--; } while (a[j].index > x.index);
  do { i++; } while (i <= j && a[i].index < x.index);

  while (i < j) {
    // swap a[i] and a[j]
    y = a[i]; a[i] = a[j]; a[j] = y;

    do { j--; } while (a[j].index > x.index);
    do { i++; } while (a[i].index < x.index);
  }

  // swap a[0] = x and a[j]
  a[0] = a[j];
  a[j] = x;

  // recursive sort
  sort_map_array(a, j);
  j ++;
  sort_map_array(a + j, n - j);
}




/*
 * Check whether a and b are equal
 * - both must have size n
 */
static bool equal_map_arrays(map_elem_t *a, map_elem_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i].index != b[i].index || a[i].value != b[i].value) {
      return false;
    }
  }
  return true;
}



/*
 * Binary search for a pair of index k in array a
 * - n = size of the array (must be less than MAX_MAP_SIZE)
 * - if there's i such that a[i].index = k then return i
 *   otherwise, return -1
 */
static int32_t binary_search_map_array(map_elem_t *a, uint32_t n, particle_t k) {
  uint32_t l, h, mid;

  assert(n < MAX_MAP_SIZE);

  l = 0;
  h = n;
  if (h == 0) return null_particle;

  for (;;) {
    mid = (l + h)/2;  // no overflow possible since n < MAX_MAP_SIZE
    assert(l <= mid && mid < h && h <= n);
    if (mid == l) break;
    if (a[mid].index > k) {
      h = mid;
    } else {
      l = mid;
    }
  }

  if (a[mid].index == k) {
    return mid;
  } else {
    return -1;
  }
}


/*
 * DEBUGGING
 */

#ifndef NDEBUG

/*
 * For debugging: check whether idx occurs in map
 */
static bool index_is_in_map(map_t *map, particle_t idx) {
  uint32_t i, n;

  n = map->nelems;
  for (i=0; i<n; i++) {
    if (map->data[i].index == idx) {
      return true;
    }
  }

  return false;
}


/*
 * For debugging: check whether map is in strictly increasing index order
 */
static bool map_is_normal(map_t *map) {
  uint32_t i, n;

  n = map->nelems;
  if (n >= 2) {
    n --;
    for (i=0; i<n; i++) {
      if (map->data[i].index >= map->data[i+1].index) {
        return false;
      }
    }
  }

  return true;
}


#endif



/*
 * CONSTRUCTION/NORMALIZATION
 */

/*
 * Add the pair [index -> value] to map
 * - index must not occur in the map
 * - value and index must be non-null
 */
void add_elem_to_map(map_t *map, particle_t index, particle_t value) {
  uint32_t i;

  assert(index != null_particle && value != null_particle &&
         !index_is_in_map(map, index));

  i = map->nelems;
  if (i == map->size) {
    extend_map(map);
  }
  assert(i < map->size);

  map->data[i].index = index;
  map->data[i].value = value;
  map->nelems = i+1;
}



/*
 * Normalize map:
 * - sort all elements in increasing index order
 */
void normalize_map(map_t *map) {
  sort_map_array(map->data, map->nelems);
}


/*
 * Add pair [index -> value] to map and keep map normalized
 * - map must be normalized
 * - index must not occur in the map
 * - value and index must be non-null
 */
void add_elem_to_normal_map(map_t *map, particle_t index, particle_t value) {
  uint32_t i, n;

  assert(index != null_particle && value != null_particle && map_is_normal(map));

  n = map->nelems;
  if (n == map->size) {
    extend_map(map);
  }
  assert(n < map->size);
  map->nelems = n+1;

  i = n;
  while (i > 0 && map->data[i-1].index > index) {
    map->data[i] = map->data[i-1];
    i --;
  }
  map->data[i].index = index;
  map->data[i].value = value;

  assert(map_is_normal(map));
}



/*
 * Evaluate map at index k
 * - map must be normalized
 * - if k is an index in map, return the corresponding value
 * - otherwise, if map has a default value return it
 * - otherwise return null_particle
 */
particle_t eval_map(map_t *map, particle_t k) {
  int32_t i;
  particle_t v;

  assert(map_is_normal(map));

  v = map->def; // default value
  i = binary_search_map_array(map->data, map->nelems, k);
  if (i >= 0) {
    assert(map->data[i].index == k);
    v = map->data[i].value;
  }

  return v;
}



/*
 * Check whether map1 and map2 are equal
 * - both must be normalized
 */
bool equal_maps(map_t *map1, map_t *map2) {
  uint32_t n;

  assert(map_is_normal(map1) && map_is_normal(map2));

  n = map1->nelems;
  return n == map2->nelems && map1->def == map2->def &&
    equal_map_arrays(map1->data, map2->data, n);
}


/*
 * Search for a point where map1 and map2 disagree
 * - both map1 and map2 must be normalized
 * - search for a point k that's in the domain of both
 *   map1 and map2 such that eval_map(map1, k) != eval_map(map2, k)
 * - if no adequate point is found, return null_particle
 */
particle_t disagreement_point(map_t *map1, map_t *map2) {
  uint32_t i1, i2;
  uint32_t n1, n2;
  particle_t k1, k2;
  particle_t d1, d2;

  assert(map_is_normal(map1) && map_is_normal(map2));
  n1 = map1->nelems;
  n2 = map2->nelems;

  d1 = map1->def;
  d2 = map2->def;

  i1 = 0;
  i2 = 0;
  while (i1<n1 && i2<n2) {
    k1 = map1->data[i1].index;
    k2 = map2->data[i2].index;
    if (k1 < k2) {
      // k1 not in map2's domain so map2[k1] = d2
      if (map1->data[i1].value != d2 && d2 != null_particle) {
        return k1;
      }
      i1 ++;
    } else if (k2 < k1) {
      // k2 not in map1's domain so map1[k2] = d1
      if (map2->data[i2].value != d1 && d1 != null_particle) {
        return k2;
      }
      i2 ++;
    } else {
      // k1  == k2
      if (map1->data[i1].value != map2->data[i2].value) {
        return k1;
      }
      i1 ++;
      i2 ++;
    }
  }

  if (d2 != null_particle) {
    while (i1 < n1) {
      k1 = map1->data[i1].index;
      if (map1->data[i1].value != d2) {
        return k1;
      }
      i1 ++;
    }
  }

  if (d1 != null_particle) {
    while (i2 < n2) {
      k2 = map2->data[i2].index;
      if (map2->data[i2].value != d1) {
        return k2;
      }
      i2 ++;
    }
  }

  // failure
  return null_particle;
}




/*
 * Search for a point in the domain of only one of map1 and map2
 * - map1 and map2 must be normalized
 * - return null_particle if the domains of map1 and map2 are equal
 */
particle_t distinguishing_point(map_t *map1, map_t *map2) {
  particle_t idx1, idx2;
  uint32_t i;
  uint32_t n1, n2;

  assert(map_is_normal(map1) && map_is_normal(map2));

  n1 = map1->nelems;
  n2 = map2->nelems;
  i = 0;
  while (i<n1 && i<n2 && map1->data[i].index == map2->data[i].index) {
    i ++;
  }

  if (i < n1 && i < n2) {
    idx1 = map1->data[i].index;
    idx2 = map2->data[i].index;
    assert(idx1 != idx2);
    if (idx1 < idx2) {
      return idx1;
    } else {
      return idx2;
    }
  } else if (i < n1) {
    assert(i == n2);
    return map1->data[i].index;
  } else if (i < n2) {
    assert(i == n1);
    return map2->data[i].index;
  } else {
    assert(i == n1 && i == n2);
    return null_particle;
  }
}



/*
 * Add all indices in the domain of map to vector v
 * - the default index (null_particle) is not added if it's present in map
 */
void collect_map_indices(map_t *map, ivector_t *v) {
  uint32_t i, n;

  n = map->nelems;
  for (i=0; i<n; i++) {
    ivector_push(v, map->data[i].index);
  }
}



/*
 * Check whether index k is in the domain of map
 */
bool index_in_map_domain(map_t *map, particle_t k) {
  return binary_search_map_array(map->data, map->nelems, k) >= 0;
}





/***********************************
 *  CONSTRUCTION OF DISTINCT MAPS  *
 **********************************/

/*
 * Tuple increment:
 * - a = an array of n integers between 0 and (c-1)
 * - increment a: in reverse lexicographic order
 */
static void tuple_successor(uint32_t *a, uint32_t n, uint32_t c) {
  uint32_t i;

  i = n;
  while (i > 0) {
    i --;
    a[i] ++;
    if (a[i] < c) {
      return;
    }
    assert(a[i] == c);
    a[i] = 0;
  }

  assert(false);
}


/*
 * Compute the smallest k such that (c ^ k) >= n
 */
static uint32_t ceil_log(uint32_t c, uint32_t n) {
  uint32_t k, d;

  assert(c > 1);
  k = 1;
  d = c;
  while (d < n) {
    d *= c;
    k ++;
  }

  return k;
}


/*
 * Force maps map[0 ... n-1] to be all distinct by updating them.
 * - store = particle store to create fresh indices
 * - f = type descriptor for all the maps in the array
 * - n must be positive
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
bool force_maps_to_differ(pstore_t *store, function_type_t *f, uint32_t n, map_t **map) {
  type_table_t *types;
  particle_t *idx;
  particle_t *a;
  uint32_t *tuple;
  type_t tau;
  uint32_t i, j, k, c;

  types = store->types;
  tau = f->range;

  if (is_unit_type(types, tau)) {
    return false;
  }

  if (is_finite_type(types, tau)) {
    c = type_card(types, tau);
    k = ceil_log(c, n);
  } else {
    c = n;
    k = 1;
  }

  assert(k>0 && c>0 && upower32(c, k) >= n);

  // tuple + index array are of size k
  // a is of size c
  tuple = (uint32_t *) safe_malloc(k * sizeof(uint32_t));
  idx = (particle_t *) safe_malloc(k * sizeof(particle_t));
  a = (particle_t *) safe_malloc(c * sizeof(particle_t));

  // initialize the idx array with fresh values
  if (f->ndom == 1) {
    for (i=0; i<k; i++) {
      idx[i] = get_new_particle(store, f->domain[0]);
      if (idx[i] == null_particle) goto failed;
    }
  } else {
    for (i=0; i<k; i++) {
      idx[i] = get_new_tuple(store, f->ndom, f->domain);
      if (idx[i] == null_particle) goto failed;
    }
  }

  // fill-in a with c distinct values of type tau
  for (i=0; i<c; i++) {
    a[i] = get_distinct_particle(store, tau, i, a);
    assert(a[i] != null_particle);
  }

  // initialize tuple = (0,...,0)
  for (i=0; i<k; i++) {
    tuple[i] = 0;
  }

  // update then normalize the maps
  i = 0;
  for (;;) {
    assert(i < n);
    for (j=0; j<k; j++) {
      assert(tuple[j] < c);
      add_elem_to_map(map[i], idx[j], a[tuple[j]]);
    }
    normalize_map(map[i]);
    i ++;
    if (i == n) break;
    tuple_successor(tuple, k, c);
  }

  safe_free(a);
  safe_free(idx);
  safe_free(tuple);
  return true;


 failed:
  safe_free(a);
  safe_free(idx);
  safe_free(tuple);
  return false;
}

