/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Support for handling arithmetic equalities of the form x = y + k
 * where x and y are variables and k is a constant.
 */

#include <assert.h>

#include "solvers/simplex/offset_equalities.h"
#include "utils/index_vectors.h"
#include "utils/memalloc.h"


/*
 * MAP ARRAY
 */

/*
 * Initialize map to the empty array
 */
static void init_remap(remap_array_t *map) {
  map->data = NULL;
  map->size = 0;
}


/*
 * Delete
 */
static void delete_remap(remap_array_t *map) {
  safe_free(map->data);
  map->data = NULL;
}


/*
 * Reset to the default map:
 */
static void reset_remap(remap_array_t *map) {
  uint32_t i, n;

  n = map->size;
  for (i=0; i<n; i++) {
    map->data[i] = -1;
  }
}


/*
 * Clear anything that's mapped to an index >= k
 */
static void remap_cleanup(remap_array_t *map, int32_t k) {
  uint32_t i, n;

  assert(k >= 0);
  n = map->size;
  for (i=0; i<n; i++) {
    if (map->data[i] >= k) {
      map->data[i] = -1;
    }
  }
}



/*
 * Make map large enough to store map[x]
 * - set map[i] to -1 for all new i's
 */
static void resize_remap(remap_array_t *map, int32_t x) {
  uint32_t i, n, min_size;

  assert(0 <= x);

  min_size = ((uint32_t) x) + 1;
  n = map->size;
  if (n < min_size) {
    if (n == 0) {
      n = DEF_REMAP_ARRAY_SIZE;
    } else {
      // try 50% larger
      n += (n + 1) >> 1;
    }

    if (n < min_size) {
      n = min_size;
    }

    if (n > MAX_REMAP_ARRAY_SIZE) {
      out_of_memory();
    }

    map->data = (int32_t *) safe_realloc(map->data, n * sizeof(int32_t));
    for (i = map->size; i<n; i++) {
      map->data[i] = -1;
    }
    map->size = n;
  }
}


/*
 * Store the map [x -> i]
 * - x must be non-negative
 */
static void remap_set(remap_array_t *map, int32_t x, int32_t i) {
  resize_remap(map, x);
  assert(map->size > (uint32_t) x);
  map->data[x] = i;
}


/*
 * Get what's mapped to x (-1 if nothing mapped)
 */
static int32_t remap_get(remap_array_t *map, int32_t x) {
  int32_t k;

  assert(x >= 0);

  k = -1;
  if ((uint32_t) x < map->size) {
    k = map->data[x];
  }

  return k;
}


/*
 * Variant to use if x is known to be mapped
 */
static inline int32_t remap_find(remap_array_t *map, int32_t x) {
  assert(0 <= x && (uint32_t) x < map->size);
  return map->data[x];
}



/*
 * OBJECT STORE FOR POLYNOMIALS
 */

/*
 * Each object in the store is a polynomial with one monomial + end marker
 */
#define OBJ_POLY_SIZE (sizeof(polynomial_t) + 2 * sizeof(monomial_t))

/*
 * Initialize store s for these polynomials
 */
static inline void init_poly_store(object_store_t *s) {
  init_objstore(s, OBJ_POLY_SIZE, 100);
}


/*
 * Allocate a polynomial and initialize it to 1.x
 * - x must be a variable (i.e., not const_idx and not max_idx)
 */
static polynomial_t *make_simple_poly(object_store_t *s, int32_t x) {
  polynomial_t *p;

  assert(const_idx < x && x < max_idx);
  p = objstore_alloc(s);

  p->nterms = 1;
  // monomial = 1 * x
  p->mono[0].var = x;
  q_init(&p->mono[0].coeff);
  q_set_one(&p->mono[0].coeff);
  // end marker
  p->mono[1].var = max_idx;

  return p;
}


/*
 * Free polynomial p allocated by the previous function
 *
 * NOTE: we don't call q_clear(&p->mono[0]) because the coefficient
 * is always 1 (so q_clear does nothing in this case).
 */
static void free_simple_poly(object_store_t *s, polynomial_t *p) {
  objstore_free(s, p);
}



/*
 * DEPENDENCY ARRAYS
 */

/*
 * Allocate and initialize a dep array of size n
 * - if n == 0, just return NULL
 */
static var_array_t *new_var_array(uint32_t n) {
  var_array_t *tmp;

  tmp = NULL;
  if (n > 0) {
    if (n > MAX_VAR_ARRAY_SIZE) {
      out_of_memory();
    }

    tmp = (var_array_t *) safe_malloc(sizeof(var_array_t) + n * sizeof(var_rec_t));
    tmp->size = n;
    tmp->ndeps = 0;
  }

  return tmp;
}


/*
 * Allocate and initialize a dependency vector of size n
 */
static dep_t *new_dep_vector(uint32_t n) {
  dep_t *tmp;

  assert(n <= MAX_DEP_ARRAY_SIZE);

  tmp = (dep_t *) safe_malloc(sizeof(dep_t) + n * sizeof(int32_t));
  tmp->size = n;
  tmp->nelems = 0;
  tmp->free_list = encode_idx(MAX_DEP_ARRAY_SIZE);

  return tmp;
}


/*
 * Increase the size of vector v
 */
static dep_t *extend_dep_vector(dep_t *v) {
  uint32_t n;

  n = v->size + 1;
  n += (n >> 1); // 50% larger
  if (n > MAX_DEP_ARRAY_SIZE) {
    out_of_memory();
  }

  v = (dep_t *) safe_realloc(v, sizeof(dep_t) + n * sizeof(int32_t));
  v->size = n;

  return v;
}


/*
 * Delete vector v
 */
static inline void delete_dep_vector(dep_t *v) {
  safe_free(v);
}


/*
 * Get an empty slot in (*v)->data
 * - if *v is NULL allocate an initial vector of default size
 * - if *v is full, increase its size
 */
static int32_t dep_vector_alloc_slot(dep_t **v) {
  dep_t *vector;
  int32_t k;

  vector = *v;
  if (vector == NULL) {
    vector = new_dep_vector(DEF_DEP_ARRAY_SIZE);
    *v = vector;
    assert(vector->size >= 1);
    vector->nelems = 1;
    k = 0;
  } else {
   // try the free list
    k = decode_idx(vector->free_list);
    if (k == MAX_DEP_ARRAY_SIZE) {
      // the free list is empty: increase nelems
      k = vector->nelems;
      if (k == vector->size) {
        // full vector: make it larger
        vector = extend_dep_vector(vector);
        *v = vector;
        assert(0 <= k && k < vector->size);
      }
      vector->nelems ++;
    } else {
      // update the free list
      assert(0 <= k && k < vector->nelems);
      vector->free_list = vector->data[k];
    }
  }

  return k;
}


/*
 * Free slot k in v
 */
static void dep_vector_free_slot(dep_t *v, int32_t k) {
  assert(0 <= k && k < v->nelems);

  v->data[k] = v->free_list;
  v->free_list = encode_idx(k);
}



/*
 * Add i to dependency vector *v
 * - this stores i into *v->data[k] for some k and return k
 */
static int32_t dep_vector_add(dep_t **v, int32_t i) {
  int32_t k;

  k = dep_vector_alloc_slot(v);
  (*v)->data[k] = i;
  return k;
}



/*
 * POLYNOMIAL TABLE
 */

/*
 * Initialize (empty table)
 */
static void init_offset_poly_table(offset_poly_table_t *table) {
  table->npolys = 0;
  table->size = 0;
  table->eterm = NULL;
  table->def = NULL;
  table->hash = NULL;
  table->vars = NULL;
  table->active = NULL;
  table->mark = NULL;

  init_remap(&table->var2poly);
  init_poly_store(&table->pstore);
}


/*
 * Delete the table
 */
static void delete_offset_poly_table(offset_poly_table_t *table) {
  uint32_t i, n;

  n = table->npolys;
  for (i=0; i<n; i++) {
    safe_free(table->vars[i]);
  }

  safe_free(table->eterm);
  safe_free(table->def);
  safe_free(table->hash);
  safe_free(table->vars);
  delete_bitvector(table->active);
  delete_bitvector(table->mark);

  delete_remap(&table->var2poly);

  /*
   * Hack: we don't call q_clear for the rational coefficients
   * in polynomials allocated in pstore (because they are all 1).
   */
  delete_objstore(&table->pstore);

  table->eterm = NULL;
  table->def = NULL;
  table->hash = NULL;
  table->vars = NULL;
  table->active = NULL;
  table->mark = NULL;
}


/*
 * Make the table larger
 */
static void extend_offset_poly_table(offset_poly_table_t *table) {
  uint32_t n;

  n = table->size;
  if (n == 0) {
    // first allocation
    n = DEF_OFFSET_POLY_TABLE_SIZE;
    assert(n <= MAX_OFFSET_POLY_TABLE_SIZE);

    table->eterm = (eterm_t *) safe_malloc(n * sizeof(eterm_t));
    table->def = (polynomial_t **) safe_malloc(n * sizeof(polynomial_t *));
    table->hash = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
    table->vars = (var_array_t **) safe_malloc(n * sizeof(var_array_t *));
    table->active = allocate_bitvector(n);
    table->mark = allocate_bitvector(n);

    table->size = n;
  } else {
    // try 50% larger
    n += (n + 1) >> 1;

    if (n > MAX_OFFSET_POLY_TABLE_SIZE) {
      out_of_memory();
    }

    table->eterm = (eterm_t *) safe_realloc(table->eterm, n * sizeof(eterm_t));
    table->def = (polynomial_t **) safe_realloc(table->def, n * sizeof(polynomial_t *));
    table->hash = (uint32_t *) safe_realloc(table->hash, n * sizeof(uint32_t));
    table->vars = (var_array_t **) safe_realloc(table->vars, n * sizeof(var_array_t *));
    table->active = extend_bitvector(table->active, n);
    table->mark = extend_bitvector(table->mark, n);

    table->size = n;
  }
}


/*
 * Empty the table
 */
static void reset_offset_poly_table(offset_poly_table_t *table) {
  uint32_t i, n;

  n = table->npolys;
  for (i=0; i<n; i++) {
    safe_free(table->vars[i]);
  }

  table->npolys = 0;
  reset_remap(&table->var2poly);
  reset_objstore(&table->pstore); // same hack as for delete
}


/*
 * Check whether polynomial p is simple
 * - i = corresponding index
 */
static bool offset_poly_is_simple(offset_poly_table_t *table, polynomial_t *p, int32_t i) {
  int32_t x;

  assert(0 <= i && i < table->npolys && table->def[i] == p);

  if (p->nterms == 1) {
    x = p->mono[0].var;
    if (remap_find(&table->var2poly, x) == i) {
      assert(q_is_one(&p->mono[0].coeff));
      return true;
    }
  }

  return false;
}


/*
 * Number of variables in p (skip the constant if any)
 */
static uint32_t poly_num_vars(polynomial_t *p) {
  uint32_t n;

  n = p->nterms;
  if (n > 0 && p->mono[0].var == const_idx) {
    n --;
  }

  return n;
}




/*
 * Store a new poly in table
 * - t = egraph term
 * - x = arithmetic variable
 * - p = polynomial
 * - p must be non NULL, x must be valid variable
 * - the dependency vector vars[i] is empty
 * return the index for this new polynomial
 */
static int32_t store_offset_poly(offset_poly_table_t *table, eterm_t t, thvar_t x, polynomial_t *p) {
  uint32_t i;

  assert(p != NULL && const_idx < x && x < max_idx && remap_get(&table->var2poly, x) < 0);

  i = table->npolys;
  if (i == table->size) {
    extend_offset_poly_table(table);
  }
  assert(i < table->size);

  table->eterm[i] = t;
  table->def[i] = p;
  table->vars[i] = new_var_array(poly_num_vars(p));
  table->hash[i] = 0; // could be anything
  clr_bit(table->active, i);
  clr_bit(table->mark, i);

  remap_set(&table->var2poly, x, i);

  table->npolys = i+1;

  return i;
}



/*
 * Set/clear/test the mark for polynomial k
 */
static inline void mark_offset_poly(offset_poly_table_t *table, int32_t k) {
  assert(0 <= k && k < table->npolys);
  set_bit(table->mark, k);
}

static inline void offset_poly_clear_mark(offset_poly_table_t *table, int32_t k) {
  assert(0 <= k && k < table->npolys);
  clr_bit(table->mark, k);
}

static inline bool offset_poly_is_marked(offset_poly_table_t *table, int32_t k) {
  assert(0 <= k && k < table->npolys);
  return tst_bit(table->mark, k);
}


/*
 * Get/set the active bit
 */
static inline void mark_offset_poly_active(offset_poly_table_t *table, int32_t k) {
  assert(0 <= k && k < table->npolys);
  set_bit(table->active, k);
}

static inline void mark_offset_poly_inactive(offset_poly_table_t *table, int32_t k) {
  assert(0 <= k && k < table->npolys);
  clr_bit(table->active, k);
}

static inline bool offset_poly_is_active(offset_poly_table_t *table, int32_t k) {
  assert(0 <= k && k < table->npolys);
  return tst_bit(table->active, k);
}

#ifndef NDEBUG
static inline bool offset_poly_is_inactive(offset_poly_table_t *table, int32_t k) {
  return !offset_poly_is_active(table, k);
}
#endif


/*
 * OFFSET-VARIABLE TABLE
 */

/*
 * Initialize descriptors + other fields for offset variable x
 * - x is root of a singleton class
 * - dep[x] is NULL
 */
static void init_offset_var(offset_table_t *table, int32_t x) {
  assert(0 <= x && x < table->nvars);

  table->desc[x].next = x; // x is the only element of its class
  table->desc[x].root = x;
  q_init(&table->desc[x].offset);  // x := x + 0

  table->edge[x] = -1;
  table->dep[x] = NULL;
}


/*
 * Initialization:
 * - always store the zero variable
 */
static void init_offset_table(offset_table_t *table) {
  uint32_t n;

  n = DEF_OFFSET_TABLE_SIZE;
  assert(0 < n && n <= MAX_OFFSET_TABLE_SIZE);

  table->size = n;
  table->desc = (offset_desc_t *) safe_malloc(n * sizeof(offset_desc_t));
  table->edge = (int32_t *) safe_malloc(n * sizeof(int32_t));
  table->dep = (dep_t **) safe_malloc(n * sizeof(dep_t *));

  init_remap(&table->var2offset_var);

  table->nvars = 1;
  init_offset_var(table, 0);
}



/*
 * Delete the table
 */
static void delete_offset_table(offset_table_t *table) {
  uint32_t i, n;

  n = table->nvars;
  for (i=0; i<n; i++) {
    q_clear(&table->desc[i].offset);
    delete_dep_vector(table->dep[i]);
  }

  safe_free(table->desc);
  safe_free(table->edge);
  safe_free(table->dep);

  delete_remap(&table->var2offset_var);

  table->desc = NULL;
  table->edge = NULL;
  table->dep = NULL;
}



/*
 * Empty the table (just keep the zero variable)
 */
static void reset_offset_table(offset_table_t *table) {
  uint32_t i, n;

  n = table->nvars;
  for (i=1; i<n; i++) {
    q_clear(&table->desc[i].offset);
    delete_dep_vector(table->dep[i]);
  }

  reset_remap(&table->var2offset_var);

  table->nvars = 1;
  table->desc[0].next = 0;

  assert(table->edge[0] < 0 && table->dep[0] == NULL &&
         table->desc[0].root == 0  && q_is_zero(&table->desc[0].offset));
}



/*
 * Make the table larger
 */
static void extend_offset_table(offset_table_t *table) {
  uint32_t n;

  n = table->size;
  n += (n + 1) >> 1; // 50% larger
  if (n > MAX_OFFSET_TABLE_SIZE) {
    out_of_memory();
  }

  table->size = n;
  table->desc = (offset_desc_t *) safe_realloc(table->desc, n * sizeof(offset_desc_t));
  table->edge = (int32_t *) safe_realloc(table->edge, n * sizeof(int32_t));
  table->dep = (dep_t **) safe_realloc(table->dep, n * sizeof(dep_t *));
}


/*
 * Allocate and initialize a new offset variable
 */
static int32_t alloc_offset_var(offset_table_t *table) {
  uint32_t i;

  i = table->nvars;
  if (i == table->size) {
    extend_offset_table(table);
  }
  assert(i < table->size);
  table->nvars = i+1;
  init_offset_var(table, i);

  return i;
}


/*
 * Make sure all arithmetic variables of p have a matching offset var
 * - create new offset vars if necessary
 */
static void make_offset_vars_for_poly(offset_table_t *table, polynomial_t *p) {
  uint32_t i, n;
  thvar_t x;
  int32_t j;

  n = p->nterms;
  if (n > 0) {
    i = 0;
    if (p->mono[0].var == const_idx) {
      i = 1;
    }

    while (i < n) {
      x = p->mono[i].var;
      j = remap_get(&table->var2offset_var, x);
      if (j < 0) {
        j = alloc_offset_var(table);
        remap_set(&table->var2offset_var, x, j);
      }
      i ++;
    }
  }
}


/*
 * Remove all variables of index >= nv
 */
static void remove_offset_vars(offset_table_t *table, uint32_t nv) {
  uint32_t i, n;

  assert(nv <= table->nvars);

  n = table->nvars;
  for (i=nv; i<n; i++) {
    delete_dep_vector(table->dep[i]);
  }
  table->nvars = nv;
  remap_cleanup(&table->var2offset_var, nv);
}


/*
 * Add i in the dependency vector of x
 * - return the index k where is is stored (i.e., dep[x]->data[k] = i)
 */
static int32_t offset_var_add_dep(offset_table_t *table, int32_t x, int32_t i) {
  assert(0 < x && x < table->nvars); // x should never be the zero variable
  return dep_vector_add(table->dep + x, i);
}


/*
 * Remove the dependent stored at index k in dep[x]
 */
static void offset_var_remove_dep(offset_table_t *table, int32_t x, int32_t k) {
  assert(0 < x && x < table->nvars);
  dep_vector_free_slot(table->dep[x], k);
}


#ifndef NDEBUG
/*
 * For debugging: check that dep[x] contains i at index k
 */
static bool offset_var_has_dep(offset_table_t *table, int32_t x, int32_t k, int32_t i) {
  dep_t *v;

  assert(0 < x && x < table->nvars && i >= 0);

  v = table->dep[x];
  assert(0 <= k && k < v->nelems);
  return v->data[k] == i;
}
#endif


/*
 * Size of vector dep[x] (approximate, we don't count the negative elements)
 */
static inline uint32_t offset_var_dep_size(offset_table_t *table, int32_t x) {
  dep_t *v;
  assert(0 < x && x < table->nvars);
  v = table->dep[x];
  return v == NULL ? 0 : v->nelems;
}



/*
 * NORMAL FORMS
 */

/*
 * Add c * (d->root + d->offset) to buffer b
 */
static void poly_buffer_addmul_offset(poly_buffer_t *b, rational_t *c, offset_desc_t *d) {
  poly_buffer_addmul_monomial(b, const_idx, c, &d->offset); // add c * d->offset
  if (d->root > 0) { // skip this if the root is zero
    poly_buffer_add_monomial(b, d->root, c); // add c * d->root
  }
}


/*
 * Compute the normal form of p (based on the current offset classes)
 * - store the result in buffer b
 * - all variables of p must have a matching offset var
 */
static void poly_offset_normal_form(offset_table_t *table, poly_buffer_t *b, polynomial_t *p) {
  uint32_t i, n;
  thvar_t x;
  int32_t j;

  reset_poly_buffer(b);

  n = p->nterms;
  if (n > 0) {
    // deal with the constant of p if any
    i = 0;
    if (p->mono[0].var == const_idx) {
      poly_buffer_add_const(b, &p->mono[0].coeff);
      i ++;
    }

    // other monomials
    while (i < n) {
      x = p->mono[i].var;
      j = remap_find(&table->var2offset_var, x);
      assert(0 < j && j < table->nvars);
      poly_buffer_addmul_offset(b, &p->mono[i].coeff, table->desc + j);

      i ++;
    }
  }

  normalize_poly_buffer(b);
}


/*
 * Hash code of polynomial stored in b
 */
static uint32_t hash_normal_form(poly_buffer_t *b) {
  return hash_monarray(poly_buffer_mono(b), poly_buffer_nterms(b));
}


/*
 * Check whether polynomials in b1 and b2 are equal
 */
static bool equal_normal_forms(poly_buffer_t *b1, poly_buffer_t *b2) {
  return equal_monarrays(poly_buffer_mono(b1), poly_buffer_mono(b2));
}





/*
 * HASH TABLE
 */

#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif

/*
 * Initialize to the default size
 */
static void init_offset_hash_table(offset_hash_table_t *table) {
  offset_hash_elem_t *tmp;
  uint32_t i, n;

  n = DEF_OFFSET_HASH_TABLE_SIZE;
  assert(n < MAX_OFFSET_HASH_TABLE_SIZE && is_power_of_two(n));

  tmp = (offset_hash_elem_t *) safe_malloc(n * sizeof(offset_hash_elem_t));
  for (i=0; i<n; i++) {
    tmp[i].index = -1;
  }

  table->data = tmp;
  table->size = n;
  table->nelems = 0;
  table->ndeleted = 0;

  table->resize_threshold = (uint32_t) (n * OFFSET_HASH_TABLE_RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t) (n * OFFSET_HASH_TABLE_CLEANUP_RATIO);
}


/*
 * Reset: empty the table
 */
static void reset_offset_hash_table(offset_hash_table_t *table) {
  uint32_t i, n;

  n = table->size;
  for (i=0; i<n; i++) {
    table->data[i].index = -1;
  }

  table->nelems = 0;
  table->ndeleted = 0;
}



/*
 * Delete the table
 */
static void delete_offset_hash_table(offset_hash_table_t *table) {
  safe_free(table->data);
  table->data = NULL;
}


/*
 * Store record d in a clean array
 * - mask = size of d - 1
 * - data must not contain deleted elements and must have at least one empty slot
 */
static void offset_hash_table_clean_copy(offset_hash_elem_t *data, offset_hash_elem_t *d, uint32_t mask) {
  uint32_t i;

  assert(d->index >= 0);

  i = d->hash & mask;
  while (data[i].index >= 0) {
    i ++;
    i &= mask;
  }
  data[i] = *d;
}


/*
 * Remove deleted elements from table
 */
static void offset_hash_table_cleanup(offset_hash_table_t *table) {
  offset_hash_elem_t *tmp, *d;
  uint32_t i, n, mask;

  assert(is_power_of_two(table->size));

  n = table->size;
  tmp = (offset_hash_elem_t *) safe_malloc(n * sizeof(offset_hash_elem_t));
  for (i=0; i<n; i++) {
    tmp[i].index = -1;
  }

  mask = n - 1;
  d = table->data;
  for (i=0; i<n; i++) {
    if (d->index >= 0) {
      offset_hash_table_clean_copy(tmp, d, mask);
    }
    d ++;
  }

  safe_free(table->data);
  table->data = tmp;
  table->ndeleted = 0;
}


/*
 * Cleanup and double the size
 */
static void offset_hash_table_extend(offset_hash_table_t *table) {
  offset_hash_elem_t *tmp, *d;
  uint32_t i, n, n2, mask;

  assert(is_power_of_two(table->size));

  n = table->size;
  n2 = n << 1;
  if (n2 > MAX_OFFSET_HASH_TABLE_SIZE) {
    out_of_memory();
  }

  tmp = (offset_hash_elem_t *) safe_malloc(n2 * sizeof(offset_hash_elem_t));
  for (i=0; i<n2; i++) {
    tmp[i].index = -1;
  }

  mask = n2 - 1;
  d = table->data;
  for (i=0; i<n; i++) {
    if (d->index >= 0) {
      offset_hash_table_clean_copy(tmp, d, mask);
    }
    d ++;
  }

  safe_free(table->data);
  table->data = tmp;
  table->ndeleted = 0;
  table->size = n2;

  table->resize_threshold = (uint32_t)(n2 * OFFSET_HASH_TABLE_RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t)(n2 * OFFSET_HASH_TABLE_CLEANUP_RATIO);
}


#ifndef NDEBUG

/*
 * Check whether i is in the table
 * - h = hash code for i
 */
static bool offset_hash_table_present(offset_hash_table_t *table, int32_t i, uint32_t h) {
  uint32_t mask, j;

  assert(table->nelems + table->ndeleted < table->size);

  mask = table->size - 1;
  j = h & mask;
  for (;;) {
    if (table->data[j].index == i) return true;
    if (table->data[j].index == -1) return false;
    j ++;
    j &= mask;
  }
}

#endif


/*
 * Remove i from the table
 * - h = hash code for i
 * - the record (i, h) must be present
 */
static void offset_hash_table_remove(offset_hash_table_t *table, int32_t i, uint32_t h) {
  uint32_t mask, j;

  assert(offset_hash_table_present(table, i, h));

  mask = table->size - 1;
  j = h & mask;
  while (table->data[j].index != i) {
    j ++;
    j &= mask;
  }

  assert(table->data[j].index == i && table->data[j].hash == h);

  table->data[j].index = -2; // mark as deleted
  table->nelems --;
  table->ndeleted ++;
  if (table->ndeleted > table->cleanup_threshold) {
    offset_hash_table_cleanup(table);
  }
}


#if 0

// NOT USED
/*
 * Add [i, h] to the table when it's known that i is not in there
 * - there must not be a record with index i in the table
 * - the table must not be full
 */
static void offset_hash_table_add(offset_hash_table_t *table, int32_t i, uint32_t h) {
  uint32_t mask, j;

  assert(! offset_hash_table_present(table, i, h));

  mask = table->size - 1;
  j = h & mask;
  while (table->data[j].index >= 0) {
    j ++;
    j &= mask;
  }

  table->data[j].index = i;
  table->data[j].hash = h;
  table->nelems ++;
  if (table->nelems + table->ndeleted > table->resize_threshold) {
    offset_hash_table_extend(table);
  }
}
#endif



/*
 * UNDO STACK
 */
static void init_offset_undo_stack(offset_undo_stack_t *stack) {
  uint32_t n;

  n = DEF_OFFSET_UNDO_SIZE;
  assert(n <= MAX_OFFSET_UNDO_SIZE);

  stack->data = (offset_undo_t *) safe_malloc(n * sizeof(offset_undo_t));
  stack->top = 0;
  stack->size = n;
}


static void extend_offset_undo_stack(offset_undo_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n >> 1;
  if (n > MAX_OFFSET_UNDO_SIZE) {
    out_of_memory();
  }
  stack->data = (offset_undo_t *) safe_realloc(stack->data, n * sizeof(offset_undo_t));
  stack->size = n;
}



/*
 * Push (x, rx) on top of the stack
 * - x = variable on left hand side of equality (x := y + k)
 * - rx = root of x before merging x's and y''s classes
 */
static void offset_undo_push(offset_undo_stack_t *stack, int32_t x, int32_t rx) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_offset_undo_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i].saved_var = x;
  stack->data[i].saved_root = rx;
  stack->top = i+1;
}


static void delete_offset_undo_stack(offset_undo_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


static inline void reset_offset_undo_stack(offset_undo_stack_t *stack) {
  stack->top = 0;

}


/*
 * INACTIVE POLY QUEUE
 */
static void init_inactive_poly_queue(inactive_poly_queue_t *queue) {
  uint32_t n;

  n = DEF_INACTIVE_QUEUE_SIZE;
  assert(n <= MAX_INACTIVE_QUEUE_SIZE);

  queue->data = (int32_t *) safe_malloc(n * sizeof(int32_t));
  queue->top = 0;
  queue->size = n;
}

static void extend_inactive_poly_queue(inactive_poly_queue_t *queue) {
  uint32_t n;

  n = queue->size + 1;
  n += (n >> 1);
  if (n > MAX_INACTIVE_QUEUE_SIZE) {
    out_of_memory();
  }
  queue->data = (int32_t *) safe_realloc(queue->data, n * sizeof(int32_t));
  queue->size = n;
}

static void inactive_poly_queue_push(inactive_poly_queue_t *queue, int32_t id) {
  uint32_t i;

  i = queue->top;
  if (i == queue->size) {
    extend_inactive_poly_queue(queue);
  }
  assert(i < queue->size);
  queue->data[i] = id;
  queue->top = i+1;
}

static void delete_inactive_poly_queue(inactive_poly_queue_t *queue) {
  safe_free(queue->data);
  queue->data = NULL;
}

static inline void reset_inactive_poly_queue(inactive_poly_queue_t *queue) {
  queue->top = 0;
}


/*
 * LEVEL STACK
 */
static void init_offset_level_stack(offset_level_stack_t *stack) {
  uint32_t n;

  n = DEF_OFFSET_LEVEL_STACK_SIZE;
  assert(0 < n && n <= MAX_OFFSET_LEVEL_STACK_SIZE);

  stack->data = (level_record_t *) safe_malloc(n * sizeof(level_record_t));
  stack->data[0].eq_ptr = 0;
  stack->data[0].undo_ptr = 0;
  stack->data[0].inactive_ptr = 0;

  stack->size = n;
}


static void extend_offset_level_stack(offset_level_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n>>1;
  if (n > MAX_OFFSET_LEVEL_STACK_SIZE) {
    out_of_memory();
  }

  stack->data = (level_record_t *) safe_realloc(stack->data, n * sizeof(level_record_t));
  stack->size = n;
}


static void delete_offset_level_stack(offset_level_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * RECHECK QUEUE
 */
static void init_recheck_queue(recheck_queue_t *queue) {
  queue->data = NULL;
  queue->top = 0;
  queue->size = 0;
}

static void delete_recheck_queue(recheck_queue_t *queue) {
  safe_free(queue->data);
  queue->data = NULL;
}

static inline void reset_recheck_queue(recheck_queue_t *queue) {
  queue->top = 0;
}

static void extend_recheck_queue(recheck_queue_t *queue) {
  uint32_t n;

  n = queue->size;
  if (n == 0) {
    n = DEF_RECHECK_QUEUE_SIZE;
    assert(0 < n && n <= MAX_RECHECK_QUEUE_SIZE);
    queue->data = (recheck_elem_t *) safe_malloc(n * sizeof(recheck_elem_t));
    queue->size = n;
  } else {
    n ++;
    n += (n >> 1);
    if (n > MAX_RECHECK_QUEUE_SIZE) {
      out_of_memory();
    }
    queue->data = (recheck_elem_t *) safe_realloc(queue->data, n * sizeof(recheck_elem_t));
    queue->size = n;
  }
}


/*
 * Add pair (level, id) to the queue
 */
static void push_to_recheck(recheck_queue_t *queue, uint32_t level, int32_t id) {
  uint32_t i;

  i = queue->top;
  if (i == queue->size) {
    extend_recheck_queue(queue);
  }
  assert(i < queue->size);

  queue->data[i].level = level;
  queue->data[i].id = id;
  queue->top = i+1;
}




/*
 * TRAIL STACK
 */
static void init_offset_trail_stack(offset_trail_stack_t *stack) {
  uint32_t n;

  n = DEF_OFFSET_TRAIL_SIZE;
  assert(n <= MAX_OFFSET_TRAIL_SIZE);

  stack->data = (offset_trail_t *) safe_malloc(n * sizeof(offset_trail_t));
  stack->top = 0;
  stack->size = n;
}


static void extend_offset_trail_stack(offset_trail_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n >> 1; // about 50% larger
  if (n > MAX_OFFSET_TRAIL_SIZE) {
    out_of_memory();
  }
  stack->size = n;
  stack->data = (offset_trail_t *) safe_realloc(stack->data, n * sizeof(offset_trail_t));
}


/*
 * Push (np, nv, ptr) on top of the stack
 * - np = number of polynomials
 * - nv = number of variables
 * - ptr = propagation pointer
 */
static void offset_trail_push(offset_trail_stack_t *stack, uint32_t np, uint32_t nv, uint32_t ptr) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_offset_trail_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i].npolys = np;
  stack->data[i].nvars = nv;
  stack->data[i].prop_ptr = ptr;
  stack->top = i+1;
}


static inline offset_trail_t *offset_trail_top(offset_trail_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}


static inline void offset_trail_pop(offset_trail_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}


static inline void reset_offset_trail_stack(offset_trail_stack_t *stack) {
  stack->top = 0;
}

static void delete_offset_trail_stack(offset_trail_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}




/*
 * EQUALITY QUEUE
 */

/*
 * Initialize: use default sizes
 */
static void init_offset_equeue(offset_equeue_t *queue) {
  offset_eq_t *tmp;
  uint32_t i, n;

  n = DEF_OFFSET_EQUEUE_SIZE;
  assert(n <= MAX_OFFSET_EQUEUE_SIZE);

  tmp = (offset_eq_t *) safe_malloc(n * sizeof(offset_eq_t));
  for (i=0; i<n; i++) {
    q_init(&tmp[i].offset);
  }

  queue->eq = tmp;
  queue->id = (int32_t *) safe_malloc(n * sizeof(int32_t));
  queue->prop_ptr = 0;
  queue->top = 0;
  queue->size = n;
}



/*
 * Increase the queue size (by 50%)
 */
static void extend_offset_equeue(offset_equeue_t *queue) {
  offset_eq_t *tmp;
  uint32_t i, n;

  n = queue->size + 1;
  n += (n >> 1);
  if (n > MAX_OFFSET_EQUEUE_SIZE) {
    out_of_memory();
  }

  tmp = (offset_eq_t *) safe_realloc(queue->eq, n * sizeof(offset_eq_t));
  for (i=queue->size; i<n; i++) {
    q_init(&tmp[i].offset);
  }

  queue->eq = tmp;
  queue->id = (int32_t *) safe_realloc(queue->id, n * sizeof(int32_t));
  queue->size = n;
}


/*
 * Push equality (x == y + c) into the queue, with the given id
 */
static void push_offset_equality(offset_equeue_t *queue, int32_t x, int32_t y, rational_t *c, int32_t id) {
  uint32_t i;

  i = queue->top;
  if (i == queue->size) {
    extend_offset_equeue(queue);
  }
  assert(i < queue->size);

  queue->eq[i].lhs = x;
  queue->eq[i].rhs = y;
  q_set(&queue->eq[i].offset, c);
  queue->id[i] = id;

  queue->top = i + 1;
}


/*
 * Delete the queue
 */
static void delete_offset_equeue(offset_equeue_t *queue) {
  uint32_t i, n;

  n = queue->size;
  for (i=0; i<n; i++) {
    q_clear(&queue->eq[i].offset);
  }

  safe_free(queue->eq);
  safe_free(queue->id);

  queue->eq = NULL;
  queue->id = NULL;
}


/*
 * Empty the queue
 */
static void reset_offset_equeue(offset_equeue_t *queue) {
  uint32_t i, n;

  n = queue->size;
  for (i=0; i<n; i++) {
    q_clear(&queue->eq[i].offset);
  }
  queue->prop_ptr = 0;
  queue->top = 0;
}



/*
 * FULL MANAGER
 */

/*
 * Initialize:
 * - ext = pointer to an external object
 * - f: callback called when an equality is detected
 */
void init_offset_manager(offset_manager_t *m, void *ext, eq_notifier_t f) {
  m->external = ext;
  m->notify_eq = f;
  m->base_level = 0;
  m->decision_level = 0;
  m->conflict_eq = -1;

  init_offset_poly_table(&m->ptable);
  init_offset_table(&m->vtable);
  init_offset_hash_table(&m->htbl);
  init_offset_equeue(&m->queue);
  init_offset_undo_stack(&m->undo);
  init_inactive_poly_queue(&m->inactives);
  init_offset_level_stack(&m->stack);
  init_offset_trail_stack(&m->tstack);

  init_recheck_queue(&m->recheck);
  init_ivector(&m->to_process, 20);

  init_poly_buffer(&m->buffer1);
  init_poly_buffer(&m->buffer2);
  q_init(&m->aux);
}


/*
 * Delete
 */
void delete_offset_manager(offset_manager_t *m) {
  delete_offset_poly_table(&m->ptable);
  delete_offset_table(&m->vtable);
  delete_offset_hash_table(&m->htbl);
  delete_offset_equeue(&m->queue);
  delete_offset_undo_stack(&m->undo);
  delete_inactive_poly_queue(&m->inactives);
  delete_offset_level_stack(&m->stack);
  delete_offset_trail_stack(&m->tstack);

  delete_recheck_queue(&m->recheck);
  delete_ivector(&m->to_process);

  delete_poly_buffer(&m->buffer1);
  delete_poly_buffer(&m->buffer2);
  q_clear(&m->aux);
}


/*
 * Remove all content
 */
void reset_offset_manager(offset_manager_t *m) {
  m->base_level = 0;
  m->decision_level = 0;
  m->conflict_eq = -1;

  reset_offset_poly_table(&m->ptable);
  reset_offset_table(&m->vtable);
  reset_offset_hash_table(&m->htbl);
  reset_offset_equeue(&m->queue);
  reset_offset_undo_stack(&m->undo);
  reset_inactive_poly_queue(&m->inactives);
  reset_offset_trail_stack(&m->tstack);

  assert(m->stack.size > 0 &&
         m->stack.data[0].eq_ptr == 0 &&
         m->stack.data[0].undo_ptr == 0 &&
         m->stack.data[0].inactive_ptr == 0);

  reset_recheck_queue(&m->recheck);
  ivector_reset(&m->to_process);

  reset_poly_buffer(&m->buffer1);
  reset_poly_buffer(&m->buffer2);
  q_clear(&m->aux);
}



/*
 * POLYNOMIAL PROCESSING
 */

/*
 * Check whether polynomial k has the same normal form as b
 */
static bool matching_poly(offset_manager_t *m, poly_buffer_t *b, int32_t k) {
  polynomial_t *p;
  poly_buffer_t *b2;

  assert(0 <= k && k < m->ptable.npolys && b != &m->buffer2);

  b2 = &m->buffer2;
  p = m->ptable.def[k];
  poly_offset_normal_form(&m->vtable, b2, p);

  return equal_normal_forms(b, b2);
}


/*
 * Search for a polynomial equal to i in htbl
 * - b must contain the normal form of i
 * - h must be the hash code of b
 *
 * - if a matching polynomial is found, return its index
 * - otherwise, add a new record [i, h] in m->htbl and return i
 */
static int32_t get_equal_poly(offset_manager_t *m, int32_t i, uint32_t h, poly_buffer_t *b) {
  offset_hash_table_t *htbl;
  uint32_t j, k, mask;
  int32_t q;

  htbl = &m->htbl;
  mask = htbl->size - 1;
  j = h & mask;
  for (;;) {
    q = htbl->data[j].index;
    if (q == -1) goto add; // empty
    if (q == -2) break;    // deleted
    if (htbl->data[j].hash == h && matching_poly(m, b, q)) goto found;
    j ++;
    j &= mask;
  }

  // j is where we'll add [h, i] if necessary
  k = j;
  for (;;) {
    k ++;
    k &= mask;
    q = htbl->data[k].index;
    if (q == -1) break;
    if (q != -2 && htbl->data[j].hash == h && matching_poly(m, b, q)) goto found;
  }

  htbl->ndeleted --;

 add:
  // store the record in htbl->data[j]
  assert(htbl->data[j].index < 0);
  htbl->data[j].index = i;
  htbl->data[j].hash = h;
  htbl->nelems ++;
  if (htbl->nelems + htbl->ndeleted > htbl->resize_threshold) {
    offset_hash_table_extend(htbl);
  }
  q = i;

 found:
  return q;
}



/*
 * Initialize the dependency data for polynomial i
 * - compute the offset variables that i depend on and store them in vars[i]
 */
static void offset_poly_init_vars(offset_manager_t *m, int32_t i) {
  polynomial_t *p;
  monomial_t *mono;
  var_array_t *vars;
  uint32_t j, n;
  int32_t x;

  assert(0 <= i && i < m->ptable.npolys);

  vars = m->ptable.vars[i];

  if (vars != NULL) {
    p = m->ptable.def[i];
    n = p->nterms;
    mono = p->mono;

    if (mono[0].var == const_idx) {
      mono ++;
      n --;
    }

    assert(n > 0 && n == vars->size);

    for (j=0; j<n; j++) {
      x = mono[j].var;
      assert(x != const_idx);

      x = remap_find(&m->vtable.var2offset_var, x);
      vars->data[j].var = x;
      vars->data[j].idx = -1;
    }

    vars->ndeps = n;
  }
}


/*
 * Attach i to the dependency vectors
 * - for every record [x, -1] in vars[i] add i to dep[x] at some index k
 *   then update the record to [x, k]
 */
static void attach_offset_poly(offset_manager_t *m, int32_t i) {
  var_array_t *vars;
  uint32_t j, n;
  int32_t k, x;

  assert(0 <= i && i < m->ptable.npolys);

  vars = m->ptable.vars[i];
  if (vars != NULL) {
    n = vars->size;
    for (j=0; j<n; j++) {
      assert(vars->data[j].idx == -1);
      x = vars->data[j].var;
      k = offset_var_add_dep(&m->vtable, x, i);
      vars->data[j].idx = k;
    }
  }
}


/*
 * Remove poly i from the dependency vectors
 * - vars[i] contains pairs [x, k] where x an offset variable
 *   and k is an index in dep[x] such that dep[x]->data[k] = i
 * - to remove i from the dependency vectors:
 *   we set dep[x]->data[k] = -1 and we replace k by -1 in vars[i]
 */
static void detach_offset_poly(offset_manager_t *m, int32_t i) {
  var_array_t *vars;
  uint32_t j, n;
  int32_t k, x;

  assert(0 <= i && i < m->ptable.npolys);

  vars = m->ptable.vars[i];
  if (vars != NULL) {
    n = vars->size;
    for (j=0; j<n; j++) {
      x = vars->data[j].var;
      k = vars->data[j].idx;
      assert(offset_var_has_dep(&m->vtable, x, k, i));;
      offset_var_remove_dep(&m->vtable, x, k);
      vars->data[j].idx = -1;
    }
  }
}




/*
 * Send equality (i1 == i2) to the external solver
 * - i1 and i2 are polynomial indices
 */
static void report_equality(offset_manager_t *m, int32_t i1, int32_t i2) {
  eterm_t t1, t2;

  assert(0 <= i1 && i1 < m->ptable.npolys && 0 <= i2 && i2 < m->ptable.npolys && i1 != i2);

  t1 = m->ptable.eterm[i1];
  t2 = m->ptable.eterm[i2];
  m->notify_eq(m->external, t1, t2);
}


/*
 * Compute or recompute the normal form of polynomial i
 * - add i to the hash table if it's root of its equivalence class and mark i active
 * - if i is equal to another poly r already in the table, mark i inactive
 */
static void process_poly(offset_manager_t *m, int32_t i) {
  poly_buffer_t *b;
  polynomial_t *p;
  uint32_t h;
  int32_t r;

  assert(0 <= i && i < m->ptable.npolys);

  if (offset_poly_is_active(&m->ptable, i)) {
    // remove i from the hash table
    h  = m->ptable.hash[i];
    offset_hash_table_remove(&m->htbl, i, h);
    detach_offset_poly(m, i);
  }

  // compute p's normal form in b
  p = m->ptable.def[i];
  b = &m->buffer1;
  poly_offset_normal_form(&m->vtable, b, p);
  h = hash_normal_form(b);
  m->ptable.hash[i] = h;

  // search for a polynomial with the same normal form
  r = get_equal_poly(m, i, h, b);
  if (r == i) {
    // i is active
    mark_offset_poly_active(&m->ptable, i);
    attach_offset_poly(m, i);
  } else {
    // i is inactive: propagate the equality eterm[r] == eterm[i]
    mark_offset_poly_inactive(&m->ptable, i);
    inactive_poly_queue_push(&m->inactives, i);
    report_equality(m, i, r);
  }
}



/*
 * Record the triple (t, x, p) as a polynomial to monitor
 * - t = egraph term
 * - x = arithmetic variable (must be the theory variable of t)
 * - p = either x's definition or NULL
 *
 * If p is NULL, then the internal definition will be 1.x
 */
void record_offset_poly(offset_manager_t *m, eterm_t t, thvar_t x, polynomial_t *p) {
  int32_t i;

  if (p == NULL) {
    p = make_simple_poly(&m->ptable.pstore, x);
  }
  make_offset_vars_for_poly(&m->vtable, p);
  i = store_offset_poly(&m->ptable, t, x, p);
  //  attach_offset_poly(m, i);
  offset_poly_init_vars(m, i);

  assert(offset_poly_is_inactive(&m->ptable, i) &&
         !offset_poly_is_marked(&m->ptable, i));

  // add i to the to_process vector and to the recheck queue if needed
  ivector_push(&m->to_process, i);
  mark_offset_poly(&m->ptable, i);

  if (m->base_level < m->decision_level) {
    push_to_recheck(&m->recheck, m->decision_level, i);
  }
}



/*
 * Add polynomial i to the 'to_process' queue if it's not there already
 */
static void push_to_process(offset_manager_t *m, int32_t i) {
  if (!offset_poly_is_marked(&m->ptable, i)) {
    ivector_push(&m->to_process, i);
    mark_offset_poly(&m->ptable, i);
  }
}


/*
 * Add all polynomials of v to vector 'to_process'
 */
static void collect_polys_to_process(offset_manager_t *m, dep_t *v) {
  uint32_t i, n;
  int32_t k;

  if (v != NULL) {
    n = v->nelems;
    for (i=0; i<n; i++) {
      k = v->data[i];
      if (k >= 0) {
        push_to_process(m, k);
      }
    }
  }
}



/*
 * EXPLANATION TREES
 */

/*
 * For an equality (x == y + k)
 * - return the variable that's not equal to z
 */
static int32_t offset_eq_other_var(offset_eq_t *eq, int32_t z) {
  assert(eq->lhs == z || eq->rhs == z);
  return eq->lhs ^ eq->rhs ^ z;
}


/*
 * Invert the branch from x to its root in the explanation tree
 */
static void offset_invert_branch(offset_manager_t *m, int32_t x) {
  int32_t *edge;
  offset_eq_t *eq;
  int32_t i, j;

  edge = m->vtable.edge;
  eq = m->queue.eq;
  i = -1;
  for (;;) {
    j = edge[x];
    edge[x] = i;
    if (j < 0) break; // root found
    x = offset_eq_other_var(eq + j, x);
    i = j;
  }
}


#ifndef NDEBUG
/*
 * Root of x's explanation tree
 */
static int32_t offset_explanation_root(offset_manager_t *m, int32_t x) {
  offset_table_t *vtbl;
  int32_t i;

  vtbl = &m->vtable;

  for (;;) {
    assert(0 <= x && x < vtbl->nvars);
    i = vtbl->edge[x];
    if (i < 0) break;
    x = offset_eq_other_var(m->queue.eq + i, x);
  }

  return x;
}
#endif




/*
 * Collect all equalities along the path from x to its root
 * - for each equality i, add i * 1 to buffer b
 *
 * NOTE: buffer interprets i=0 as the special marker const_idx.
 * This does not matter here.
 */
static void offset_explanation_add_branch(offset_manager_t *m, poly_buffer_t *b, int32_t x) {
  offset_table_t *vtbl;
  int32_t i;

  vtbl = &m->vtable;

  for (;;) {
    assert(0 <= x && x < vtbl->nvars);
    i = vtbl->edge[x];
    if (i < 0) break;
    poly_buffer_add_var(b, i);
    x = offset_eq_other_var(m->queue.eq + i, x);
  }
}

/*
 * Subtract branch
 */
static void offset_explanation_sub_branch(offset_manager_t *m, poly_buffer_t *b, int32_t x) {
  offset_table_t *vtbl;
  int32_t i;

  vtbl = &m->vtable;

  for (;;) {
    assert(0 <= x && x < vtbl->nvars);
    i = vtbl->edge[x];
    if (i < 0) break;
    poly_buffer_sub_var(b, i);
    x = offset_eq_other_var(m->queue.eq + i, x);
  }
}

/*
 * Add coeff * branch for buffer b
 */
static void offset_explanation_addmul_branch(offset_manager_t *m, poly_buffer_t *b, rational_t *coeff, int32_t x) {
  offset_table_t *vtbl;
  int32_t i;

  vtbl = &m->vtable;

  for (;;) {
    assert(0 <= x && x < vtbl->nvars);
    i = vtbl->edge[x];
    if (i < 0) break;
    poly_buffer_add_monomial(b, i, coeff);
    x = offset_eq_other_var(m->queue.eq + i, x);
  }
}


/*
 * Conflict explanation for equality eq
 * - the conflict is an equality (x == y + k) where x and y must be in the same class
 * - to build the explanation: we add the branch from x and subtract the branch from y to buffer b
 * - then we normalize b
 */
static void offset_explanation_for_conflict(offset_manager_t *m, poly_buffer_t *b, offset_eq_t *eq) {
  int32_t x, y;

  x = eq->lhs;
  y = eq->rhs;

  assert(0 <= x && x < m->vtable.nvars && 0 <= y && y < m->vtable.nvars);
  assert(m->vtable.desc[x].root == m->vtable.desc[y].root);

  reset_poly_buffer(b);
  offset_explanation_add_branch(m, b, x);
  offset_explanation_sub_branch(m, b, y);
  normalize_poly_buffer(b);
}


/*
 * Explanation for b1 == 0
 * - b1 must be normalized
 * - the explanation is stored in buffer b
 */
static void offset_explanation_for_zero(offset_manager_t *m, poly_buffer_t *b, poly_buffer_t *b1) {
  monomial_t *mono;
  uint32_t i, n;
  int32_t x, j;

  assert(b1 != b);

  n = poly_buffer_nterms(b1);
  mono = poly_buffer_mono(b1);

  reset_poly_buffer(b);

  // skip the constant of b1 if any
  i = 0;
  if (mono[0].var == const_idx) {
    i = 1;
  }

  while (i<n) {
    assert(mono[i].var != const_idx);
    x = mono[i].var;
    j = remap_find(&m->vtable.var2offset_var, x);
    offset_explanation_addmul_branch(m, b, &mono[i].coeff, j);
    i ++;
  }
  normalize_poly_buffer(b);
}



/*
 * Collect all edge that occur in b with a non-zero coefficient
 * - b must be normalized
 * - add the corresponding id to vector v
 *
 * NOTE: we don't treat index 0 = const_idx in a special way here
 */
static void collect_edges_of_poly(offset_manager_t *m, poly_buffer_t *b, ivector_t *v) {
  monomial_t *mono;
  uint32_t i, n;
  int32_t k;

  n = poly_buffer_nterms(b);
  mono = poly_buffer_mono(b);

  for (i=0; i<n; i++) {
    k = mono[i].var;
    assert(q_is_nonzero(&mono[i].coeff) && 0 <= k && k < m->queue.top);
    ivector_push(v, m->queue.id[k]);
  }
}


/*
 * Explanation for a conflict
 */
void offset_manager_explain_conflict(offset_manager_t *m, ivector_t *v) {
  poly_buffer_t *b;
  offset_eq_t *eq;
  int32_t c;

  c = m->conflict_eq;

  assert(0 <= c && c < m->queue.top);

  b = &m->buffer1;
  eq = m->queue.eq + c;
  ivector_push(v, m->queue.id[c]);
  offset_explanation_for_conflict(m, b, eq);
  collect_edges_of_poly(m, b, v);
}



/*
 * Explanation for (x == y)
 * - x and y must be present in the internal poly table
 *   and they must have equal normal form
 * - this function collect the ids of equalities that imply x == y into vector v
 *   (v is not reset)
 */
void offset_manager_explain_equality(offset_manager_t *m, thvar_t x, thvar_t y, ivector_t *v) {
  offset_poly_table_t *ptbl;
  poly_buffer_t *b, *b1;
  int32_t px, py;

  ptbl = &m->ptable;
  px = remap_find(&ptbl->var2poly, x);
  py = remap_find(&ptbl->var2poly, y);

  assert(0 <= px && px < ptbl->npolys && 0 <= py && py < ptbl->npolys);

  // compute poly[px] - poly[py] in b1
  b1 = &m->buffer1;
  reset_poly_buffer(b1);
  poly_buffer_add_poly(b1, ptbl->def[px]);
  poly_buffer_sub_poly(b1, ptbl->def[py]);
  normalize_poly_buffer(b1);

  // build the explanation for b1 == 0 in b
  b = &m->buffer2;
  offset_explanation_for_zero(m, b, b1);
  collect_edges_of_poly(m, b, v);
}


/*
 * EQUALITIES
 */

/*
 * Process equality x == y + k
 * - i = the corresponding index in equality queue
 * - returns false if a conflict is detected, true otherwise
 */
static bool process_offset_equality(offset_manager_t *m, int32_t x, int32_t y, rational_t *k, int32_t i ) {
  offset_table_t *vtbl;
  offset_desc_t *dx, *dy;
  rational_t *delta;
  int32_t rx, ry;
  int32_t z;

  vtbl = &m->vtable;

  assert(0 <= x && x < vtbl->nvars && 0 <= y && y < vtbl->nvars && i >= 0);

  /*
   * x is [root1 + delta1]
   * y is [root2 + delta2]
   * so (x == y + k) is equivalent to root1 == root2 + delta2 - delta1 + k
   */
  dx = vtbl->desc + x;
  dy = vtbl->desc + y;

  rx = dx->root;   // root1
  ry = dy->root;   // root2
  delta = &m->aux;
  q_set(delta, &dy->offset);
  q_sub(delta, &dx->offset);
  q_add(delta, k);  // delta2 - delta1 + k

  if (rx == ry) {
    if (q_is_nonzero(delta)) {
      return false;
    }
  } else {
    /*
     * Swap rx and ry: we want to force lhs /= 0
     * Otherwise, we take as lhs the variable with smallest dep vector
     */
    if (rx == 0 ||
        (ry != 0 && offset_var_dep_size(vtbl, rx) > offset_var_dep_size(vtbl, ry))) {
      z = rx; rx = ry; ry = z;
      // z = x; x = y; y = z;
      x = y;
      q_neg(delta);
    }

    assert(rx != 0);

    // save (x, rx)
    offset_undo_push(&m->undo, x, rx);

    // Update the explanation tree: make x root then add an edge from x to y (labeled by i)
    assert(offset_explanation_root(m, x) == rx);
    offset_invert_branch(m, x);
    assert(vtbl->edge[x] == -1);
    vtbl->edge[x] = i;

    /*
     * Update the descriptors in rx's class + collect all polynomials
     * that depend on variables in rx's class
     */
    z = rx;
    do {
      dx = vtbl->desc  + z;
      assert(dx->root == rx);
      dx->root = ry;
      q_add(&dx->offset, delta);
      collect_polys_to_process(m, vtbl->dep[z]);

      z = dx->next;
    } while (z != rx);

    /*
     * Merge the circular lists: swap the desc[rx].next and desc[ry].next
     */
    z = vtbl->desc[rx].next;
    vtbl->desc[rx].next = vtbl->desc[ry].next;
    vtbl->desc[ry].next = z;
  }

  return true;
}


/*
 * Push equality (x == y + k) into the queue
 * - id = unique id for this equality
 * - if y is -1, the assertion is interpreted as x == k
 * - if x is -1. the assertion is interpreted as y + k == 0
 * - otherwise both x and y must be arithmetic variables.
 * - the equality is ignored if x or y are not mapped to an offset variable in m
 */
void assert_offset_equality(offset_manager_t *m, thvar_t x, thvar_t y, rational_t *k, int32_t id) {
  offset_table_t *vtbl;
  int32_t xx, yy;

  vtbl = &m->vtable;

  // replace x and y by the matching offset variables
  xx = (x < 0) ? 0 : remap_get(&vtbl->var2offset_var, x);
  yy = (y < 0) ? 0 : remap_get(&vtbl->var2offset_var, y);
  if (xx >= 0 && yy >= 0) {
    assert(xx < vtbl->nvars && yy < vtbl->nvars);
    push_offset_equality(&m->queue, xx, yy, k, id);
  }
}


/*
 * After propagate: if no conflict is found, process all polys in m->to_process
 * then empty the queue.
 */
static void reprocess_polys(offset_manager_t *m) {
  ivector_t *v;
  uint32_t i, n;
  int32_t k;

  v = &m->to_process;
  n = v->size;
  for (i=0; i<n; i++) {
    k = v->data[i];
    assert(offset_poly_is_marked(&m->ptable, k));
    process_poly(m, k);
    offset_poly_clear_mark(&m->ptable, k);
  }

  ivector_reset(v);
}



/*
 * Propagate:
 * - process all equalities in the queue
 * - compute normal form of all polynomials in the to_process queue
 */
bool offset_manager_propagate(offset_manager_t *m) {
  offset_eq_t *eq;
  uint32_t i, n;

  i = m->queue.prop_ptr;
  n = m->queue.top;
  while (i < n) {
    eq = m->queue.eq + i;
    if (! process_offset_equality(m, eq->lhs, eq->rhs, &eq->offset, i)) {
      // conflict
      m->conflict_eq = i;
      m->queue.prop_ptr = i;
      return false;
    }
    i ++;
  }

  m->queue.prop_ptr = i;

  reprocess_polys(m);
  assert(m->to_process.size == 0);

  return true;
}


/*
 * Increase the decision level:
 * - save the current top of queue, undo, and inactive queue
 */
void offset_manager_increase_decision_level(offset_manager_t *m) {
  uint32_t k;

  k = m->decision_level + 1;
  m->decision_level = k;

  if (m->stack.size == k) {
    extend_offset_level_stack(&m->stack);
  }
  assert(k < m->stack.size);
  m->stack.data[k].eq_ptr = m->queue.top;
  m->stack.data[k].undo_ptr = m->undo.top;
  m->stack.data[k].inactive_ptr = m->inactives.top;
}



/*
 * BACKTRACKING
 */

/*
 * Undo equality
 * - d = undo record for this equality:
 *   d->saved_var = variable x that was eliminated
 *   d->saved_root = root of x before the equality was processed
 */
static void undo_offset_equality(offset_manager_t *m, offset_undo_t *d) {
  offset_table_t *vtbl;
  offset_desc_t *dz;
  int32_t x, rx, ry, z;

  vtbl = &m->vtable;

  x = d->saved_var;
  rx = d->saved_root;
  assert(0 <= x && x < vtbl->nvars && 0 <= rx && rx < vtbl->nvars);

  ry = vtbl->desc[x].root;
  assert(0 <= ry && ry < vtbl->nvars);
  assert(vtbl->desc[ry].root == ry && vtbl->desc[rx].root == ry);

  /*
   * The current descriptor of rx must be of the form ry + delta.
   * To undo the merge, we need delta.
   */
  q_set(&m->aux, &vtbl->desc[rx].offset);

  // split the circular lists:
  z = vtbl->desc[rx].next;
  vtbl->desc[rx].next = vtbl->desc[ry].next;
  vtbl->desc[ry].next = z;

  // restore the offset descriptors in rx's class
  // and collect all polynomials that depend on variables in rx's class
  z = rx;
  do {
    dz = vtbl->desc + z;
    assert(dz->root == ry);
    dz->root = rx;
    q_sub(&dz->offset, &m->aux);
    collect_polys_to_process(m, vtbl->dep[z]);
    z = dz->next;
  } while (z != rx);

  // clear edge[x] then restore the branch from rx to x
  vtbl->edge[x] = -1;
  offset_invert_branch(m, rx);
  assert(offset_explanation_root(m, x) == rx);
}


/*
 * Scan the recheck queue after backtracking to level k
 * - any polynomial that was added at level > k is moved to the 'to_process' vector
 * - if k is base_level, remove all records with higher level from the queue
 */
static void process_recheck_queue(offset_manager_t *m, uint32_t k) {
  recheck_queue_t *queue;
  uint32_t i;
  int32_t q;

  assert(k >= m->base_level);

  queue = &m->recheck;
  i = queue->top;

  if (k > m->base_level) {
    while (i > 0 && queue->data[i-1].level > k) {
      i --;
      q = queue->data[i].id;
      push_to_process(m, q);
    }
  } else {
    // remove records of level >= k
    while (i > 0 && queue->data[i-1].level >= k) {
      i --;
    }
    queue->top = i;
  }
}


/*
 * Backtrack to level k
 */
void offset_manager_backtrack(offset_manager_t *m, uint32_t k) {
  level_record_t *lev;
  offset_undo_stack_t *undo;
  inactive_poly_queue_t *inactives;
  uint32_t back, i;

  assert(k < m->decision_level && k + 1 < m->stack.size);

  lev = m->stack.data + (k + 1);

  // clear conflict if any
  m->conflict_eq = -1;

  // clean up the equality queue
  m->queue.top = lev->eq_ptr;
  m->queue.prop_ptr = lev->eq_ptr;

  // undo all merges
  undo = &m->undo;
  back = lev->undo_ptr;
  i = undo->top;
  while (i > back) {
    i --;
    undo_offset_equality(m, undo->data + i);
  }
  undo->top = back;

  // process the inactive polys
  inactives = &m->inactives;
  back = lev->inactive_ptr;
  i = inactives->top;
  while (i > back) {
    i --;
    push_to_process(m, inactives->data[i]);
  }
  inactives->top = back;

  process_recheck_queue(m, k);

  m->decision_level = k;
}



/*
 * Start a new base level
 */
void offset_manager_push(offset_manager_t *m) {
  uint32_t np, nv, ptr;

  assert(m->base_level == m->decision_level);

  np = m->ptable.npolys;
  nv = m->vtable.nvars;
  ptr = m->queue.prop_ptr;

  offset_trail_push(&m->tstack, np, nv, ptr);

  offset_manager_increase_decision_level(m);

  m->base_level ++;
}



/*
 * Remove all polys of index >= np
 */
static void cleanup_process_vector(offset_manager_t *m, uint32_t np) {
  ivector_t *v;
  uint32_t i, j, n;
  int32_t id;

  v = &m->to_process;
  n = v->size;
  j = 0;
  for (i=0; i<n; i++) {
    id = v->data[i];
    if (id < np) {
      assert(offset_poly_is_marked(&m->ptable, id));
      v->data[j] = id;
      j ++;
    }
  }

  v->size = j;
}


static void remove_offset_polys(offset_manager_t *m, uint32_t np) {
  offset_poly_table_t *table;
  polynomial_t *p;
  uint32_t i, n, h;

  table = &m->ptable;

  assert(np <= table->npolys);

  n = table->npolys;
  for (i=np; i<n; i++) {
    if (offset_poly_is_active(table, i)) {
      h = m->ptable.hash[i];
      offset_hash_table_remove(&m->htbl, i, h);
      detach_offset_poly(m, i);
    }
    safe_free(table->vars[i]);
    p = table->def[i];
    if (offset_poly_is_simple(table, p, i)) {
      free_simple_poly(&table->pstore, p);
    }
  }

  table->npolys = np;
  remap_cleanup(&table->var2poly, np);
}



/*
 * Return to the previous base level
 */
void offset_manager_pop(offset_manager_t *m) {
  offset_trail_t *trail;

  assert(m->base_level > 0 && m->base_level == m->decision_level);

  m->base_level --;
  offset_manager_backtrack(m, m->base_level);
  trail = offset_trail_top(&m->tstack);

  remove_offset_polys(m, trail->npolys);
  cleanup_process_vector(m, trail->npolys);
  remove_offset_vars(&m->vtable, trail->nvars);
  m->queue.prop_ptr = trail->prop_ptr;

  offset_trail_pop(&m->tstack);

  assert(m->conflict_eq == -1);
}

