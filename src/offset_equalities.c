/*
 * Support for handling arithmetic equalities of the form x = y + k
 * where x and y are variables and k is a constant.
 */

#include <assert.h>

#include "memalloc.h"
#include "index_vectors.h"
#include "offset_equalities.h"



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
    if (remap_get(&table->var2poly, x) == i) {
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
 * Remove all polys of index >= np
 */
static void remove_offset_polys(offset_poly_table_t *table, uint32_t np) {
  uint32_t i, n;
  polynomial_t *p;

  assert(np <= table->npolys);

  n = table->npolys;
  for (i=np; i<n; i++) {
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
 * Store a new poly in table
 * - t = egraph term
 * - x = arithmetic variable
 * - p = polynomial
 * - p must be non NULL, x must be valid variable
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
  clr_bit(table->mark, i);

  remap_set(&table->var2poly, x, i);

  table->npolys = i+1;

  return i;
}




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
  q_clear(&table->desc[x].offset);  // x := x + 0

  table->elim[x] = -1;
  table->dep[x] = NULL;
}


/*
 * Check whether x is a root variable
 */
static inline bool offset_var_is_root(offset_table_t *table, int32_t x) {
  assert(0 <= x && x < table->nvars);
  return table->elim[x] < 0;
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
  table->elim = (int32_t *) safe_malloc(n * sizeof(int32_t));
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
  safe_free(table->elim);
  safe_free(table->dep);

  delete_remap(&table->var2offset_var);

  table->desc = NULL;
  table->elim = NULL;
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

  assert(table->elim[0] < 0 && table->dep[0] == NULL && 
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
  table->elim = (int32_t *) safe_realloc(table->elim, n * sizeof(int32_t));
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


#if 0

// NOT USED
/*
 * Get the offset variable for arithmetic variable x
 * - create a new offset variable if nothing is mapped to x
 */
static int32_t get_offset_var(offset_table_t *table, thvar_t x) {
  int32_t i;

  i = remap_get(&table->var2offset_var, x);
  if (i< 0) {
    i = alloc_offset_var(table);
    remap_set(&table->var2offset_var, x, i);
  }

  return i;
}

#endif


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
}



/*
 * Add i in the depency vector of x
 * - return the index k where is is stored (i.e., dep[x]->data[k] = i)
 */
static int32_t offset_var_add_dep(offset_table_t *table, int32_t x, int32_t i) {
  assert(0 < x && x < table->nvars); // x should never be the zero variable
  return dep_vector_add(table->dep + x, i);
}



/*
 * Remove the depent stored at index k in dep[x]
 */
static void offset_var_remove_dep(offset_table_t *table, int32_t x, int32_t k) {
  assert(0 < x && x < table->nvars);
  dep_vector_free_slot(table->dep[x], k);
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

  init_poly_buffer(&table->buffer);
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

  reset_poly_buffer(&table->buffer);
}



/*
 * Delete the table
 */
static void delete_offset_hash_table(offset_hash_table_t *table) {
  safe_free(table->data);
  table->data = NULL;
  delete_poly_buffer(&table->buffer);
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
 * - h = hahs code for i
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
  table->ndeleted --;
  if (table->ndeleted > table->cleanup_threshold) {
    offset_hash_table_cleanup(table);
  }
}


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






/*
 * TRAIL STACK
 */

/*
 * Initialize
 */
static void init_offset_trail_stack(offset_trail_stack_t *stack) {
  uint32_t n;

  n = DEF_OFFSET_TRAIL_SIZE;
  assert(n <= MAX_OFFSET_TRAIL_SIZE);

  stack->data = (offset_trail_t *) safe_malloc(n * sizeof(offset_trail_t));
  stack->top = 0;
  stack->size = n;
}


/*
 * Make the stack larger
 */
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


/*
 * Get the top record
 */
static inline offset_trail_t *offset_trail_top(offset_trail_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}


/*
 * Remove the top record
 */
static inline void offset_trail_pop(offset_trail_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}


/*
 * Empty the stack
 */
static inline void reset_offset_trail_stack(offset_trail_stack_t *stack) {
  stack->top = 0;
}


/*
 * Delete stack
 */
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
  queue->top = 0;
  queue->prop_ptr = 0;
  queue->size = n;

  n = DEF_OFFSET_EQUEUE_LEVELS;
  assert(n <= MAX_OFFSET_EQUEUE_LEVELS);

  queue->level_index = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  queue->level_index[0] = 0;
  queue->nlevels = 0;
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
 * Make the level_index array 50% larger
 */
static void increase_offset_equeue_levels(offset_equeue_t *queue) {
  uint32_t n;

  n = queue->nlevels + 1;
  n += (n >> 1);
  if (n > MAX_OFFSET_EQUEUE_LEVELS) {
    out_of_memory();
  }

  queue->level_index = (uint32_t *) safe_realloc(queue->level_index, n * sizeof(uint32_t));;
  queue->nlevels = n;
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
  safe_free(queue->level_index);
  queue->eq = NULL;
  queue->id = NULL;
  queue->level_index = NULL;
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

  queue->top = 0;
  queue->prop_ptr = 0;
  queue->level_index[0] = 0;
}



/*
 * FULL MANAGER
 */

/*
 * Initialize
 */
void init_offset_manager(offset_manager_t *m, egraph_t *egraph) {
  m->egraph = egraph;
  m->base_level = 0;
  m->decision_level = 0;

  init_offset_poly_table(&m->ptable);
  init_offset_table(&m->vtable);
  init_offset_hash_table(&m->htbl);
  init_offset_equeue(&m->queue);
  init_offset_trail_stack(&m->tstack);

  init_poly_buffer(&m->buffer);
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
  delete_offset_trail_stack(&m->tstack);

  delete_poly_buffer(&m->buffer);
  q_clear(&m->aux);
}


/*
 * Remove all content
 */
void reset_offset_manager(offset_manager_t *m) {
  reset_offset_poly_table(&m->ptable);
  reset_offset_table(&m->vtable);
  reset_offset_hash_table(&m->htbl);
  reset_offset_equeue(&m->queue);
  reset_offset_trail_stack(&m->tstack);

  reset_poly_buffer(&m->buffer);
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

  assert(0 <= k && k < m->ptable.npolys);

  b2 = &m->htbl.buffer;
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
 * Set dependency data for polynomial i
 * - b must be the normal form of i
 */
static void attach_offset_poly(offset_manager_t *m, int32_t i, poly_buffer_t *b) {
  monomial_t *mono;
  var_array_t *vars;
  uint32_t j, n;
  int32_t k, x;

  assert(0 <= i && i < m->ptable.npolys);

  vars = m->ptable.vars[i];

  n = poly_buffer_nterms(b);
  if (n == 0) {
    vars->ndeps = 0;
    return;
  }

  mono = poly_buffer_mono(b);
  if (mono[0].var == const_idx) {
    // skip the constant
    mono ++;
    n --;
  }

  assert(n <= vars->size);

  for (j=0; j<n; j++) {
    x = mono[j].var;
    k = offset_var_add_dep(&m->vtable, x, i);
    vars->data[j].var = x;
    vars->data[j].idx = k;
  }
  vars->ndeps = n;  
}



/*
 * Remove i from the dependency vectors of root variables
 * - then clear vars[i]
 */
static void detach_offset_poly(offset_manager_t *m, int32_t i) {
  var_array_t *vars;
  uint32_t j, n;
  int32_t k, x;

  assert(0 <= i && i < m->ptable.npolys);

  vars = m->ptable.vars[i];
  n = vars->ndeps;
  for (j=0; j<n; j++) {
    x = vars->data[j].var;
    k = vars->data[j].idx;

    assert(0 <= k && k < m->vtable.dep[x]->nelems && m->vtable.dep[x]->data[k] == i);

    if (offset_var_is_root(&m->vtable, x)) {
      offset_var_remove_dep(&m->vtable, x, k);
    }
  }

  vars->ndeps = 0;  
}


/*
 * Add polynomial i to the dependency structures and the hash table
 * - this is called just after i is added to the poly table
 * - all variables of i are mapped to offset variables
 */
static void process_new_poly(offset_manager_t *m, int32_t i) {
  poly_buffer_t *b;
  polynomial_t *p;
  uint32_t h;
  int32_t r;

  assert(0 <= i && i < m->ptable.npolys);

  p = m->ptable.def[i];
  b = &m->buffer;

  // compute p's normal form in b
  poly_offset_normal_form(&m->vtable, b, p);
  h = hash_normal_form(b);
  m->ptable.hash[i] = h;

  // search for a polynomial with the same normal form
  r = get_equal_poly(m, i, h, b);
  if (r == i) {
    // set dependencies for i
    attach_offset_poly(m, i, b);
  } else {
    // send the equality eterm[r] == eterm[i] to the Egraph
  }
}



/*
 * Revisit polynomial i after its normal form has changed
 */
static void revisit_poly(offset_manager_t *m, int32_t i) {
  poly_buffer_t *b;
  polynomial_t *p;
  uint32_t h;
  int32_t r;

  assert(0 <= i && i < m->ptable.npolys);

  // remove i from the hash table and dependency vectors
  h  = m->ptable.hash[i];
  offset_hash_table_remove(&m->htbl, i, h);
  detach_offset_poly(m, i);

  // recompute i's normal form
  p = m->ptable.def[i];
  b = &m->buffer;
  poly_offset_normal_form(&m->vtable, b, p);
  h = hash_normal_form(b);
  m->ptable.hash[i] = h;

  // search for a matching polynomial
  r = get_equal_poly(m, i, h, b);
  if (r == i) {
    // set dependencies for u
    attach_offset_poly(m, i, b);
  } else {
    // new equality discoverd: i == r
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

  assert(m->base_level == m->decision_level); // We'll have to address out-of-order addition later

  if (p == NULL) {
    p = make_simple_poly(&m->ptable.pstore, x);
  }
  make_offset_vars_for_poly(&m->vtable, p);
  i = store_offset_poly(&m->ptable, t, x, p);
  process_new_poly(m, i);
}




/*
 * Push equality (x == y + k) into the queue
 * - id = unique id for this equality
 * - if y is -1, the assertion is interpreted as x == k
 * - otherwise both x and y must be arithmetic variables.
 * - the equality is ignored if x or y are not mapped to an offset variable in m
 */
void assert_offset_equality(offset_manager_t *m, thvar_t x, thvar_t y, rational_t *k, int32_t id) {
  int32_t xx, yy;

  // replace x and y by the matching offset equalities
  xx = (x < 0) ? 0 : remap_get(&m->vtable.var2offset_var, x);
  yy = (y < 0) ? 0 : remap_get(&m->vtable.var2offset_var, y);
  if (xx >= 0 && yy >= 0) {
    assert(xx < m->vtable.nvars && yy < m->vtable.nvars);
    push_offset_equality(&m->queue, xx, yy, k, id);
  }
}





/*
 * Increase the decision level
 * - the propagation queue should be empty
 */
void offset_manager_increase_decision_level(offset_manager_t *m) {
  uint32_t k;

  assert(m->queue.prop_ptr == m->queue.top);

  k = m->decision_level + 1;
  m->decision_level = k;
  if (m->queue.nlevels == k) {
    increase_offset_equeue_levels(&m->queue);
  }
  assert(k < m->queue.nlevels);
  m->queue.level_index[k] = m->queue.top;
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
 * Return the the previous base level
 */
void offset_manager_pop(offset_manager_t *m) {
  offset_trail_t *trail;

  assert(m->base_level > 0 && m->base_level == m->decision_level);
  
  m->base_level --;
  offset_manager_backtrack(m, m->base_level);

  trail = offset_trail_top(&m->tstack);
  remove_offset_polys(&m->ptable, trail->npolys);
  remove_offset_vars(&m->vtable, trail->nvars);
  m->queue.prop_ptr = trail->prop_ptr;

  offset_trail_pop(&m->tstack);
}


