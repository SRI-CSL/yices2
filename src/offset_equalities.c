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
static dep_array_t *new_dep_array(uint32_t n) {
  dep_array_t *tmp;

  tmp = NULL;
  if (n > 0) {
    if (n > MAX_DEP_ARRAY_SIZE) {
      out_of_memory();
    }

    tmp = (dep_array_t *) safe_malloc(sizeof(dep_array_t) + n * sizeof(dep_rec_t));
    tmp->size = n;
    tmp->ndeps = 0;
  }

  return tmp;
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
    table->vars = (dep_array_t **) safe_malloc(n * sizeof(dep_array_t *));
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
    table->vars = (dep_array_t **) safe_realloc(table->vars, n * sizeof(dep_array_t *));
    table->mark = extend_bitvector(table->mark, n);

    table->size = n;
  }
}


/*
 * Empty the table
 */
static void reset_offfset_poly_table(offset_poly_table_t *table) {
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

  assert(p != NULL && const_idx < x && x < max_idx);

  i = table->npolys;
  if (i == table->size) {
    extend_offset_poly_table(table);
  }
  assert(i < table->size);

  table->eterm[i] = t;
  table->def[i] = p;
  table->vars[i] = new_dep_array(poly_num_vars(p));
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
  table->dep = (int32_t **) safe_malloc(n * sizeof(int32_t *));

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
    delete_index_vector(table->dep[i]);
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
    delete_index_vector(table->dep[i]);
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
  table->dep = (int32_t **) safe_realloc(table->dep, n * sizeof(int32_t *));
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


