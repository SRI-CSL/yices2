/*
 * Table of variables for arithmetic solvers
 *
 * This table maps theory variables within an arithmetic
 * solver to their definition and to the attached eterm if any.
 * It also supports hash-consing and removal of variables for push/pop
 * The table is intended primarily for the Simplex solver,
 * but it should be usable by future variants.
 *
 * More precisely, for each arithmetic variable v, the table stores
 * - the definition of v, which can be 
 *    either NULL
 *    or a pointer to a polynomial_t object
 *    or a pointer to a varprod_t object (for non-linear arithmetic)
 * - whether v is an integer or a real variable
 * - the egraph term attached to v (or null_eterm if there's none)
 * - a vector of atoms indices (all the atoms whose variable is v)
 */

#include "memalloc.h"
#include "hash_functions.h"
#include "arith_vartable.h"



/*
 * INITIALIZATION/DELETION/RESET
 */

/*
 * Initialization: use default sizes
 * - eterm_of is not allocated yet
 */
void init_arith_vartable(arith_vartable_t *table) {
  uint32_t n;
  
  n = DEF_AVARTABLE_SIZE;
  table->nvars = 0;
  table->ivars = 0;
  table->size = n;
  table->def = (void **) safe_malloc(n * sizeof(void *));
  table->i_flag = allocate_bitvector(n);
  table->atoms = (int32_t **) safe_malloc(n * sizeof(int32_t *));
  table->eterm_of = NULL;

  table->value = (xrational_t *) safe_malloc(n * sizeof(xrational_t));
  table->lower_index = (int32_t *) safe_malloc(n * sizeof(int32_t));
  table->upper_index = (int32_t *) safe_malloc(n * sizeof(int32_t));
  table->tag = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  
  init_int_htbl(&table->htbl, 0); // use the default size defined in int_hash_tables.h
}



/*
 * Increate the size by 50%
 */
static void extend_arith_vartable(arith_vartable_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;

  if (n >= MAX_AVARTABLE_SIZE) {
    out_of_memory();
  }
  
  table->size = n;
  table->def = (void **) safe_realloc(table->def, n * sizeof(void *));
  table->i_flag = extend_bitvector(table->i_flag, n);
  table->atoms = (int32_t **) safe_realloc(table->atoms, n * sizeof(int32_t *));
  if (table->eterm_of != NULL) {
    table->eterm_of = (eterm_t *) safe_realloc(table->eterm_of, n * sizeof(eterm_t));
  }

  table->value = (xrational_t *) safe_realloc(table->value, n * sizeof(xrational_t));
  table->lower_index = (int32_t *) safe_realloc(table->lower_index, n * sizeof(int32_t));
  table->upper_index = (int32_t *) safe_realloc(table->upper_index, n * sizeof(int32_t));
  table->tag = (uint8_t *) safe_realloc(table->tag, n * sizeof(uint8_t));
}



/*
 * Delete the table
 */
void delete_arith_vartable(arith_vartable_t *table) {
  uint32_t i, n;
  void *p;

  n = table->nvars;
  for (i=0; i<n; i++) {
    delete_index_vector(table->atoms[i]);
    xq_clear(table->value + i);
    p = table->def[i];
    if (p != NULL) {
      if (get_ptr_tag(p) == POLY_PTR_TAG) {
	free_polynomial(untag_poly_ptr(p));
      } else {
	assert(get_ptr_tag(p) == VARPROD_PTR_TAG);
	safe_free(untag_varprd_ptr(p));
      }
    }
  }


  safe_free(table->def);
  delete_bitvector(table->i_flag);
  safe_free(table->atoms);
  safe_free(table->eterm_of);
  safe_free(table->value);
  safe_free(table->lower_index);
  safe_free(table->upper_index);
  safe_free(table->tag);

  table->def = NULL;
  table->i_flag = NULL;
  table->atoms = NULL;
  table->eterm_of = NULL;
  table->value = NULL;
  table->lower_index = NULL;
  table->upper_index = NULL;
  table->tag = NULL;

  delete_int_htbl(&table->htbl);
}



/*
 * Reset table: delete all polynomials and products
 * - free all the extended rationals
 */
void reset_arith_vartable(arith_vartable_t *table) {
  uint32_t i, n;
  void *p;

  n = table->nvars;
  for (i=0; i<n; i++) {
    p = table->def[i];
    if (p != NULL) {
      if (get_ptr_tag(p) == POLY_PTR_TAG) {
	free_polynomial(untag_poly_ptr(p));
      } else {
	assert(get_ptr_tag(p) == VARPROD_PTR_TAG);
	safe_free(untag_varprd_ptr(p));
      }
    }
  }

  for (i=0; i<n; i++) {
    delete_index_vector(table->atoms[i]);
    xq_clear(table->value + i);
  }

  table->nvars = 0;
  table->ivars = 0;

  reset_int_htbl(&table->htbl);
}



/*
 * Remove all variables of index >= nvars
 */
void arith_vartable_remove_vars(arith_vartable_t *table, uint32_t nvars) {
  uint32_t i, n, k;
  void *p;
  polynomial_t *poly;
  varprod_t *vp;

  n = table->nvars;
  for (i=nvars; i<n; i++) {
    p = table->def[i];
    if (p != NULL) {
      if (get_ptr_tag(p) == POLY_PTR_TAG) {
	poly = untag_poly_ptr(p);
	// make sure the hash matches hash_poly(poly_hobj_t *o)
	k = hash_monarray(poly->mono); 
	int_htbl_erase_record(&table->htbl, k, i);
	free_polynomial(poly);

      } else {
	assert(get_ptr_tag(p) == VARPROD_PTR_TAG);
	vp = untag_varprd_ptr(p);
	// make sure this one matches hash_varprod(varprod_hobj_t *o)
	k = jenkins_hash_intarray(2 * vp->len, (int32_t *) vp->prod);
	int_htbl_erase_record(&table->htbl, k, i);
	safe_free(vp);
      }
    }

    if (tst_bit(table->i_flag, i)) {
      table->ivars --;
    }

    delete_index_vector(table->atoms[i]);
    xq_clear(table->value + i);

  }

  table->nvars = nvars;  
}


#if 0

/*
 * Get the number of integer variables in table
 */
uint32_t num_integer_vars(arith_vartable_t *table) {
  uint32_t i, n, t;

  t = 0;
  n = table->nvars;
  for (i=0; i<n; i++) {
    t += tst_bit(table->i_flag, i);
  }
  assert(t == table->ivars);
  return t;
}

#endif




/*
 * VARIABLE CREATION
 */

/*
 * Allocate a new variable: return its index v
 * - initialize def[v] to d
 * - initialize atoms[v] to NULL
 * - initialize value[v] to 0
 * - initialize lower_index[v] and upper_index[v] to -1
 * - initialize tag to 0
 * - i_flag[v] is 1 if is_int is true, 0 otherwise
 * - if eterm_of exists, then eterm_of[v] is initialized to null_eterm
 */
static thvar_t new_arith_var(arith_vartable_t *table, void *def, bool is_int) {
  uint32_t v;

  v = table->nvars;
  if (v == table->size) {
    extend_arith_vartable(table);
  }
  assert(v < table->size);
  table->def[v] = def;
  assign_bit(table->i_flag, v, is_int);
  table->atoms[v] = NULL;
  if (table->eterm_of != NULL) {
    table->eterm_of[v] = null_eterm;
  }

  xq_init(table->value + v);
  table->lower_index[v] = -1;
  table->upper_index[v] = -1;
  table->tag[v] = 0;

  table->nvars = v+1;
  table->ivars += is_int;

  return v;
}


/*
 * Create a new variable
 */
thvar_t create_arith_var(arith_vartable_t *table, bool is_int) {
  return new_arith_var(table, NULL, is_int);
}


/*
 * Attach eterm t to variable x
 */
void attach_eterm_to_arith_var(arith_vartable_t *table, thvar_t x, eterm_t t) {
  eterm_t *tmp;
  uint32_t i, n;

  assert(0 <= x && x < table->nvars && t != null_eterm);

  tmp = table->eterm_of;
  if (tmp == NULL) {
    n = table->size;
    tmp = (eterm_t *) safe_malloc(n * sizeof(eterm_t));
    n = table->nvars;
    for (i=0; i<n; i++) {
      tmp[i] = null_eterm;
    }
    table->eterm_of = tmp;
  }

  assert(tmp[x] == null_eterm);
  tmp[x] = t;
}


/*
 * Attach atom index i to atoms[x]
 * - i must not be in atoms[x]
 */
void attach_atom_to_arith_var(arith_vartable_t *table, thvar_t x, int32_t i) {
  assert(0 <= x && x < table->nvars && ! index_in_vector(table->atoms[x], i));
  add_index_to_vector(table->atoms + x, i);
}


/*
 * Remove atom index i from atoms[x]
 * - i must be in atoms[x]
 */
void detach_atom_from_arith_var(arith_vartable_t *table, thvar_t x, int32_t i) {
  assert(0 <= x && x < table->nvars && index_in_vector(table->atoms[x], i));
  remove_index_from_vector(table->atoms[x], i);
}






/*
 * HASH CONSING FOR PRODUCTS OF VARIABLES
 */

/*
 * Hash-consing object
 * - the definition is in array a = array of pairs <variable, exponent>
 * - len = length of array a
 * - a must be normalized (as defined in varproducts.c)
 */
typedef struct varprod_hobj_s {
  int_hobj_t m;
  arith_vartable_t *table;
  varexp_t *a;
  uint32_t len;
} varprod_hobj_t;

/*
 * Hash code for a product v
 * - o points to a hash consing object
 * - v must be stored in table->prod_buffer
 * - the buffer must be normalized
 */
static uint32_t hash_varprod(varprod_hobj_t *o) {
  return jenkins_hash_intarray(2 * o->len, (int32_t *) o->a);
}

/*
 * Check whether x is equal to the product in o
 * - o points to a hash consing object
 */
static bool eq_varprod(varprod_hobj_t *o, thvar_t x) {
  arith_vartable_t *table;
  void *p;
  varprod_t *prod;

  table = o->table;
  p = table->def[x];
  if (p == NULL || get_ptr_tag(p) != VARPROD_PTR_TAG) return false;

  prod = untag_varprd_ptr(p);
  return prod->len == o->len && varexp_array_equal(prod->prod, o->a, prod->len);
}


/*
 * Check whether all variables in product p are integer
 * - n = number of elements in p
 */
static bool integer_varexp(arith_vartable_t *table, varexp_t *p, uint32_t n) {
  uint32_t i;
  thvar_t x;

  for (i=0; i<n; i++) {
    x = p[i].var;
    assert(0 <= x && x < table->nvars);
    if (! tst_bit(table->i_flag, x)) return false;
  }
  return true;
}

/*
 * Build a new product and add it to the table
 * - o points to a hash consing object
 */
static thvar_t build_varprod(varprod_hobj_t *o) {
  arith_vartable_t *table;
  varprod_t *p;

  table = o->table;
  p = make_varprod(o->a, o->len);
  return new_arith_var(table, tag_varprod_ptr(p), integer_varexp(table, o->a, o->len));
}


/*
 * Hash consing object
 */
static varprod_hobj_t varprod_hobj = {
  { (hobj_hash_t) hash_varprod, (hobj_eq_t) eq_varprod, (hobj_build_t) build_varprod },
  NULL,
  NULL,
  0,
};



/*
 * Search for a variable whose definition is equal to p
 * - return null_thvar if there no such variable in the table
 */
thvar_t find_var_for_product(arith_vartable_t *table, varprod_t *p) {
  varprod_hobj.table = table;
  varprod_hobj.a = p->prod;
  varprod_hobj.len = p->len;
  /*
   * int_htbl_find_obj returns NULL_VALUE == -1 if the object is
   * not found. This is the same as null_thvar == -1.
   */
  return int_htbl_find_obj(&table->htbl, (int_hobj_t*) &varprod_hobj);
}


/*
 * Create the variable if needed
 */
thvar_t get_var_for_product(arith_vartable_t *table, varprod_t *p, bool *new_var) {
  uint32_t n;
  thvar_t x;

  n = table->nvars;
  varprod_hobj.table = table;
  varprod_hobj.a = p->prod;
  varprod_hobj.len = p->len;
  x = int_htbl_get_obj(&table->htbl, (int_hobj_t*) &varprod_hobj);
  *new_var = table->nvars > n;
  return x;
}
 

/*
 * Variants: input is stored in a vpbuffer rather than a varprod object
 */

/*
 * Search for a variable whose definition is equal to p
 * - return null_thvar if there no such variable in the table
 */
thvar_t find_var_for_vpbuffer(arith_vartable_t *table, vpbuffer_t *b) {
  varprod_hobj.table = table;
  varprod_hobj.a = b->prod;
  varprod_hobj.len = b->len;
  /*
   * int_htbl_find_obj returns NULL_VALUE == -1 if the object is
   * not found. This is the same as null_thvar == -1.
   */
  return int_htbl_find_obj(&table->htbl, (int_hobj_t*) &varprod_hobj);
}


/*
 * Create the variable if needed
 */
thvar_t get_var_for_vpbuffer(arith_vartable_t *table, vpbuffer_t *b, bool *new_var) {
  uint32_t n;
  thvar_t x;

  n = table->nvars;
  varprod_hobj.table = table;
  varprod_hobj.a = b->prod;
  varprod_hobj.len = b->len;
  x = int_htbl_get_obj(&table->htbl, (int_hobj_t*) &varprod_hobj);
  *new_var = table->nvars > n;
  return x;
}
 




/*
 * FIND/CREATE THE CONSTANT
 */

/*
 * Return -1 or a variable whose definition is the empty product
 */
thvar_t find_var_for_constant(arith_vartable_t *table) {
  varprod_hobj.table = table;
  varprod_hobj.a = NULL; // this is safe since len is 0
  varprod_hobj.len = 0;
  return int_htbl_find_obj(&table->htbl, (int_hobj_t *) &varprod_hobj);
}


/*
 * Create or find a variable whose definition is the empty product
 * - set *new_var to true if the variable is created
 * - otherwise, set it to false
 */
thvar_t get_var_for_constant(arith_vartable_t *table, bool *new_var) {
  uint32_t n;
  thvar_t x;

  n = table->nvars;
  varprod_hobj.table = table;
  varprod_hobj.a = NULL;
  varprod_hobj.len = 0;
  x = int_htbl_get_obj(&table->htbl, (int_hobj_t*) &varprod_hobj);
  *new_var = table->nvars > n;
  return x;
}



/*
 * HASH CONSING FOR POLYNOMIALS
 */

/*
 * Hash-consing object to interface with int_hash_table 
 * - the polynomial to create is in o->poly
 * - the polynomial must be normalized as defined by varsort in polynomials.h:
 *   all coefficients must be non-zero
 *   the polynomial must be terminated by a max_idx end-marker
 * - len must be the polynomial length, not including the end marker
 */
typedef struct poly_hobj_s {
  int_hobj_t m;
  arith_vartable_t *table;
  monomial_t *poly;
  uint32_t len;
} poly_hobj_t;


/*
 * Hash code for polynomial stored in o
 */
static uint32_t hash_poly(poly_hobj_t *o) {
  return hash_monarray(o->poly);
}

/*
 * Check whether x's def is equal to poly in o
 */
static bool eq_poly(poly_hobj_t *o, thvar_t x) {
  arith_vartable_t *table;
  void *p;

  table = o->table;
  p = table->def[x];
  if (p == NULL || get_ptr_tag(p) != POLY_PTR_TAG) return false;
  return equal_monarray(untag_poly_ptr(p)->mono, o->poly);
}



/*
 * Check whether all variables and coefficients of p are integer
 * - p must be normalized (sorted and terminated by max_idx)
 */
static bool integer_poly(arith_vartable_t *table, monomial_t *p) {
  thvar_t x;

  x = p->var;
  while (x < max_idx) {
    assert(0 <= x && x < table->nvars);
    if (! tst_bit(table->i_flag, x)) return false;
    if (! q_is_integer(&p->coeff)) return false;
    p ++;
    x = p->var;
  }
  return true;
}


/*
 * Build a new polynomial and add it to the table
 */
static thvar_t build_poly(poly_hobj_t *o) {
  arith_vartable_t *table;
  polynomial_t *p;

  table = o->table;
  p = monarray_copy(o->poly, o->len);
  return new_arith_var(table, tag_poly_ptr(p), integer_poly(table, p->mono));
}


/*
 * Hash-object for polynomials
 */
static poly_hobj_t poly_hobj = {
  { (hobj_hash_t) hash_poly, (hobj_eq_t) eq_poly, (hobj_build_t) build_poly },
  NULL,
  NULL,
  0,
};



/*
 * Find a variable whose definition is equal to polynomial p 
 * - if there's no such variable, return null_thvar = -1
 * - p must be normalized and all its variables must exist in table
 *   (i.e., p must have its variables sorted and it must be terminated 
 *    by the end-marker max_idx)
 * - n must be the length of p, excluding the end marker
 */
thvar_t find_var_for_poly(arith_vartable_t *table, monomial_t *p, uint32_t n) {
  poly_hobj.table = table;
  poly_hobj.poly = p;
  poly_hobj.len = n;
  return int_htbl_find_obj(&table->htbl, (int_hobj_t *) &poly_hobj);
}

/*
 * Get a variable whose definition is equal to p
 * - create a fresh variable if there's no such variable in the table
 * - if a new variable is created, the flag *new_var is set to true,
 * - if an existing variable is returned, then *new_var is set false
 */
thvar_t get_var_for_poly(arith_vartable_t *table, monomial_t *p, uint32_t n, bool *new_var) {
  uint32_t k;
  thvar_t x;

  k = table->nvars;
  poly_hobj.table = table;
  poly_hobj.poly = p;
  poly_hobj.len = n;
  x = int_htbl_get_obj(&table->htbl, (int_hobj_t*) &poly_hobj);
  *new_var = table->nvars > k;
  return x;
}


/*
 * Find a variable whose definition is equal to the non-constant part of p
 * - i.e., write p as k + q where k is the constant term, then find variable for q
 */
thvar_t find_var_for_poly_offset(arith_vartable_t *table, monomial_t *p, uint32_t n) {
  if (n > 0 && p->var == const_idx) {
    // skip the first monomial = constant term
    p ++;
    n --;
  }
  return find_var_for_poly(table, p, n);
}


/*
 * Get a variable whose definition is equal to the non-constant part of p
 * - i.e., write p as k + q where k is the constant term, then get variable for q
 */
thvar_t get_var_for_poly_offset(arith_vartable_t *table, monomial_t *p, uint32_t n, bool *new_var) {
  if (n > 0 && p->var == const_idx) {
    p ++;
    n --;
  }
  return get_var_for_poly(table, p, n, new_var);
}



