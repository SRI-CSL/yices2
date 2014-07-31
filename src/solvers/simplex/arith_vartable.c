/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

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

#include "utils/memalloc.h"
#include "utils/hash_functions.h"
#include "solvers/simplex/arith_vartable.h"



/*
 * HASH CODES
 */

/*
 * For power products, we use a hash function local to
 * this module (rather than relying on pprod_table).
 */
static inline uint32_t hash_pprod(varexp_t *p, uint32_t n) {
  return jenkins_hash_array((uint32_t *) p, 2 * n, 0x1238932f);
}

// variant
static inline uint32_t hash_pprod2(pprod_t *p) {
  return hash_pprod(p->prod, p->len);
}

/*
 * Hash code for rational q
 */
static uint32_t hash_rational(rational_t *q) {
  uint32_t num, den;

  q_hash_decompose(q, &num, &den);
  return jenkins_hash_pair(num, den, 0xf82fadbe);
}



/*
 * INITIALIZATION/DELETION/RESET
 */

/*
 * Initialization: use default sizes
 * - eterm is not allocated yet
 */
void init_arith_vartable(arith_vartable_t *table) {
  uint32_t n;

  n = DEF_AVARTABLE_SIZE;
  table->nvars = 0;
  table->ivars = 0;
  table->size = n;
  table->def = (void **) safe_malloc(n * sizeof(void *));
  table->atoms = (int32_t **) safe_malloc(n * sizeof(int32_t *));
  table->eterm = NULL;
  table->tag = (uint8_t *) safe_malloc(n * sizeof(uint8_t));

  table->value = (xrational_t *) safe_malloc(n * sizeof(xrational_t));
  table->lower_index = (int32_t *) safe_malloc(n * sizeof(int32_t));
  table->upper_index = (int32_t *) safe_malloc(n * sizeof(int32_t));

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
  table->atoms = (int32_t **) safe_realloc(table->atoms, n * sizeof(int32_t *));
  if (table->eterm != NULL) {
    table->eterm = (eterm_t *) safe_realloc(table->eterm, n * sizeof(eterm_t));
  }
  table->tag = (uint8_t *) safe_realloc(table->tag, n * sizeof(uint8_t));

  table->value = (xrational_t *) safe_realloc(table->value, n * sizeof(xrational_t));
  table->lower_index = (int32_t *) safe_realloc(table->lower_index, n * sizeof(int32_t));
  table->upper_index = (int32_t *) safe_realloc(table->upper_index, n * sizeof(int32_t));
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
    switch (arith_var_kind(table, i)) {
    case AVAR_FREE: // nothing to delete
      break;

    case AVAR_POLY:
      free_polynomial(p);
      break;

    case AVAR_PPROD:
      safe_free(p);
      break;

    case AVAR_CONST:
      q_clear(p);
      safe_free(p);
      break;
    }
  }


  safe_free(table->def);
  safe_free(table->atoms);
  safe_free(table->eterm);
  safe_free(table->tag);
  safe_free(table->value);
  safe_free(table->lower_index);
  safe_free(table->upper_index);

  table->def = NULL;
  table->atoms = NULL;
  table->eterm = NULL;
  table->tag = NULL;
  table->value = NULL;
  table->lower_index = NULL;
  table->upper_index = NULL;

  delete_int_htbl(&table->htbl);
}



/*
 * Reset table:
 * - delete all descriptors
 * - free all the extended rationals
 */
void reset_arith_vartable(arith_vartable_t *table) {
  uint32_t i, n;
  void *p;

  n = table->nvars;
  for (i=0; i<n; i++) {
    p = table->def[i];
    switch (arith_var_kind(table, i)) {
    case AVAR_FREE: // nothing to do
      break;

    case AVAR_POLY:
      free_polynomial(p);
      break;

    case AVAR_PPROD:
      safe_free(p);
      break;

    case AVAR_CONST:
      q_clear(p);
      safe_free(p);
      break;
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



#ifndef NDEBUG

/*
 * The number of integer variables in table
 */
uint32_t dbg_integer_vars(arith_vartable_t *table) {
  uint32_t i, n, t;

  t = 0;
  n = table->nvars;
  for (i=0; i<n; i++) {
    t += arith_var_is_int(table, i);
  }
  return t;
}

#endif




/*
 * Remove all variables of index >= nvars
 */
void arith_vartable_remove_vars(arith_vartable_t *table, uint32_t nvars) {
  uint32_t i, n, k;
  void *p;

  n = table->nvars;
  for (i=nvars; i<n; i++) {
    p = table->def[i];
    switch (arith_var_kind(table, i)) {
    case AVAR_FREE:
      break;

    case AVAR_POLY:
      k = hash_polynomial(p);
      int_htbl_erase_record(&table->htbl, k, i);
      free_polynomial(p);
      break;

    case AVAR_PPROD:
      k = hash_pprod2(p);
      int_htbl_erase_record(&table->htbl, k, i);
      safe_free(p);
      break;

    case AVAR_CONST:
      k = hash_rational(p);
      int_htbl_erase_record(&table->htbl, k, i);
      q_clear(p);
      safe_free(p);
      break;
    }

    table->ivars -= arith_var_is_int(table, i);

    delete_index_vector(table->atoms[i]);
    xq_clear(table->value + i);
  }

  table->nvars = nvars;

  assert(table->ivars == dbg_integer_vars(table));
}



/*
 * Remove all references to egraph terms of indices >= nterms
 */
void arith_vartable_remove_eterms(arith_vartable_t *table, uint32_t nterms) {
  eterm_t *tmp;
  uint32_t i, n;
  eterm_t t;

  tmp = table->eterm;

  if (tmp != NULL) {
    n = table->nvars;
    for (i=0; i<n; i++) {
      t = tmp[i];
      if (t != null_eterm && t >= nterms) {
        tmp[i] = null_eterm;
      }
    }
  }
}



/*
 * Collect the set of integer variables as a bit vector
 * - i.e., return a bitvector V of size n = table->nvars
 * - bit i of V is 1 if variable i has integer type.
 * - V must be deleted when no longer used by calling delete_bitvector(V)
 *   (cf. bitvectors.h)
 */
byte_t *get_integer_vars_vector(arith_vartable_t *table) {
  byte_t *v;
  uint32_t i, n;

  n = table->nvars;
  v = allocate_bitvector(n);
  for (i=0; i<n; i++) {
    assign_bit(v, i, arith_var_is_int(table, i));
  }

  return v;
}



/*
 * VARIABLE CREATION
 */

/*
 * Check whether the INT bit of tg is set
 */
static inline bool is_int_tag(uint8_t tg) {
  return (tg & AVARTAG_INT_MASK) != 0;
}

/*
 * Build a tag for the given kind + is_int flag
 * - bit 0, 1, 2 are 0: no mark
 */
static inline uint8_t mk_arith_vartag(avar_kind_t kind, bool is_int) {
  assert(AVAR_FREE <= kind && kind <= AVAR_CONST);
  assert(is_int == 0 || is_int == 1);
  return (uint8_t) ((kind << 4) | (is_int << 3));
}


/*
 * Allocate a new variable: return its index v
 * - initialize def[v] to d
 * - initialize atoms[v] to NULL
 * - initialize value[v] to 0
 * - initialize lower_index[v] and upper_index[v] to -1
 * - initialize tag to tg
 * - if eterm exists, then eterm[v] is initialized to null_eterm
 */
static thvar_t new_arith_var(arith_vartable_t *table, void *def, uint8_t tg) {
  uint32_t v;

  // all bits of tg except kind + int bits must be 0
  assert((tg & ~(AVARTAG_KIND_MASK|AVARTAG_INT_MASK)) == 0);

  v = table->nvars;
  if (v == table->size) {
    extend_arith_vartable(table);
  }
  assert(v < table->size);

  table->def[v] = def;
  table->atoms[v] = NULL;
  if (table->eterm != NULL) {
    table->eterm[v] = null_eterm;
  }
  table->tag[v] = tg;

  xq_init(table->value + v);
  table->lower_index[v] = -1;
  table->upper_index[v] = -1;

  table->nvars = v+1;
  table->ivars += is_int_tag(tg);

  return v;
}


/*
 * Create a new variable
 */
thvar_t create_arith_var(arith_vartable_t *table, bool is_int) {
  return new_arith_var(table, NULL, mk_arith_vartag(AVAR_FREE, is_int));
}


/*
 * Attach eterm t to variable x
 */
void attach_eterm_to_arith_var(arith_vartable_t *table, thvar_t x, eterm_t t) {
  eterm_t *tmp;
  uint32_t i, n;

  assert(0 <= x && x < table->nvars && t != null_eterm);

  tmp = table->eterm;
  if (tmp == NULL) {
    n = table->size;
    tmp = (eterm_t *) safe_malloc(n * sizeof(eterm_t));
    n = table->nvars;
    for (i=0; i<n; i++) {
      tmp[i] = null_eterm;
    }
    table->eterm = tmp;
  }

  assert(tmp[x] == null_eterm);
  tmp[x] = t;
}


/*
 * Check whether there's at least one variable with an attached eterm in table
 */
bool arith_vartable_has_eterms(arith_vartable_t *table) {
  uint32_t i, n;

  if (table->eterm != NULL) {
    n = table->nvars;
    for (i=0; i<n; i++) {
      if (table->eterm[i] != null_eterm) {
	return true;
      }
    }
  }
  return false;
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
 * HASH CONSING FOR RATIONAL CONSTANTS
 */

/*
 * Hash consing object (cf. int_hash_tables.h)
 */
typedef struct {
  int_hobj_t m;
  arith_vartable_t *table;
  rational_t *q;
} rational_hobj_t;


/*
 * Hash code/equality check/constructor
 */
static uint32_t hash_rational_hobj(rational_hobj_t *o) {
  return hash_rational(o->q);
}

static bool eq_rational_hobj(rational_hobj_t *o, thvar_t x) {
  arith_vartable_t *table;

  table = o->table;
  return arith_var_def_is_rational(table, x)
    && q_eq(arith_var_rational_def(table, x), o->q);
}

static thvar_t build_rational_hobj(rational_hobj_t *o) {
  arith_vartable_t *table;
  rational_t *a;

  table = o->table;
  a = (rational_t *) safe_malloc(sizeof(rational_t));
  q_init(a);
  q_set(a, o->q);

  return new_arith_var(table, a, mk_arith_vartag(AVAR_CONST, q_is_integer(a)));
}


/*
 * Hash consing object
 */
static rational_hobj_t rational_hobj = {
  { (hobj_hash_t) hash_rational_hobj, (hobj_eq_t) eq_rational_hobj, (hobj_build_t) build_rational_hobj },
  NULL,
  NULL,
};


/*
 * Return a variable equal to rational q
 * - return null_thvar if there's no such variable in table
 */
thvar_t find_var_for_constant(arith_vartable_t *table, rational_t *q) {
  rational_hobj.table = table;
  rational_hobj.q = q;
  return int_htbl_find_obj(&table->htbl, &rational_hobj.m);
}


/*
 * Create or find a variable whose definition is the empty product
 * - set *new_var to true if the variable is created
 * - otherwise, set it to false
 */
thvar_t get_var_for_constant(arith_vartable_t *table, rational_t *q, bool *new_var) {
  uint32_t nv;
  thvar_t x;

  nv = table->nvars;
  rational_hobj.table = table;
  rational_hobj.q = q;
  x = int_htbl_get_obj(&table->htbl, &rational_hobj.m);
  *new_var = table->nvars > nv;

  return x;
}




/*
 * HASH CONSING FOR POWER PRODUCTS
 */

/*
 * Hash-consing object
 * - the definition is in array a = array of pairs <variable, exponent>
 * - len = length of array a
 * - a must be normalized (as defined in power_products.c)
 */
typedef struct pprod_hobj_s {
  int_hobj_t m;
  arith_vartable_t *table;
  varexp_t *a;
  uint32_t len;
} pprod_hobj_t;


/*
 * Hash code for a product v
 * - o points to a hash consing object
 * - v must be stored in table->prod_buffer
 * - the buffer must be normalized
 */
static uint32_t hash_pprod_hobj(pprod_hobj_t *o) {
  return hash_pprod(o->a, o->len);
}

/*
 * Check whether x is equal to the product in o
 * - o points to a hash consing object
 */
static bool eq_pprod_hobj(pprod_hobj_t *o, thvar_t x) {
  arith_vartable_t *table;
  pprod_t *p;

  table = o->table;
  if (arith_var_def_is_product(table, x)) {
    p = arith_var_product_def(table, x);
    return p->len == o->len && varexp_array_equal(p->prod, o->a, p->len);
  }

  return false;
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
    if (! arith_var_is_int(table, x)) {
      return false;
    }
  }
  return true;
}


/*
 * Build a new product and add it to the table
 * - o points to a hash consing object
 */
static thvar_t build_pprod_hobj(pprod_hobj_t *o) {
  arith_vartable_t *table;
  pprod_t *p;

  table = o->table;
  p = make_pprod(o->a, o->len);
  return new_arith_var(table, p, mk_arith_vartag(AVAR_PPROD, integer_varexp(table, o->a, o->len)));
}


/*
 * Hash consing object
 */
static pprod_hobj_t pprod_hobj = {
  { (hobj_hash_t) hash_pprod_hobj, (hobj_eq_t) eq_pprod_hobj, (hobj_build_t) build_pprod_hobj },
  NULL,
  NULL,
  0,
};



/*
 * Search for a variable whose definition is equal to p
 * - p = array of pairs <variable, exponent>
 * - n = number of pairs in p
 * - p must be normalized and have degree at least 2
 * - return null_thvar if there no such variable in the table
 */
thvar_t find_var_for_product(arith_vartable_t *table, varexp_t *p, uint32_t n) {
  assert(n >= 2 || (n == 1 && p[0].exp >= 2));

  pprod_hobj.table = table;
  pprod_hobj.a = p;
  pprod_hobj.len = n;

  /*
   * int_htbl_find_obj returns NULL_VALUE == -1 if the object is
   * not found. This is the same as null_thvar == -1.
   */
  return int_htbl_find_obj(&table->htbl, &pprod_hobj.m);
}


/*
 * Get the variable for p: create a fresh variable if needed
 */
thvar_t get_var_for_product(arith_vartable_t *table, varexp_t *p, uint32_t n, bool *new_var) {
  uint32_t nv;
  thvar_t x;

  assert(n >= 2 || (n == 1 && p[0].exp >= 2));

  nv = table->nvars;
  pprod_hobj.table = table;
  pprod_hobj.a = p;
  pprod_hobj.len = n;

  x = int_htbl_get_obj(&table->htbl, &pprod_hobj.m);
  *new_var = table->nvars > nv;

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
static uint32_t hash_poly_hobj(poly_hobj_t *o) {
  return hash_monarray(o->poly, o->len);
}

/*
 * Check whether x's def is equal to poly in o
 */
static bool eq_poly_hobj(poly_hobj_t *o, thvar_t x) {
  arith_vartable_t *table;
  polynomial_t *p;

  table = o->table;
  if (arith_var_def_is_poly(table, x)) {
    p = table->def[x];
    return p->nterms == o->len && equal_monarrays(p->mono, o->poly);
  }

  return false;
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
    if (! arith_var_is_int(table, x)) return false;
    if (! q_is_integer(&p->coeff)) return false;
    p ++;
    x = p->var;
  }
  return true;
}


/*
 * Build a new polynomial and add it to the table
 */
static thvar_t build_poly_hobj(poly_hobj_t *o) {
  arith_vartable_t *table;
  polynomial_t *p;

  table = o->table;
  p = monarray_copy_to_poly(o->poly, o->len);
  return new_arith_var(table, p, mk_arith_vartag(AVAR_POLY, integer_poly(table, p->mono)));
}


/*
 * Hash-object for polynomials
 */
static poly_hobj_t poly_hobj = {
  { (hobj_hash_t) hash_poly_hobj, (hobj_eq_t) eq_poly_hobj, (hobj_build_t) build_poly_hobj },
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
  return int_htbl_find_obj(&table->htbl, &poly_hobj.m);
}


/*
 * Get a variable whose definition is equal to p
 * - create a fresh variable if there's no such variable in the table
 * - if a new variable is created, the flag *new_var is set to true,
 * - if an existing variable is returned, then *new_var is set false
 */
thvar_t get_var_for_poly(arith_vartable_t *table, monomial_t *p, uint32_t n, bool *new_var) {
  uint32_t nv;
  thvar_t x;

  nv = table->nvars;
  poly_hobj.table = table;
  poly_hobj.poly = p;
  poly_hobj.len = n;
  x = int_htbl_get_obj(&table->htbl, &poly_hobj.m);
  *new_var = table->nvars > nv;
  return x;
}


/*
 * Find a variable whose definition is equal to the non-constant part of p
 * - i.e., write p as k + q where k is the constant term, then find a variable for q
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
 * - i.e., write p as k + q where k is the constant term, then get the variable for q
 */
thvar_t get_var_for_poly_offset(arith_vartable_t *table, monomial_t *p, uint32_t n, bool *new_var) {
  if (n > 0 && p->var == const_idx) {
    p ++;
    n --;
  }
  return get_var_for_poly(table, p, n, new_var);
}



