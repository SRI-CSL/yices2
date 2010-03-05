/*
 * Polynomial manager: hash consing for variable products.
 * Store data for two kinds of variables:
 * - primitive variables have an index attached (term index)
 * - auxiliary variables represent products of primitive variables
 * Index 0 is reserved for the empty product.
 */

#include "memalloc.h"
#include "hash_functions.h"
#include "polynomial_manager.h"

/*
 * Default notifiers: do nothing
 */
static void default_resize_notify(void *m, uint32_t old_size, uint32_t new_size) {
}

static void default_newprod_notify(void *m, int32_t new_index, varprod_t *p) {
}


/*
 * Initialization of manager m.
 * - n = initial size.
 */
static void polymanager_alloc(polynomial_manager_t *m, uint32_t n) {
  if (n >= MAX_VARTBL_SIZE) {
    out_of_memory();
  }

  m->size = n;
  m->nelems = 0;
  m->free_idx = null_idx; // -1
  m->degree = (int32_t *) safe_malloc(n * sizeof(int32_t));
  m->desc = (polyvar_desc_t *) safe_malloc(n * sizeof(polyvar_desc_t));

  init_int_htbl(&m->htbl, 0);
  init_vpbuffer(&m->vpbuffer, 0);

  m->notify_resize = default_resize_notify;
  m->notify_newprod = default_newprod_notify;
}


/*
 * Extend: increase size by 50%
 */
static void polymanager_extend(polynomial_manager_t *m) {
  uint32_t n;

  n = m->size + 1;
  n += n >> 1;
  if (n >= MAX_VARTBL_SIZE) {
    out_of_memory();
  }

  m->degree = (int32_t *) safe_realloc(m->degree, n * sizeof(int32_t));
  m->desc = (polyvar_desc_t *) safe_realloc(m->desc, n * sizeof(polyvar_desc_t));
  m->notify_resize(m, m->size, n);
  m->size = n;
}


/*
 * Allocate a new variable index
 */
static int32_t alloc_index(polynomial_manager_t *m) {
  int32_t i;

  i = m->free_idx;
  if (i >= 0) {
    m->free_idx = m->desc[i].integer;
  } else {
    i = m->nelems;
    m->nelems ++;
    if (i == m->size) {
      polymanager_extend(m);
    }
  }

  return i;
}


/*
 * Add new var and return its index. 
 */
int32_t polymanager_new_var(polynomial_manager_t *m, int32_t term_index) {
  int32_t i;

  i = alloc_index(m);
  m->degree[i] = 1;
  m->desc[i].integer = term_index;

  return i;
}


/*
 * Add new product
 */
static int32_t polymanager_add_product(polynomial_manager_t *m, varprod_t *p) {
  int32_t i;

  i = alloc_index(m);
  m->degree[i] = varprod_degree(p);
  m->desc[i].prod = p;
  m->notify_newprod(m, i, p);

  return i;
}



/*
 * Objects for hash-consing of products
 * - the product is stored in m->vpbuffer
 * - it must be normalized and not reduced to a single variable.
 */
typedef struct prod_hobj_s {
  int_hobj_t m;
  polynomial_manager_t *manager;  
} prod_hobj_t;

/*
 * methods for interacting with int_hash_table
 */
static uint32_t hash_product(void *o) {
  polynomial_manager_t *m;

  m = ((prod_hobj_t *) o)->manager;
  return jenkins_hash_intarray(2 * m->vpbuffer.len, (int32_t *) m->vpbuffer.prod);
}

static bool eq_product(void *o, int32_t v) {
  polynomial_manager_t *m;
  varprod_t *p;
  varexp_t *a, *b;
  int32_t i, n;

  m = ((prod_hobj_t *) o)->manager;
  if (m->degree[v] == 1) return false; // v is not a product

  p = m->desc[v].prod;
  n = p->len;
  if (n != m->vpbuffer.len) return false;
  a = p->prod;
  b = m->vpbuffer.prod;
  for (i=0; i<n; i ++) {
    if (a[i].var != b[i].var || a[i].exp != b[i].exp) return false;
  }

  return true;
}

static int32_t build_product(void *o) {
  polynomial_manager_t *m;
  varprod_t *p;

  m = ((prod_hobj_t *) o)->manager;
  p = vpbuffer_getprod(&m->vpbuffer);
  return polymanager_add_product(m, p);
}


/*
 * Global object for hash consing
 */
static prod_hobj_t prod_hobj = {
  { hash_product, eq_product, build_product },
  NULL,
};



/*
 * Get index of product stored in the internal buffer.
 * The product must be normalized.
 * Allocate a fresh index if the product is not already present.
 */
static int32_t polymanager_get_product_index(polynomial_manager_t *m) {
  if (m->vpbuffer.len == 1 && m->vpbuffer.prod[0].exp == 1) {
    // product of a single variable: return v
    return m->vpbuffer.prod[0].var;
  }
  prod_hobj.manager = m;
  return int_htbl_get_obj(&m->htbl, (int_hobj_t *) &prod_hobj);
}




/*
 * Initialize and store the constant idx = empty product.
 * n = initial size.
 */
void init_polymanager(polynomial_manager_t *m, uint32_t n) {
  int32_t tst;

  polymanager_alloc(m, n);
  assert(m->vpbuffer.len == 0);
  tst = polymanager_get_product_index(m);
  assert(tst == const_idx);
}



/*
 * Free memory
 */
void delete_polymanager(polynomial_manager_t *m) {
  int32_t i;

  // delete the products
  for (i=0; i<m->nelems; i++) {
    if (m->degree[i] != 1) safe_free(m->desc[i].prod);
  }

  safe_free(m->degree);
  safe_free(m->desc);

  delete_int_htbl(&m->htbl);
  delete_vpbuffer(&m->vpbuffer);

  m->degree = NULL;
  m->desc = NULL;
  m->nelems = 0;
  m->size = 0;
}



/*
 * Get index of product v1 * v2
 */
int32_t polymanager_mul_var(polynomial_manager_t *m, int32_t v1, int32_t v2) {
  assert(0 <= v1 && v1 < m->nelems);
  assert(0 <= v2 && v2 < m->nelems);

  if (m->degree[v1] == 1) {
    vpbuffer_set_var(&m->vpbuffer, v1); 
  } else {
    vpbuffer_set_varprod(&m->vpbuffer, m->desc[v1].prod);
  }

  if (m->degree[v2] == 1) {
    vpbuffer_mul_var(&m->vpbuffer, v2); 
  } else {
    vpbuffer_mul_varprod(&m->vpbuffer, m->desc[v2].prod);
  }

  return polymanager_get_product_index(m);
}


/*
 * Get index of a product of variables v[0] to v[n-1]
 */
int32_t polymanager_product_vars(polynomial_manager_t *m, int32_t n, int32_t *v) {
#ifndef NDEBUG
  int32_t i;

  for (i=0; i<n; i++) {
    assert(polymanager_var_is_primitive(m, v[i]));
  }
#endif

  vpbuffer_set_vars(&m->vpbuffer, n, v);
  vpbuffer_normalize(&m->vpbuffer);
  return polymanager_get_product_index(m);
}

/*
 * Get index of a product v[0]^d[0] to v[n-1]^d[n-1]
 * - v[i] must be a variable
 * - d[i] must be non-negative
 */
int32_t polymanager_product_varexps(polynomial_manager_t *m, int32_t n, int32_t *v, int32_t *d) {
#ifndef NDEBUG
  int32_t i;

  for (i=0; i<n; i++) {
    assert(d[i] >= 0);
    assert(polymanager_var_is_primitive(m, v[i]));
  }
#endif

  vpbuffer_set_varexps(&m->vpbuffer, n, v, d);
  assert(vpbuffer_below_max_degree(&m->vpbuffer)); // check for overflow
  vpbuffer_normalize(&m->vpbuffer);
  return polymanager_get_product_index(m);
}


/*
 * Delete v
 */
void polymanager_delete_var(polynomial_manager_t *m, int32_t v) {
  if (v == const_idx) return;

  if (m->degree[v] > 1) safe_free(m->desc[v].prod);
  m->desc[v].integer = m->free_idx;
  m->free_idx = v;
}


/*
 * var_precedes(m, v, w) returns true if v < w.
 *
 * - the order on variables is defined by 
 *   v < w iff degree(v) < degree(w) 
 *         or  degree(v) = degree(w) = 1 and v < w
 *         or  degree(v) = degree(w) > 1 and prod(v) < prod(w) in lexical ordering
 */
bool polymanager_var_precedes(polynomial_manager_t *m, int32_t v, int32_t w) {
  int32_t dv, dw;

  if (v == w) return false;
  if (v == max_idx) return false;
  if (w == max_idx) return true;

  dv = m->degree[v];
  dw = m->degree[w];

  if (dv == dw) {
    if (dv == 1) 
      return v < w;
    else 
      return varprod_lex_cmp(m->desc[v].prod, m->desc[w].prod) < 0;
  } else {
    return dv < dw;
  }
}



/*
 * Get all primitive variables of v
 * - that's either v itself or the variables in the product represented by v
 */
void polymanager_get_vars(polynomial_manager_t *m, int32_t v, ivector_t *u) {
  int32_t i;
  varprod_t *p;

  assert(0 <= v && v < m->nelems);
  if (m->degree[v] == 1) {
    ivector_push(u, v);
  } else {
    p = m->desc[v].prod;
    for (i=0; i<p->len; i++) {
      ivector_push(u, p->prod[i].var);
    }
  }
  
}


/*
 * Collect all terms occurring in variable v
 * - if v is primitive there's only one term t = m->desc[v]
 * - otherwise, v is a product of primitive variables, the terms of v
 *   are all the terms attached to these primitive variables.
 */
void polymanager_get_terms(polynomial_manager_t *m, int32_t v, ivector_t *u) {
  int32_t i;
  varprod_t *p;
 
  assert(0 <= v && v < m->nelems);
  if (m->degree[v] == 1) {
    ivector_push(u, m->desc[v].integer);
  } else {
    p = m->desc[v].prod;
    for (i=0; i<p->len; i++) {
      v = p->prod[i].var;
      assert(m->degree[v] == 1);
      ivector_push(u, m->desc[v].integer);
    }
  }
}


/*
 * Compute the degree of x in the product represented by variable v
 * - x must be a primitive variable in m
 * - if v is primitive, return 1 if x == v, 0 if x != v
 * - otherwise, get the exponent of x in the product v
 */
int32_t polymanager_var_degree_in_prod(polynomial_manager_t *m, int32_t v, int32_t x) {
  int32_t d;

  assert(0 <= x && x < m->nelems && m->degree[x] == 1 && 0 <= v && v < m->nelems);

  if (m->degree[v] == 1) {
    d = (x == v);
  } else {
    d = varprod_var_degree(m->desc[v].prod, x);
  }

  return d;
}
