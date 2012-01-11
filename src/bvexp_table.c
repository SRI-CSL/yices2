/*
 * Table to store bitvector variable definition in expanded form.
 */

#include "memalloc.h"
#include "bvexp_table.h"
#include "int_powers.h"


/*
 * Initialize table
 * - the table is initially empty (size = 0)
 * - the array def is allocated on the first addition
 * - vtbl = associated variable table
 */
void init_bvexp_table(bvexp_table_t *table, bv_vartable_t *vtbl) {
  table->nvars = 0;
  table->size = 0;
  table->def = NULL;
  table->vtbl = vtbl;
  init_bvmlist_store(&table->store);
  init_bvmlist64_store(&table->store64);
  init_pprod_table(&table->pprods, 32);
  init_int_htbl(&table->htbl, 0);

  init_bvarith_buffer(&table->aux, &table->pprods, &table->store);
  init_bvarith64_buffer(&table->aux64, &table->pprods, &table->store64);
  init_pp_buffer(&table->pp, 10);
  init_bvconstant(&table->bvconst);
}


/*
 * Make the table large enough to store def[n]
 */
static void resize_bvexp_table(bvexp_table_t *table, uint32_t n) {
  uint32_t size;  

  size = table->size;
  if (n >= size) {
    if (size == 0) {
      size = DEF_BVEXPTABLE_SIZE;
    } else {
      size += size >> 1;
    }
    if (n >= size) {
      size = n+1;
    }

    if (size >= MAX_BVEXPTABLE_SIZE) {
      out_of_memory();
    }

    table->def = (void **) safe_realloc(table->def, size * sizeof(void *));
    table->size = size;
  }
}


/*
 * Set def[x] to p
 * - resize the def array if necessary
 * - set def[y] to NULL for table->nvars <= y < x
 */
static void bvexp_set_def(bvexp_table_t *table, thvar_t x, void *p) {
  uint32_t i, n;

  assert(0 < x && x < MAX_BVVARTABLE_SIZE);

  n = x;
  resize_bvexp_table(table, n);
  assert(n < table->size);

  if (n >= table->nvars) {
    for (i=table->nvars; i<n; i++) {
      table->def[i] = NULL;
    }
    table->nvars = n+1;
  }
  table->def[n] = p;
}


/*
 * Add the mapping def[v] = p to the table
 * - v must be a new variable (v >= table->nvars)
 * - p is the polynomial stored in buffer
 * - p must not be present in table (call find first)
 * - buffer must be normalized and h must be the hash code of p
 * Side effect: buffer is reset to the zero polynomial
 */
void bvexp_table_add(bvexp_table_t *table, thvar_t v, bvarith_buffer_t *buffer, uint32_t h) {
  bvmlist_t *p;

  assert(bvvar_bitsize(table->vtbl, v) > 64);
  assert(h == hash_bvmlist(buffer->list, buffer->bitsize));
  assert(buffer->store == &table->store && buffer->ptbl == &table->pprods);

  p = bvarith_buffer_get_mlist(buffer);
  bvexp_set_def(table, v, p);
  int_htbl_add_record(&table->htbl, h, v);
}

void bvexp_table_add64(bvexp_table_t *table, thvar_t v, bvarith64_buffer_t *buffer, uint32_t h) {
  bvmlist64_t *p;

  assert(bvvar_bitsize(table->vtbl, v) <= 64);
  assert(h == hash_bvmlist64(buffer->list, buffer->bitsize));
  assert(buffer->store == &table->store64 && buffer->ptbl == &table->pprods);

  p = bvarith64_buffer_get_mlist(buffer);
  bvexp_set_def(table, v, p);
  int_htbl_add_record(&table->htbl, h, v);
}


/*
 * Remove variable x from the table
 */
static void bvexp_table_remove_var(bvexp_table_t *table, thvar_t x) {
  void *p;
  uint32_t n, h;

  assert(0 <= x && x < table->nvars);
  p = table->def[x];
  if (p != NULL) {
    n = bvvar_bitsize(table->vtbl, x);
    if (n > 64) {
      h = hash_bvmlist(p, n);
      free_bvmlist(p, &table->store, n);
    } else {
      h = hash_bvmlist64(p, n);      
      free_bvmlist64(p, &table->store64);
    }
    int_htbl_erase_record(&table->htbl, h, x);
  }
}


/*
 * Remove all variables of index >= nv
 */
void bvexp_table_remove_vars(bvexp_table_t *table, uint32_t nv) {
  uint32_t i;

  for (i=nv; i<table->nvars; i++) {
    bvexp_table_remove_var(table, i);
  }
  table->nvars = nv;
}


/*
 * Empty the table
 */
void reset_bvexp_table(bvexp_table_t *table) {
  bvexp_table_remove_vars(table, 0);

  // aux buffers must be reset before the stores
  bvarith_buffer_prepare(&table->aux, 100);
  bvarith64_buffer_prepare(&table->aux64, 32);
  pp_buffer_reset(&table->pp);  

  reset_objstore(&table->store);
  reset_objstore(&table->store64);
  reset_pprod_table(&table->pprods);
}



/*
 * Delete all the coefficients in p
 * - n = coefficient size (number of bits)
 */
static void delete_bvmlist_coeffs(bvmlist_t *p, uint32_t n) {
  uint32_t k;

  assert(p != NULL);

  k = (n + 31) >> 5;
  while (p->next != NULL) {
    bvconst_free(p->coeff, k);
    p->coeff = NULL;
    p = p->next;
  }
}

/*
 * Delete the table
 */
void delete_bvexp_table(bvexp_table_t *table) {
  uint32_t i, n, b;
  void *p;

  n = table->nvars;
  for (i=0; i<n; i++) {
    p = table->def[i];
    if (p != NULL) {
      b = bvvar_bitsize(table->vtbl, i);
      if (b > 64) {
	delete_bvmlist_coeffs(p, b);
      }      
    }
  }

  // aux buffers must be deleted first
  delete_bvarith_buffer(&table->aux);
  delete_bvarith64_buffer(&table->aux64);
  delete_pp_buffer(&table->pp);
  delete_bvconstant(&table->bvconst);

  safe_free(table->def);
  table->def = NULL;
  delete_bvmlist_store(&table->store);
  delete_bvmlist64_store(&table->store64);
  delete_pprod_table(&table->pprods);
  delete_int_htbl(&table->htbl);  
}



/*
 * Hash object for using int_hash_table
 * - def = either bvmlist_t or bvmlist64_t depending on the bitsize
 * - h = hash code of def
 */
typedef struct bvexp_hobj_s {
  int_hobj_t m;
  bvexp_table_t *table;
  void *def;
  uint32_t bitsize;
  uint32_t h;
} bvexp_hobj_t;


/*
 * Hash function
 */
static uint32_t hash_bvexp_hobj(bvexp_hobj_t *o) {
  return o->h;
}

/*
 * Equality test
 */
static bool eq_hash_bvexp_hobj(bvexp_hobj_t *o, thvar_t i) {
  bvexp_table_t *table;
  uint32_t n;
  bool result;

  table = o->table;
  assert(0 <= i && i < table->nvars && table->def[i] != NULL);

  n = o->bitsize;
  result = false;

  if (bvvar_bitsize(table->vtbl, i) == n) {
    if (n < 64) {
      result = equal_bvmlists64(o->def, table->def[i]);
    } else {
      result = equal_bvmlists(o->def, table->def[i], n);
    }
  }

  return result;
}


/*
 * Check whether the polynomial p stored in buffer is present in table
 * - if so, return the variable index i sucb that def[i] = p
 *   otherwise, return -1
 * - buffer must be normalized and h must be the hash code of p
 * - buffer->store must be the same as table->store (or table->store64).
 * - two versions depending on the number of bits in p
 */
thvar_t bvexp_table_find(bvexp_table_t *table, bvarith_buffer_t *buffer, uint32_t h) {
  bvexp_hobj_t hobj;

  assert(h == hash_bvmlist(buffer->list, buffer->bitsize));
  assert(buffer->store == &table->store && buffer->ptbl == &table->pprods);

  hobj.m.hash = (hobj_hash_t) hash_bvexp_hobj;
  hobj.m.eq = (hobj_eq_t) eq_hash_bvexp_hobj;
  hobj.m.build = NULL;
  hobj.table = table;
  hobj.def = buffer->list;
  hobj.bitsize = buffer->bitsize;
  hobj.h = h;

  return int_htbl_find_obj(&table->htbl, &hobj.m);
}

thvar_t bvexp_table_find64(bvexp_table_t *table, bvarith64_buffer_t *buffer, uint32_t h) {
  bvexp_hobj_t hobj;

  assert(h == hash_bvmlist64(buffer->list, buffer->bitsize));
  assert(buffer->store == &table->store64 && buffer->ptbl == &table->pprods);

  hobj.m.hash = (hobj_hash_t) hash_bvexp_hobj;
  hobj.m.eq = (hobj_eq_t) eq_hash_bvexp_hobj;
  hobj.m.build = NULL;
  hobj.table = table;
  hobj.def = buffer->list;
  hobj.bitsize = buffer->bitsize;
  hobj.h = h;

  return int_htbl_find_obj(&table->htbl, &hobj.m);
}




/*
 * EXPANDED FORM OF POLYNOMIALS AND POWER PRODUCTS
 */

/*
 * Expanded form of a bitvector polynomial p
 * - p is stored in a bvpoly_buffer object
 * - the expansion is returned in a bvarith_buffer or bvarith64_buffer object
 * - the result is normalized
 */
void expand_bvpoly64(bvexp_table_t *table, bvarith64_buffer_t *buffer, bvpoly_buffer_t *p) {
  bv_vartable_t *vtbl;
  bvmlist64_t *q;
  uint64_t c;
  uint32_t i, n;
  thvar_t x;

  assert(buffer->store == &table->store64 && buffer->ptbl == &table->pprods);

  bvarith64_buffer_prepare(buffer, bvpoly_buffer_bitsize(p)); 

  n = bvpoly_buffer_num_terms(p);
  if (n > 0) {
    vtbl = table->vtbl;
    i = 0;

    // deal with the constant term if any
    if (bvpoly_buffer_var(p, 0) == const_idx) {
      bvarith64_buffer_add_const(buffer, bvpoly_buffer_coeff64(p, 0));
      i ++;
    }

    /*
     * non-constant terms of p are of the form a * x
     * we replace x by its value if x has tag BVTAG_CONST64
     * we replace x by its definition if x has a definition in table 
     * otherwise, we keep x as is
     */
    while (i < n) {
      x = bvpoly_buffer_var(p, i);
      c = bvpoly_buffer_coeff64(p, i);
      i ++;
      if (bvvar_is_const64(vtbl, x)) {
	c *= bvvar_val64(vtbl, x);
	bvarith64_buffer_add_const(buffer, c);
      } else {
	q = bvexp_def64(table, x);
	if (q != NULL) {
	  bvarith64_buffer_add_const_times_mlist(buffer, q, c);
	} else {
	  bvarith64_buffer_add_varmono(buffer, c, x);
	}
      }
    }

    bvarith64_buffer_normalize(buffer);
  }
}


void expand_bvpoly(bvexp_table_t *table, bvarith_buffer_t *buffer, bvpoly_buffer_t *p) {
  bv_vartable_t *vtbl;
  bvmlist_t *q;
  uint32_t *c;
  uint32_t i, n;
  thvar_t x;

  assert(buffer->store == &table->store && buffer->ptbl == &table->pprods);

  bvarith_buffer_prepare(buffer, bvpoly_buffer_bitsize(p));

  n = bvpoly_buffer_num_terms(p);
  if (n > 0) {
    vtbl = table->vtbl;
    i = 0;
    
    // constant term of p
    if (bvpoly_buffer_var(p, 0) == const_idx) {
      bvarith_buffer_add_const(buffer, bvpoly_buffer_coeff(p, 0));
      i ++;
    }

    // non-constant terms
    while (i < n) {
      x = bvpoly_buffer_var(p, i);
      c = bvpoly_buffer_coeff(p, i);
      i ++;
      if (bvvar_is_const(vtbl, x)) {
	bvarith_buffer_add_const_times_const(buffer, c, bvvar_val(vtbl, x));
      } else {
	q = bvexp_def(table, x);
	if (q != NULL) {
	  bvarith_buffer_add_const_times_mlist(buffer, q, c);
	} else {
	  bvarith_buffer_add_varmono(buffer, c, x);
	}
      }
    }

    bvarith_buffer_normalize(buffer);
  }
}



/*
 * Check whether one variable of power product p has a non-null expanded form in table
 */
bool pprod_can_expand(bvexp_table_t *table, pp_buffer_t *p) {
  uint32_t i, n;
  thvar_t x;

  n = p->len;
  for (i=0; i<n; i++) {
    x = p->prod[i].var;
    if (bvexp_get_def(table, x) != NULL) return true;
  }

  return false;
}




/*
 * Expanded form for a power product p
 * - p is stored in a pp_buffer object
 * - n = bitsize of p 
 * - the expansion is returned in a bvarith_buffer or bvarith64_buffer object
 * - the result is normalized
 */
void expand_bvpprod64(bvexp_table_t *table, bvarith64_buffer_t *buffer, pp_buffer_t *p, uint32_t n) {
  bv_vartable_t *vtbl;
  bvmlist64_t *q;
  pprod_t *exp;
  uint64_t c;
  uint32_t i, m, d;
  thvar_t x;

  assert(buffer->store == &table->store64 && buffer->ptbl == &table->pprods);

  bvarith64_buffer_prepare(buffer, n);
  bvarith64_buffer_set_one(buffer);

  // TODO: make this more efficient?
  vtbl = table->vtbl;
  m = p->len;
  for (i=0; i<m; i++) {
    x = p->prod[i].var;
    d = p->prod[i].exp;
    if (bvvar_is_const64(vtbl, x)) {
      c = bvvar_val64(vtbl, x);
      c = upower64(c, d);
      bvarith64_buffer_mul_const(buffer, c);
    } else {
      q = bvexp_def64(table, x);
      if (q != NULL) {
	bvarith64_buffer_mul_mlist_power(buffer, q, d, &table->aux64);
      } else {
	exp = pprod_varexp(&table->pprods, x, d);
	bvarith64_buffer_mul_pp(buffer, exp);
      }
    }
  }

  bvarith64_buffer_normalize(buffer);
}

void expand_bvpprod(bvexp_table_t *table, bvarith_buffer_t *buffer, pp_buffer_t *p, uint32_t n) {
  bv_vartable_t *vtbl;
  bvmlist_t *q;
  pprod_t *exp;
  uint32_t *c;
  uint32_t i, m, d, k;
  thvar_t x;


  assert(buffer->store == &table->store && buffer->ptbl == &table->pprods);

  bvarith_buffer_prepare(buffer, n);
  bvarith_buffer_set_one(buffer);

  k = (n + 31) >> 5;

  vtbl = table->vtbl;
  m = p->len;
  for (i=0; i<m; i++) {
    x = p->prod[i].var;
    d = p->prod[i].exp;
    if (bvvar_is_const(vtbl, x)) {
      c = bvvar_val(vtbl, x);
      if (d == 1) {
	bvarith_buffer_mul_const(buffer, c);
      } else {
	// compute c^d in the table's bvconst buffer
	bvconstant_copy64(&table->bvconst, n, 1);
	bvconst_mulpower(table->bvconst.data, k, c, d);
	bvarith_buffer_mul_const(buffer, table->bvconst.data);
      }
    } else {
      q = bvexp_def(table, x);
      if (q != NULL) {
	bvarith_buffer_mul_mlist_power(buffer, q, d, &table->aux);
      } else {
	exp = pprod_varexp(&table->pprods, x, d);
	bvarith_buffer_mul_pp(buffer, exp);
      }
    }
  }

  bvarith_buffer_normalize(buffer);
}




