/*
 * Table to store bitvector variable definition in expanded form.
 */

#include "memalloc.h"
#include "bvexp_tables.h"


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

    table->def = (void **) safe_malloc(size * sizeof(void *));
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
  hobj.def = buffer->list;
  hobj.bitsize = buffer->bitsize;

  return int_htbl_find_obj(&table->htbl, &hobj.m);
}

thvar_t bvexp_table_find64(bvexp_table_t *table, bvarith64_buffer_t *buffer, uint32_t h) {
  bvexp_hobj_t hobj;

  assert(h == hash_bvmlist64(buffer->list, buffer->bitsize));
  assert(buffer->store == &table->store && buffer->ptbl == &table->pprods);

  hobj.m.hash = (hobj_hash_t) hash_bvexp_hobj;
  hobj.m.eq = (hobj_eq_t) eq_hash_bvexp_hobj;
  hobj.m.build = NULL;
  hobj.def = buffer->list;
  hobj.bitsize = buffer->bitsize;

  return int_htbl_find_obj(&table->htbl, &hobj.m);
}

