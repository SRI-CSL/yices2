/*
 * Symbol tables: hash map strings to 32bit integers
 */

#include <assert.h>
#include <stdbool.h>
#include <string.h>

#include "memalloc.h"
#include "hash_functions.h"
#include "symbol_tables.h"


/*
 * Default finalizer: do nothing
 */
static void default_stbl_finalizer(stbl_rec_t *r) {
}


/*
 * Allocate and initialize a bank
 */
static stbl_bank_t *stbl_alloc_bank() {
  stbl_bank_t *b;
  uint32_t i;

  b = (stbl_bank_t *) safe_malloc(sizeof(stbl_bank_t));
  for (i=0; i<STBL_BANK_SIZE; i++) {
    b->block[i].string = NULL;
  }
  return b;
}




/*
 * Allocate a record
 */
static stbl_rec_t *stbl_alloc_record(stbl_t *sym_table) {
  stbl_rec_t *tmp;
  stbl_bank_t *new_bnk;
  uint32_t i;

  tmp = sym_table->free_rec;
  if (tmp != NULL) {    
    sym_table->free_rec = tmp->next;
    sym_table->ndeleted --;
    return tmp;
  }

  i = sym_table->free_idx;
  if (i == 0) {
    new_bnk = stbl_alloc_bank();
    new_bnk->next = sym_table->bnk;
    sym_table->bnk = new_bnk;
    i = STBL_BANK_SIZE;
  }
  assert(i > 0);

  i --;
  tmp = sym_table->bnk->block + i;
  sym_table->free_idx = i;

  return tmp;
}


/*
 * Free a record: put it on the free list
 */
static void stbl_free_record(stbl_t *sym_table, stbl_rec_t *r) {
  assert(r != NULL);
  r->string = NULL;
  r->next = sym_table->free_rec;
  sym_table->free_rec = r;
  sym_table->ndeleted ++;
}


/*
 * Initialize a record: store h, val, and s.
 */
static void stbl_init_record(stbl_rec_t *r, uint32_t h, int32_t val, char *s) {
  r->hash = h;
  r->value = val;
  r->string = s;
}

/*
 * Re-insert all non-deleted records into sym_table->data
 */
static void stbl_restore(stbl_t *sym_table) {
  uint32_t i, k, mask;
  stbl_rec_t *r;
  stbl_bank_t *b;

  mask = sym_table->size - 1;
  k = sym_table->free_idx;
  for (b = sym_table->bnk; b != NULL; b = b->next) {
    for (r = b->block + k; r < b->block + STBL_BANK_SIZE; r ++) {
      if (r->string != NULL) {
	i = r->hash & mask;
	r->next = sym_table->data[i];
	sym_table->data[i] = r;
      }
    }
    k = 0;
  }
}


/*
 * Resize the table: n = new size
 */
static void stbl_resize(stbl_t *sym_table, uint32_t n) {
  uint32_t i;
  stbl_rec_t **tmp;

  tmp = (stbl_rec_t **) safe_malloc(n * sizeof(stbl_rec_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  safe_free(sym_table->data);
  sym_table->data = tmp;
  sym_table->size = n;

  stbl_restore(sym_table);
}


/*
 * Extend the table: make it twice as large.
 */
static void stbl_extend(stbl_t *sym_table) {
  uint32_t n;

  n = sym_table->size << 1;
  if (n == 0 || n >= MAX_STBL_SIZE) {
    // overflow: cannot expand 
    out_of_memory();
  }
  stbl_resize(sym_table, n);
}


/*
 * For debugging: check whether n is a power of two
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialize: empty table of size n. n must be a power of 2.
 * If n = 0, the default size is used.
 */
void init_stbl(stbl_t *sym_table, uint32_t n) {
  uint32_t i;
  stbl_rec_t **tmp;

  if (n == 0) {
    n = STBL_DEFAULT_SIZE;
  }

  if (n >= MAX_STBL_SIZE) {    
    out_of_memory(); // abort if too large
  }

  assert(is_power_of_two(n));

  tmp = (stbl_rec_t**) safe_malloc(n * sizeof(stbl_rec_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  sym_table->size = n;
  sym_table->nelems = 0;
  sym_table->ndeleted = 0;
  sym_table->bnk = NULL;
  sym_table->free_idx = 0;
  sym_table->free_rec = NULL;
  sym_table->data = tmp;
  sym_table->finalize = default_stbl_finalizer;
}



/*
 * Delete all the table
 */
void delete_stbl(stbl_t *sym_table) {
  stbl_bank_t *b, *next;
  stbl_rec_t *r;
  uint32_t k;

  b = sym_table->bnk;
  sym_table->bnk = NULL;
  k = sym_table->free_idx; // first live record in first bank

  while (b != NULL) {
    // apply finalizer to all live records
    for (r = b->block + k; r < b->block + STBL_BANK_SIZE; r ++) {
      if (r->string != NULL) {
	sym_table->finalize(r);
      }
    }
    // delete b
    next = b->next;   
    safe_free(b);
    b = next;
    k = 0;
  }

  safe_free(sym_table->data);
  sym_table->data = NULL;
}




/*
 * Empty the table
 */
void reset_stbl(stbl_t *sym_table) {
  uint32_t i, n;
  stbl_rec_t *r, *p;

  n = sym_table->size;
  for (i=0; i<n; i++) {
    r = sym_table->data[i];
    while (r != NULL) {
      p = r->next;
      sym_table->finalize(r);
      stbl_free_record(sym_table, r);
      r = p;
    }
    sym_table->data[i] = NULL;
  }

  sym_table->ndeleted = 0;
  sym_table->nelems = 0;
}


/*
 * Remove first occurrence of symbol.
 * No effect if symbol is not present.
 */
void stbl_remove(stbl_t *sym_table, char *symbol) {
  uint32_t h, mask, i;
  stbl_rec_t *r, *p;

  mask = sym_table->size - 1;
  h = jenkins_hash_string(symbol);
  i = h & mask;
  p = NULL;
  for (r = sym_table->data[i]; r != NULL; r = r->next) {
    if (r->hash == h && strcmp(symbol, r->string) == 0) {
      if (p == NULL) {
	sym_table->data[i] = r->next;
      } else {
	p->next = r->next;
      }
      sym_table->finalize(r);
      stbl_free_record(sym_table, r);
      return;
    }
    p = r;
  }
}


/*
 * Return value of first occurrence of symbol, or -1 if symbol is not
 * present
 */
int32_t stbl_find(stbl_t *sym_table, char *symbol) {
  uint32_t mask, i, h;
  stbl_rec_t *r;

  mask = sym_table->size - 1;
  h = jenkins_hash_string(symbol);
  i = h & mask;
  for (r = sym_table->data[i]; r != NULL; r = r->next) {
    if (r->hash == h && strcmp(symbol, r->string) == 0) {
      return r->value;
    }
  }

  return -1;
}


/*
 * Add new mapping for symbol.
 */
void stbl_add(stbl_t *sym_table, char *symbol, int32_t value) {
  uint32_t mask, i, h;
  stbl_rec_t *r;

  assert(value >= 0);
  mask = sym_table->size - 1;
  h = jenkins_hash_string(symbol);
  i = h & mask;

  r = stbl_alloc_record(sym_table);
  stbl_init_record(r, h, value, symbol);
  r->next = sym_table->data[i];
  sym_table->data[i] = r;

  sym_table->nelems ++;
  if (sym_table->nelems > sym_table->size) {
    stbl_extend(sym_table);
  }
}



/*
 * Iterator: call f(aux, r) for every live record r in the table
 * - aux is an arbitrary pointer, provided byt the caller
 * - f must not have side effects (it must not add or remove anything 
 *   from the symbol table, or modify the record r).
 */
void stbl_iterate(stbl_t *sym_table, void *aux, stbl_iterator_t f) {
  stbl_bank_t *b;
  stbl_rec_t *r;
  uint32_t k;

  k = sym_table->free_idx;
  for (b = sym_table->bnk; b != NULL; b = b->next) {
    for (r = b->block + k; r < b->block + STBL_BANK_SIZE; r++) {
      if (r->string != NULL) {
	// r is a live record
	f(aux, r);
      }
    }
    k = 0;
  }
}
