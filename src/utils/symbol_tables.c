/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SYMBOL TABLES: MAP STRINGS TO 32BIT INTEGERS
 */

#include <assert.h>
#include <stdbool.h>
#include <string.h>

#define TRACE_RESIZE 0

#if TRACE_RESIZE
// PROVISIONAL
#include <stdio.h>
#include <inttypes.h>

#endif

#include "utils/memalloc.h"
#include "utils/hash_functions.h"
#include "utils/symbol_tables.h"


/*
 * For debugging: check whether n is a power of two
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


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
    assert(sym_table->ndeleted > 0);
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
 * Insert all the records from list into array tmp
 * - mask = size of tmp - 1 (tmp's size is a power of 2)
 * - the records are inserted in reverse order
 */
static void stbl_restore_list(stbl_rec_t **tmp, uint32_t mask, stbl_rec_t *list) {
  stbl_rec_t *r, *p;
  uint32_t i;

  // reverse the list
  p = NULL;;
  while (list != NULL) {
    r = list->next;
    list->next = p;
    p = list;
    list = r;
  }

  // now p = list in reverse order
  while (p != NULL) {
    r = p->next;
    assert(p->string != NULL);
    i = p->hash & mask;
    p->next = tmp[i];
    tmp[i] = p;
    p = r;
  }
}


/*
 * Extend the table: make it twice as large.
 * - do nothing if malloc fails or if the table has maximal size already
 */
static void stbl_extend(stbl_t *sym_table) {
  stbl_rec_t **tmp;
  stbl_rec_t *list;
  uint32_t i, n, old_size, mask;

  old_size = sym_table->size;
  n = old_size << 1;
  if (n == 0 || n >= MAX_STBL_SIZE) {
    // overflow: cannot expand
    return;
  }

  assert(is_power_of_two(n));

  // new data array
  tmp = (stbl_rec_t **) malloc(n * sizeof(stbl_rec_t *));
  if (tmp == NULL)  return;

  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  // move the data lists to tmp
  mask = n-1;
  for (i=0; i<old_size; i++) {
    list = sym_table->data[i];
    if (list != NULL) {
      stbl_restore_list(tmp, mask, list);
    }
  }

  // clean up
  safe_free(sym_table->data);
  sym_table->data = tmp;
  sym_table->size = n;

#if TRACE_RESIZE
  printf("resize table %p: cost = %"PRIu32", nelems = %"PRIu32", ndeleted = %"PRIu32
         ", old size = %"PRIu32", new size = %"PRIu32"\n",
	 sym_table, sym_table->cost, sym_table->nelems, sym_table->ndeleted, old_size, n);
  fflush(stdout);
#endif
}


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

  sym_table->data = tmp;
  sym_table->bnk = NULL;
  sym_table->free_rec = NULL;
  sym_table->size = n;
  sym_table->nelems = 0;
  sym_table->ndeleted = 0;
  sym_table->free_idx = 0;

  sym_table->lctr = STBL_NLOOKUPS;
  sym_table->cost = 0;

  sym_table->finalize = default_stbl_finalizer;
}



/*
 * Delete all the table
 */
void delete_stbl(stbl_t *sym_table) {
  stbl_bank_t *b, *next;
  stbl_rec_t *r;
  uint32_t k;

#if TRACE_RESIZE
  printf("delete table %p: cost = %"PRIu32", nelems = %"PRIu32", ndeleted = %"PRIu32", size = %"PRIu32"\n",
	 sym_table, sym_table->cost, sym_table->nelems, sym_table->ndeleted, sym_table->size);
  fflush(stdout);
#endif

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

  sym_table->nelems = 0;

  sym_table->lctr = STBL_NLOOKUPS;
  sym_table->cost = 0;
}


/*
 * Remove first occurrence of symbol.
 * No effect if symbol is not present.
 */
void stbl_remove(stbl_t *sym_table, const char *symbol) {
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
 * Remove the first occurrence of (symbol, value).
 * No effect if it's not present.
 */
void stbl_delete_mapping(stbl_t *sym_table, const char *symbol, int32_t val) {
  uint32_t h, mask, i;
  stbl_rec_t *r, *p;

  mask = sym_table->size - 1;
  h = jenkins_hash_string(symbol);
  i = h & mask;
  p = NULL;
  for (r = sym_table->data[i]; r != NULL; r = r->next) {
    if (r->hash == h && r->value == val && strcmp(symbol, r->string) == 0) {
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
 * Check whether the list sym_table->data[i] has many duplicates
 * - r must either be NULL or be a pointer to one list record (not the first one)
 * - return true if all elements before r have the same hash code
 * - in such a case, and if r is not NULL, we move r to the front
 *   of the list
 */
static bool list_has_duplicates(stbl_t *sym_table, uint32_t i, stbl_rec_t *r) {
  stbl_rec_t *p, *l;
  uint32_t h;

  assert(i < sym_table->size);
  l = sym_table->data[i];
  h = l->hash;
  assert(l != r);

  for (;;) {
    p = l;
    l = l->next;
    if (l == r) break;
    if (l->hash != h) return false;
  }

  /*
   * all elements before r have the same hash code
   * p = predecessor of r
   */
  assert(p->next == r && p->hash == h);
  if (r != NULL) {
    p->next = r->next;
    r->next = sym_table->data[i];
    sym_table->data[i] = r;
  }

  return true;
}


/*
 * Return value of first occurrence of symbol, or -1 if symbol is not
 * present.
 * - update the cost
 */
int32_t stbl_find(stbl_t *sym_table, const char *symbol) {
  uint32_t mask, i, h, steps;
  int32_t result;
  stbl_rec_t *r;

  result = -1;
  steps = 0;
  mask = sym_table->size - 1;
  h = jenkins_hash_string(symbol);
  i = h & mask;
  for (r = sym_table->data[i]; r != NULL; r = r->next) {
    steps ++;
    if (r->hash == h && strcmp(symbol, r->string) == 0) {
      result = r->value;
      break;
    }
  }

  /*
   * Check whether the list contains many duplicates and move r to the
   * front if possible. If the list has duplicates, we reduce steps to 1,
   * since resizing won't help much.
   */
  if (steps > STBL_MAXVISITS && list_has_duplicates(sym_table, i, r)) {
    steps = 1;
  }

  /*
   * Update cost and counter. Resize if the last NLOOKUPS have a
   * high total cost.
   */
  assert(sym_table->lctr > 0);
  sym_table->cost += steps;
  sym_table->lctr --;
  if (sym_table->lctr == 0) {
    if (sym_table->cost > STBL_RESIZE_THRESHOLD && sym_table->size <= (MAX_STBL_SIZE/2)) {
      stbl_extend(sym_table);
    }
    sym_table->cost = 0;
    sym_table->lctr = STBL_NLOOKUPS;
  }

  return result;
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
}



/*
 * Iterator: call f(aux, r) for every live record r in the table
 * - aux is an arbitrary pointer, provided by the caller
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


/*
 * Remove records using a filter
 * - calls f(aux, r) on every record r present in the table
 * - if f(aux, r) returns true, then the finalizer is called
 *   then r is removed from the table.
 * - f must not have side effects
 */
void stbl_remove_records(stbl_t *sym_table, void *aux, stbl_filter_t f) {
  uint32_t i, n;
  stbl_rec_t *r, *p, **q;

  n = sym_table->size;
  for (i=0; i<n; i++) {
    q = sym_table->data + i;
    r = sym_table->data[i];
    while (r != NULL) {
      p = r->next;
      if (f(aux, r)) {
	sym_table->finalize(r);
	stbl_free_record(sym_table, r);
	r = p;
      } else {
	// keep r
	*q = r;
	q = &r->next;
      }
    }
    *q = NULL;
  }
}
