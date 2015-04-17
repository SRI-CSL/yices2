/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CANDIDATE TERM SUBSTITUTIONS
 */

#include <assert.h>

#include "context/pseudo_subst.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"



/*
 * BANK
 */
static void init_bank(st_bank_t *bnk) {
  bnk->tail = NULL;
  bnk->head = NULL;
  bnk->free_idx = ST_BANK_SIZE;
}

static void delete_bank(st_bank_t *bnk) {
  st_block_t *b, *next;

  b = bnk->head;
  while (b != NULL) {
    next = b->next;
    safe_free(b);
    b = next;
  }

  bnk->head = NULL;
  bnk->tail = NULL;
}

static void reset_bank(st_bank_t *bnk) {
  delete_bank(bnk);
  bnk->free_idx = ST_BANK_SIZE;
}



/*
 * Allocate a new triple
 */
static subst_triple_t *alloc_triple(st_bank_t *bnk) {
  st_block_t *b, *aux;
  uint32_t n;

  n = bnk->free_idx;
  b = bnk->tail;
  if (n == ST_BANK_SIZE) {
    // add a block
    b = (st_block_t *) safe_malloc(sizeof(st_block_t));
    b->next = NULL;
    n = 0;
    aux = bnk->tail;
    bnk->tail = b;
    if (aux == NULL) {
      bnk->head = b;
    } else {
      aux->next = b;
    }
  }

  assert(b != NULL && b == bnk->tail && n < ST_BANK_SIZE);

  bnk->free_idx = n + 1;

  return b->data + n;
}




/*
 * HASH TABLE
 */

/*
 * For debugging: check whether n is a power of 2
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialize hash-table + bank.
 * - n = hash table size. If n=0, use the default size.
 * - empty slots in subst->data are marked by NULL
 */
void init_pseudo_subst(pseudo_subst_t *subst, uint32_t n) {
  subst_triple_t **tmp;
  uint32_t i;

  if (n == 0) {
    n = PSEUDO_SUBST_DEF_SIZE;
  }

  if (n >= PSEUDO_SUBST_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (subst_triple_t **) safe_malloc(n * sizeof(subst_triple_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  subst->data = tmp;
  subst->size = n;
  subst->nelems = 0;
  subst->resize_threshold = (uint32_t) (n * PSEUDO_SUBST_RESIZE_RATIO);

  init_bank(&subst->bank);
}



/*
 * Delete all
 */
void delete_pseudo_subst(pseudo_subst_t *subst) {
  safe_free(subst->data);
  delete_bank(&subst->bank);
}


/*
 * Reset: empty the hash table and the bank.
 * - keep the current size
 */
void reset_pseudo_subst(pseudo_subst_t *subst) {
  subst_triple_t **tmp;
  uint32_t i, n;

  tmp = subst->data;
  n = subst->size;
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  subst->nelems = 0;
  reset_bank(&subst->bank);
}



/*
 * Hash code for a triple d
 */
static inline uint32_t hash_triple(subst_triple_t *d) {
  assert(d != NULL);
  return jenkins_hash_int32(d->var);
}

/*
 * Add d to a clean array a
 * - d must be non NULL
 * - a must not be full
 * - mask = size of h - 1 where size of h is a power of 2
 */
static void pseudo_subst_clean_copy(subst_triple_t **a, subst_triple_t *d, uint32_t mask) {
  uint32_t j;

  j = hash_triple(d) & mask;
  while (a[j] != NULL) {
    j ++;
    j &= mask;
  }
  a[j] = d;
}


/*
 * Make the hash table twice as large. Keep its content.
 */
static void pseudo_subst_extend(pseudo_subst_t *subst) {
  subst_triple_t **tmp;
  subst_triple_t *d;
  uint32_t i, n, n2, mask;

  n = subst->size;
  n2 = n<<1;
  if (n2 >= PSEUDO_SUBST_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n2));

  tmp = (subst_triple_t **) safe_malloc(n2 * sizeof(subst_triple_t *));
  for (i=0; i<n2; i++) {
    tmp[i] = NULL;
  }

  mask = n2 - 1;
  for (i=0; i<n; i++) {
    d = subst->data[i];
    if (d != NULL) {
      pseudo_subst_clean_copy(tmp, d, mask);
    }
  }

  safe_free(subst->data);

  subst->data = tmp;
  subst->size = n2;
  subst->resize_threshold = (uint32_t) (n2 * PSEUDO_SUBST_RESIZE_RATIO);
}


/*
 * Find the triple of variable equal to x in subst
 * - return NULL if there's no such triple
 */
subst_triple_t *pseudo_subst_find(pseudo_subst_t *subst, term_t x) {
  subst_triple_t *d;
  uint32_t i, mask;

  assert(subst->nelems < subst->size);

  mask = subst->size - 1;
  i = jenkins_hash_int32(x) & mask;
  for (;;) {
    d = subst->data[i];
    if (d == NULL || d->var == x) return d;
    i ++;
    i &= mask;
  }
}


/*
 * Search for a triple with variable x in subst. If such a triple
 * is found, return it. Otherwise create a fresh record, add it
 * to the table, and return it.
 * - the fresh record is initialized with var = x, map = NULL_TERM,
 *   and eq = NULL_TERM.
 */
subst_triple_t *pseudo_subst_get(pseudo_subst_t *subst, term_t x) {
  subst_triple_t *d;
  uint32_t i, mask;

  assert(subst->nelems < subst->size);

  mask = subst->size - 1;
  i = jenkins_hash_int32(x) & mask;
  for (;;) {
    d = subst->data[i];
    if (d == NULL) break; // x is not in the table
    if (d->var == x) goto found;
    i ++;
    i &= mask;
  }

  d = alloc_triple(&subst->bank);
  d->var = x;
  d->map = NULL_TERM;
  d->eq = NULL_TERM;

  subst->data[i] = d;
  subst->nelems ++;
  if (subst->nelems > subst->resize_threshold) {
    pseudo_subst_extend(subst);
  }

 found:
  return d;
}

/*
 * ITERATOR
 */

/*
 * Apply function f(aux, s) to all substitution triples s in subst
 * - aux is an arbitrary pointer provided by the caller
 * - f must not have side effects on subst
 */
void pseudo_subst_iterate(pseudo_subst_t *subst, void *aux, pseudo_subst_iterator_t f) {
  st_block_t *b;
  uint32_t i, n;

  b = subst->bank.head;
  n = ST_BANK_SIZE;
  while (b != NULL) {
    if (b == subst->bank.tail) {
      n = subst->bank.free_idx;
    }
    for (i=0; i<n; i++) {
      f(aux, b->data + i);
    }
    b = b->next;
  }
}


