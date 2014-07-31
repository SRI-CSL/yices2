/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * HASH TABLE FOR BOOLEAN GATES
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>

#include "utils/memalloc.h"
#include "utils/hash_functions.h"
#include "solvers/cdcl/gates_hash_table.h"



/*******************************
 *  OPERATIONS ON DESCRIPTORS  *
 ******************************/

/*
 * Allocate a descriptor or linked descriptor for n literals
 * - n = indegree + outdegree
 */
static inline boolgate_t *alloc_descriptor(uint32_t n) {
  return (boolgate_t *) safe_malloc(sizeof(boolgate_t) + n * sizeof(literal_t));
}

static inline boolgate_t *alloc_linked_descriptor(uint32_t n) {
  lnkgate_t *tmp;
  tmp = (lnkgate_t *) safe_malloc(sizeof(lnkgate_t) + n * sizeof(literal_t));
  return &tmp->gate;
}


/*
 * Get link from a linked descriptor d
 */
static inline lnkgate_t *get_lnk(boolgate_t *d) {
  assert(d != NULL);
  return (lnkgate_t *) (((char *) d) - offsetof(lnkgate_t, gate));
}


/*
 * Allocate and initialize a gate descriptor
 * - tag = encoding of opcode + indegree + outdegree
 * - a = array of input literals (its size must be equal to indegree(tag))
 * - level = object level
 *
 * The hash field is not initialized, the output literals are initialized
 * to null_literal.
 *
 * If level>0, the descriptor is preceded by an uninitialized link pointer
 */
static boolgate_t *new_descriptor(uint32_t tag, literal_t *a, uint32_t level) {
  boolgate_t *tmp;
  uint32_t i, d, n;

  d = tag_indegree(tag);
  n = d + tag_outdegree(tag);

  if (level > 0) {
    tmp = alloc_linked_descriptor(n);
  } else {
    tmp = alloc_descriptor(n);
  }

  // copy tag and input
  tmp->tag = tag;
  for (i=0; i<d; i++) {
    tmp->lit[i] = a[i];
  }
  // output
  while (i<n) {
    tmp->lit[i] = null_literal;
    i++;
  }

  return tmp;
}


/*
 * Compute the hash code for a pair tag/input array
 * - a = array of input literals. its size must be equal to indegree(tag)
 */
static uint32_t hash(uint32_t tag, literal_t *a) {
  uint32_t n;
  n = tag_indegree(tag);
  return jenkins_hash_mix2(tag, jenkins_hash_intarray(a, n));
}


/*
 * Check whether descriptor g matches tag and input array
 */
static bool descriptor_match(boolgate_t *g, uint32_t tag, literal_t *a) {
  uint32_t i, n;

  if (g->tag != tag) return false;

  n = tag_indegree(tag);
  for (i=0; i<n; i++) {
    if (g->lit[i] != a[i]) return false;
  }

  return true;
}





/********************
 *  PUSH/POP STACK  *
 *******************/

/*
 * Initialize: empty list/no data array allocated
 */
static void init_levlist_stack(levlist_stack_t *stack) {
  stack->current_level = 0;
  stack->top_level = 0;
  stack->nlists = 0;
  stack->size = 0;
  stack->data = NULL;
}

/*
 * Delete the stack: the list elements must be deleted separately
 */
static void delete_levlist_stack(levlist_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}

/*
 * Reset the stack: the list elements must be deleted separately
 */
static void reset_levlist_stack(levlist_stack_t *stack) {
  stack->current_level = 0;
  stack->top_level = 0;
  stack->nlists = 0;
}

/*
 * Get the top-level list descriptor in stack
 * - allocate larger data array if needed
 * - requires stack->current_level > 0
 */
static levlist_t *top_list(levlist_stack_t *stack) {
  uint32_t i, n, k;

  k = stack->current_level;
  i = stack->nlists;

  assert(k > 0);

  if (k > stack->top_level) {
    // push a new list descriptor
    n = stack->size;
    if (i == n) {
      // allocate initial data array or make existing array larger
      if (n < DEF_LEVLIST_STACK_SIZE) {
        n = DEF_LEVLIST_STACK_SIZE;
      } else {
        n += n>>1;
        if (n > MAX_LEVLIST_STACK_SIZE) out_of_memory();
      }
      stack->data = (levlist_t *) safe_realloc(stack->data, n * sizeof(levlist_t));
      stack->size = n;
    }

    assert(i < n);
    stack->data[i].level = k;
    stack->data[i].list = NULL;
    stack->nlists = i+1;
    stack->top_level = k;

    return stack->data + i;

  }

  assert(i>0);
  return stack->data + (i - 1);
}


/*
 * Add a newly allocated linked descriptor into the current-level's list.
 * Allocate stack and lists if required
 * - current level must be positive
 * - g must be allocated via alloc_linked_descriptor
 */
static void push_linked_descriptor(levlist_stack_t *stack, boolgate_t *g) {
  levlist_t *d;
  lnkgate_t *lnk;

  d = top_list(stack);
  assert(d->level == stack->current_level);
  // add g first into list d
  lnk = get_lnk(g);
  lnk->next = d->list;
  d->list = lnk;
}



/*
 * Pop: remove the top-list
 */
static void remove_top_list(levlist_stack_t *stack) {
  uint32_t i;

  assert(stack->nlists > 0);

  i = stack->nlists - 1;
  stack->nlists = i;
  if (i == 0) {
    // last list removed
    stack->top_level = 0;
  } else {
    stack->top_level = stack->data[i-1].level;
  }
}




/***************************
 *  HASH TABLE OPERATIONS  *
 **************************/

/*
 * Initialize tbl
 * - make data small to save memory if the table is never used
 * - set resize_threshold low to trigger a resize on the first addition
 */
static void init_gate_htbl(gate_htbl_t *tbl) {
  tbl->data = (boolgate_t **) safe_malloc(sizeof(boolgate_t*));
  tbl->data[0] = NULL;
  tbl->size = 1;
  tbl->nelems = 0;
  tbl->ndeleted = 0;
  tbl->resize_threshold = 0;
  tbl->cleanup_threshold = 0;
}


/*
 * Check whether a descriptor pointer is non-deleted and non-null
 * - i.e., check g == 0 or g == 1
 */
static inline bool live_descriptor(boolgate_t *g) {
  return ((size_t) g)>>1 != 0;
}


/*
 * Delete all descriptors in tbl then delete tbl->data
 * - make sure all linked descriptors (anything created at level>0)
 *   have been removed first
 */
static void delete_gate_htbl(gate_htbl_t *tbl) {
  uint32_t i, n;
  boolgate_t *d;

  n = tbl->size;
  for (i=0; i<n; i++) {
    d = tbl->data[i];
    if (live_descriptor(d)) safe_free(d);
  }
  safe_free(tbl->data);
  tbl->data = NULL;
}



/*
 * Reset tbl: remove all descriptors
 * - all linked descriptors must be removed first
 */
static void reset_gate_htbl(gate_htbl_t *tbl) {
  uint32_t i, n;
  boolgate_t *d;

  n = tbl->size;
  for (i=0; i<n; i++) {
    d = tbl->data[i];
    if (live_descriptor(d)) safe_free(d);
    tbl->data[i] = NULL;
  }
  tbl->nelems = 0;
  tbl->ndeleted = 0;
}



/*
 * Store descriptor pointer d in a clean array data
 * - mask = size of data - 1 (size must be a power of 2)
 * - d->hash must be set to the correct hash-code
 * data must not contain delete DELETED_GATE mark and must have room for d
 */
static void gate_htbl_clean_copy(boolgate_t **data, boolgate_t *d, uint32_t mask) {
  uint32_t j;

  j = d->hash & mask;
  while (data[j] != NULL) {
    j++;
    j &= mask;
  }
  data[j] = d;
}


/*
 * Remove all deleted elements from tbl
 */
static void gate_htbl_cleanup(gate_htbl_t *tbl) {
  boolgate_t **tmp, *d;
  uint32_t j, n, mask;

  n = tbl->size;
  tmp = (boolgate_t **) safe_malloc(n * sizeof(boolgate_t *));
  for (j=0; j<n; j++) {
    tmp[j] = NULL;
  }

  mask = n - 1;
  for (j=0; j<n; j++) {
    d = tbl->data[j];
    if (live_descriptor(d)) {
      gate_htbl_clean_copy(tmp, d, mask);
    }
  }

  safe_free(tbl->data);
  tbl->data = tmp;
  tbl->ndeleted = 0;
}


/*
 * Remove deleted elements if deletion threshold is reached
 */
static inline void gate_htbl_cleanup_if_needed(gate_htbl_t *tbl) {
  if (tbl->ndeleted > tbl->cleanup_threshold) {
    gate_htbl_cleanup(tbl);
  }
}


/*
 * Remove all deleted elements and make the table larger
 * - new size is min(DEF_GATE_HTBL_SIZE, 2 * current_size)
 */
static void gate_htbl_extend(gate_htbl_t *tbl) {
  boolgate_t **tmp, *d;
  uint32_t j, n, new_size, mask;

  n = tbl->size;
  new_size = n << 1;
  if (new_size < DEF_GATE_HTBL_SIZE) {
    new_size = DEF_GATE_HTBL_SIZE;
  } else if (new_size >= MAX_GATE_HTBL_SIZE) {
    out_of_memory();
  }

  tmp = (boolgate_t **) safe_malloc(new_size * sizeof(boolgate_t *));
  for (j=0; j<new_size; j++) {
    tmp[j] = NULL;
  }

  mask = new_size - 1;
  for (j=0; j<n; j++) {
    d = tbl->data[j];
    if (live_descriptor(d)) {
      gate_htbl_clean_copy(tmp, d, mask);
    }
  }

  safe_free(tbl->data);
  tbl->data = tmp;
  tbl->ndeleted = 0;
  tbl->size = new_size;

  tbl->resize_threshold = (uint32_t)(new_size * GATE_HTBL_RESIZE_RATIO);
  tbl->cleanup_threshold = (uint32_t)(new_size * GATE_HTBL_CLEANUP_RATIO);
}


/*
 * Remove d from the table. d must be present and d->hash must be set
 */
static void gate_htbl_remove(gate_htbl_t *tbl, boolgate_t *d) {
  uint32_t mask, j;

  mask = tbl->size - 1;
  j = d->hash & mask;
  while (tbl->data[j] != d) {
    j ++;
    j &= mask;
  }
  tbl->data[j] = DELETED_GATE;
  tbl->nelems --;
  tbl->ndeleted ++;
}


/*
 * Remove and delete all elements in the given list
 * - list must not be NULL
 */
static void gate_htbl_remove_list(gate_htbl_t *tbl, lnkgate_t *list) {
  lnkgate_t *aux;

  assert(list != NULL);
  do {
    aux = list->next;
    gate_htbl_remove(tbl, &list->gate);
    safe_free(list);
    list = aux;
  } while (list != NULL);
}





/***********
 *  TABLE  *
 **********/

/*
 * Initialize table: memory for stack and hash-table is not
 * allocated yet.
 */
void init_gate_table(gate_table_t *table) {
  init_levlist_stack(&table->stack);
  init_gate_htbl(&table->htbl);
}

/*
 * Delete table
 */
void delete_gate_table(gate_table_t *table) {
  levlist_stack_t *stack;
  uint32_t i;

  stack = &table->stack;
  for (i = 0; i<stack->nlists; i++) {
    gate_htbl_remove_list(&table->htbl, stack->data[i].list);
  }
  delete_levlist_stack(stack);
  delete_gate_htbl(&table->htbl);
}


/*
 * Empty the table: remove all elements
 */
void reset_gate_table(gate_table_t *table) {
  levlist_stack_t *stack;
  uint32_t i;

  stack = &table->stack;
  for (i = 0; i<stack->nlists; i++) {
    gate_htbl_remove_list(&table->htbl, stack->data[i].list);
  }
  reset_gate_htbl(&table->htbl);
  reset_levlist_stack(stack);
}


/*
 * Pop: remove and delete all elements in the top-list if it has level == current_level
 */
void gate_table_pop(gate_table_t *table) {
  levlist_stack_t *stack;
  uint32_t i;

  assert(table->stack.current_level > 0);

  stack = &table->stack;
  if (stack->current_level == stack->top_level) {
    assert(stack->nlists > 0);
    i = stack->nlists - 1;
    assert(stack->data[i].level == stack->current_level);
    gate_htbl_remove_list(&table->htbl, stack->data[i].list);
    gate_htbl_cleanup_if_needed(&table->htbl);
    remove_top_list(stack);
  }

  stack->current_level --;
}


/*
 * Search for a descriptor that matches tag and input literals in a
 * - the size of a must be indegree(tag)
 * - return NULL if no match is found
 */
boolgate_t *gate_table_find(gate_table_t *table, uint32_t tag, literal_t *a) {
  gate_htbl_t *htbl;
  uint32_t j, h, mask;
  boolgate_t *d;

  htbl = &table->htbl;
  assert(htbl->nelems + htbl->ndeleted < htbl->size);

  mask = htbl->size - 1;
  h = hash(tag, a);
  j = h & mask;
  for (;;) {
    d = htbl->data[j];
    if (d == NULL || (d != DELETED_GATE && d->hash == h && descriptor_match(d, tag, a))) {
      return d;
    }
    j ++;
    j &= mask;
  }
}


/*
 * Find or create a descriptor with the given tag/input literals
 * - if the descriptor is new, then its output literals are initialized to null_literal
 */
boolgate_t *gate_table_get(gate_table_t *table, uint32_t tag, literal_t *a) {
  gate_htbl_t *htbl;
  uint32_t k, j, h, mask, level;
  boolgate_t *d;

  htbl = &table->htbl;
  assert(htbl->nelems + htbl->ndeleted < htbl->size);

  mask = htbl->size - 1;
  h = hash(tag, a);
  j = h & mask;
  for (;;) {
    d = htbl->data[j];
    if (d == NULL) goto add;
    if (d == DELETED_GATE) break;
    if (d->hash == h && descriptor_match(d, tag, a)) goto found;
    j ++;
    j &= mask;
  }

  // htbl->data[j] = where new descriptor can be added
  k = j;
  for (;;) {
    k ++;
    k &= mask;
    d = htbl->data[k];
    if (d == NULL) {
      htbl->ndeleted --;
      goto add;
    }
    if (d != DELETED_GATE && d->hash == h && descriptor_match(d, tag, a)) goto found;
  }

 add:
  level = table->stack.current_level;
  d = new_descriptor(tag, a, level);
  d->hash = h;
  if (level > 0) {
    push_linked_descriptor(&table->stack, d);
  }
  htbl->data[j] = d;
  htbl->nelems ++;
  if (htbl->nelems + htbl->ndeleted > htbl->resize_threshold) {
    gate_htbl_extend(htbl);
  }

 found:
  return d;
}



/*
 * Find and get for (op a b) and (op a b c)
 */
boolgate_t *gate_table_find2(gate_table_t *table, uint32_t tag, literal_t a, literal_t b) {
  literal_t aux[2];

  assert(tag_indegree(tag) == 2);

  aux[0] = a;
  aux[1] = b;
  return gate_table_find(table, tag, aux);
}

boolgate_t *gate_table_get2(gate_table_t *table, uint32_t tag, literal_t a, literal_t b) {
  literal_t aux[2];

  assert(tag_indegree(tag) == 2);

  aux[0] = a;
  aux[1] = b;
  return gate_table_get(table, tag, aux);
}

boolgate_t *gate_table_find3(gate_table_t *table, uint32_t tag, literal_t a, literal_t b, literal_t c) {
  literal_t aux[3];

  assert(tag_indegree(tag) == 3);

  aux[0] = a;
  aux[1] = b;
  aux[2] = c;
  return gate_table_find(table, tag, aux);
}

boolgate_t *gate_table_get3(gate_table_t *table, uint32_t tag, literal_t a, literal_t b, literal_t c) {
  literal_t aux[3];

  assert(tag_indegree(tag) == 3);

  aux[0] = a;
  aux[1] = b;
  aux[2] = c;
  return gate_table_get(table, tag, aux);
}


