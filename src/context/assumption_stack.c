/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2018 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * STACK TO STORE ASSUMPTIONS IN A CONTEXT
 */

#include <assert.h>
#include <stdbool.h>

#include "context/assumption_stack.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"


/*
 * INDEX STRUCTURES
 */

/*
 * Match functions: it takes a key k and an index i and checks whether
 * the assumption at index i in the stack has key k. For the first
 * variant, the key is a literal. For the second variant, the key
 * is a term.
 */
typedef bool (*match_fun_t)(const assumption_elem_t *a, int32_t key, int32_t i);

static bool match_literal(const assumption_elem_t *a, int32_t key, int32_t i) {
  assert(i >= 0);
  return a[i].lit == key;
}

static bool match_term(const assumption_elem_t *a, int32_t key, int32_t i) {
  assert(i >= 0);
  return a[i].term == key;
}

/*
 * Get key functions: takes an index i and either returns the literal or the term.
 */
typedef int32_t (*get_key_fun_t)(const assumption_elem_t *a, int32_t i);

static int32_t key_literal(const assumption_elem_t *a, int32_t i) {
  assert(i >= 0);
  return a[i].lit;
}

static int32_t key_term(const assumption_elem_t *a, int32_t i) {
  assert(i >= 0);
  return a[i].term;
}


/*
 * For debugging: check whether n is 0 or a power of 2
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialize an index: nothing allocated
 */
static void init_hash_index(hash_index_t *index) {
  index->data = NULL;
  index->size = 0;
  index->nelems = 0;
  index->ndeleted = 0;
  index->resize_threshold = 0;
  index->cleanup_threshold = 0;
}


/*
 * Free memory
 */
static void delete_hash_index(hash_index_t *index) {
  safe_free(index->data);
  index->data = NULL;
}


/*
 * Reset: empty the index
 */
static void reset_hash_index(hash_index_t *index) {
  uint32_t i, n;

  n = index->size;
  for (i=0; i<n; i++) {
    index->data[i] = -1;
  }
  index->nelems = 0;
  index->ndeleted = 0;
}


/*
 * Allocate an array of n elements and initialize all of them to -1
 */
static int32_t *new_index_array(uint32_t n) {  
  int32_t *tmp;
  uint32_t i;

  assert(is_power_of_two(n));
  tmp = (int32_t *) safe_malloc(n * sizeof(int32_t));
  for (i=0; i<n; i++) {
    tmp[i] = -1;
  }
  return tmp;
}

/*
 * Add mapping [key -> x] into array a
 * - x must be non-negative
 * - mask = size of a - 1 (the size of a is a power of 2)
 * - a must not be full
 */
static void clean_array_add(int32_t *a, int32_t key, int32_t x, uint32_t mask) {
  uint32_t i;

  assert(x >= 0);

  i = jenkins_hash_int32(key) & mask;
  while (a[i] >= 0) {
    i ++;
    i &= mask;
  }
  a[i] = x;
}


/*
 * First allocation
 */
static void alloc_hash_index(hash_index_t *index) {
  uint32_t n;

  assert(index->size == 0);

  n = DEF_ASSUMPTION_INDEX_SIZE;
  index->data = new_index_array(n);
  index->size = n;
  index->resize_threshold = (uint32_t)(n * ASSUMPTION_INDEX_RESIZE_RATIO);
  index->cleanup_threshold = (uint32_t)(n * ASSUMPTION_INDEX_CLEANUP_RATIO);
}


/*
 * Double the hash table size and copy its content into a fresh array
 * - key returns the key for element of index i in the stack
 */
static void resize_hash_index(hash_index_t *index, const assumption_elem_t *a, get_key_fun_t key) {
  uint32_t i, n, new_size, mask;
  int32_t x, k;
  int32_t *tmp;

  n = index->size;
  new_size = n << 1;
  if (new_size >= MAX_ASSUMPTION_INDEX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(new_size));

  tmp = new_index_array(new_size);
  mask = new_size - 1;
  for (i=0; i<n; i++) {
    x = index->data[i];
    if (x >= 0) {
      k = key(a, x);
      clean_array_add(tmp, k, x, mask);
    }
  }

  safe_free(index->data);

  index->data = tmp;
  index->size = new_size;
  index->ndeleted = 0;
  index->resize_threshold = (uint32_t) (new_size * ASSUMPTION_INDEX_RESIZE_RATIO);
  index->cleanup_threshold = (uint32_t) (new_size * ASSUMPTION_INDEX_CLEANUP_RATIO);
}


/*
 * Cleanup the table: remove the deletion marks (i.e., elements set to -2)
 */
static void cleanup_hash_index(hash_index_t *index, const assumption_elem_t *a, get_key_fun_t key) {
  uint32_t i, n, mask;
  int32_t x, k;
  int32_t *tmp;

  n = index->size;
  tmp = new_index_array(n);
  mask = n - 1;
  for (i=0; i<n; i++) {
    x = index->data[i];
    if (x >= 0) {
      k = key(a, x);
      clean_array_add(tmp, k, x, mask);
    }
  }

  safe_free(index->data);
  index->data = tmp;
  index->ndeleted = 0;
}


/*
 * Check whether we need to resize/cleanup
 */
static inline bool hash_index_needs_resize(const hash_index_t *index) {
  return index->nelems + index->ndeleted >= index->resize_threshold;
}

static inline bool hash_index_needs_cleanup(const hash_index_t *index) {
  return index->ndeleted >= index->cleanup_threshold && index->ndeleted > 0;
}


/*
 * Search for an entry mapped to k in the index
 * - return -1 if not found
 */
static int32_t find_in_hash_index(const hash_index_t *index, int32_t k, const assumption_elem_t *a, match_fun_t match) {
  uint32_t i, mask;
  int32_t j;

  assert(is_power_of_two(index->size) && index->size > 0);

  mask = index->size - 1;
  i = jenkins_hash_int32(k) & mask;
  for (;;) {
    j = index->data[i];
    if (j == -1 || (j >= 0 && match(a, k, j))) break;
    i ++;
    i &= mask;
  }
  return j;
}


/*
 * Remove entry (k, x) from the index
 * - no change if the entry is not present
 * - note: there's at most one occurrence of x in the index
 */
static void remove_from_hash_index(hash_index_t *index, int32_t k, int32_t x) {
  uint32_t i, mask;
  int32_t j;

  assert(is_power_of_two(index->size) && index->size > 0);
  assert(x >= 0);
  
  mask = index->size - 1;
  i = jenkins_hash_int32(k) & mask;
  for (;;) {
    j = index->data[i];
    if (j == x) break;
    if (j == -1) return;
    i ++;
    i &= mask;
  }

  index->data[i] = -2;
  index->nelems --;
  index->ndeleted ++;
}


/*
 * Add (k, x) to the index
 * - no change if there's already an entry for k
 */
static void add_to_hash_index(hash_index_t *index, int32_t k, int32_t x, const assumption_elem_t *a, match_fun_t match) {
  uint32_t i, mask;
  int32_t j, free;

  assert(is_power_of_two(index->size) && index->size > 0);
  assert(x >= 0);

  free = -1;
  mask = index->size - 1;
  i = jenkins_hash_int32(k) & mask;
  for (;;) {
    j = index->data[i];
    if (j < 0) {
      if (free < 0) free = i; // free slot
      if (j == -1) break;
    } else if (match(a, k, j)) {
      return;
    }
    i ++;
    i &= mask;
  }

  assert(0 <= free && free < (int32_t) index->size && index->data[free] < 0);

  if (index->data[free] == -2) {
    assert(index->ndeleted > 0);
    index->ndeleted --;
  }

  index->data[free] = x;
  index->nelems ++;
}


/*
 * ASSUMPTION STACK
 */

/*
 * Initialize the stack:
 * - nothing is allocated yet
 * - level is 0
 */
void init_assumption_stack(assumption_stack_t *stack) {
  stack->data = NULL;
  stack->size = 0;
  stack->top = 0;
  stack->level = 0;
  init_hash_index(&stack->lit_index);
  init_hash_index(&stack->term_index);
}

/*
 * Free memory
 */
void delete_assumption_stack(assumption_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
  delete_hash_index(&stack->lit_index);
  delete_hash_index(&stack->term_index);
}

/*
 * Empty the stack
 */
void reset_assumption_stack(assumption_stack_t *stack) {
  stack->top = 0;
  stack->level = 0;
  reset_hash_index(&stack->lit_index);
  reset_hash_index(&stack->term_index);
}


/*
 * Make the stack larger
 */
static void extend_assumption_stack(assumption_stack_t *stack) {
  uint32_t n;

  n = stack->size;
  if (n == 0) {
    // first allocation
    n = DEF_ASSUMPTION_STACK_SIZE;
    assert(n <= MAX_ASSUMPTION_STACK_SIZE);
    stack->data = (assumption_elem_t *) safe_malloc(n * sizeof(assumption_elem_t));
    stack->size = n;
    alloc_hash_index(&stack->lit_index);
    alloc_hash_index(&stack->term_index);

  } else {
    // try to make the stack 50% larger
    n += (n >> 1);
    if (n > MAX_ASSUMPTION_STACK_SIZE) {
      out_of_memory();
    }
    assert(n > stack->size);

    stack->data = (assumption_elem_t *) safe_realloc(stack->data, n * sizeof(assumption_elem_t));
    stack->size = n;
  }
}

/*
 * Close the current level and remove all assumptions added at this
 * level. stack->level must be positive.
 */
void assumption_stack_pop(assumption_stack_t *stack) {
  uint32_t i;

  assert(stack->level > 0);

  i = stack->top;
  while (i>0 && stack->data[i-1].level == stack->level) {
    i --;
    remove_from_hash_index(&stack->lit_index, stack->data[i].lit, i);
    remove_from_hash_index(&stack->term_index, stack->data[i].term, i);
  }

  stack->top = i;
  stack->level --;

  if (hash_index_needs_cleanup(&stack->lit_index)) {
    cleanup_hash_index(&stack->lit_index, stack->data, key_literal);
  }
  if (hash_index_needs_cleanup(&stack->term_index)) {
    cleanup_hash_index(&stack->term_index, stack->data, key_term);
  }
}


/*
 * Add a pair (t, l) on top of the stack: at the current level
 */
void assumption_stack_add(assumption_stack_t *stack, term_t t, literal_t l) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_assumption_stack(stack);
  }
  assert(i < stack->size);

  stack->data[i].term = t;
  stack->data[i].lit = l;
  stack->data[i].level = stack->level;
  stack->top = i+1;
  
  add_to_hash_index(&stack->lit_index, l, i, stack->data, match_literal);
  add_to_hash_index(&stack->term_index, t, i, stack->data, match_term);

  if (hash_index_needs_resize(&stack->lit_index)) {
    resize_hash_index(&stack->lit_index, stack->data, key_literal);
  }
  if (hash_index_needs_resize(&stack->term_index)) {
    resize_hash_index(&stack->term_index, stack->data, key_term);
  }
}


/*
 * Search for a term t attached to literal l in the stack:
 * - this searches for an element of the form (t, l, k) in the stack
 *   and return t;
 * - if several terms are mapped to l, the function returns the first one
 *   (i.e., with the lowest level k).
 * - if there's no such element, the function returns NULL_TERM (i.e., -1)
 */
term_t assumption_term_for_literal(const assumption_stack_t *stack, literal_t l) {
  int32_t i;
  term_t t;

  t = NULL_TERM;
  if (stack->size > 0) {
    i = find_in_hash_index(&stack->lit_index, l, stack->data, match_literal);
    if (i >= 0) {
      assert(i < stack->size);
      t = stack->data[i].term;
    }
  }

  return t;
}

/*
 * Search for a literal l attached to term t in the stack:
 * - search for a triple (t, l, k) in the stack and return l
 * - return null_literal if there's no such triple
 */
literal_t assumption_literal_for_term(const assumption_stack_t *stack, term_t t) {
  int32_t i;
  literal_t l;

  l = null_literal;
  if (stack->size > 0) {
    i = find_in_hash_index(&stack->term_index, t, stack->data, match_term);
    if (i >= 0) {
      assert(i < stack->size);
      l = stack->data[i].lit;
    }
  }
  return l;
}

