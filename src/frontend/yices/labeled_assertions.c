/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
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
 * STACK OF NAMED ASSERTIONS
 */

#include <assert.h>
#include <string.h>

#include "frontend/yices/labeled_assertions.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"



/*********
 * TRAIL *
 ********/

static void init_labeled_assertion_trail(labeled_assertion_trail_t *stack) {
  stack->data = NULL;
  stack->top = 0;
  stack->size = 0;
}

static void reset_labeled_assertion_trail(labeled_assertion_trail_t *stack) {
  stack->top = 0;
}

static void delete_labeled_assertion_trail(labeled_assertion_trail_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Make room on the stack
 */
static void extend_labeled_assertion_trail(labeled_assertion_trail_t *stack) {
  uint32_t n;

  n = stack->size;
  if (n == 0) {
    n = DEF_LABELED_ASSERTION_TRAIL_SIZE;
    assert(n <= MAX_LABELED_ASSERTION_TRAIL_SIZE);
    stack->data = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
    stack->size = n;
  } else {
    n += (n >> 1) + 2;
    assert(n > stack->size);

    if (n > MAX_LABELED_ASSERTION_TRAIL_SIZE) {
      out_of_memory();
    }
    stack->data = (uint32_t *) safe_realloc(stack->data, n * sizeof(uint32_t));
    stack->size = n;
  }
}


/*
 * Push an integer on the stack
 */
static void labeled_assertion_trail_push(labeled_assertion_trail_t *stack, uint32_t k) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_labeled_assertion_trail(stack);
  }
  assert(i < stack->size);
  stack->data[i] = k;
  stack->top = i+1;
}


/*
 * Get the top element and pop
 */
static uint32_t labeled_assertion_trail_pop(labeled_assertion_trail_t *stack) {
  assert(stack->top > 0);
  stack->top --;
  return stack->data[stack->top];
}


/***********
 *  INDEX  *
 **********/

/*
 * For debugging: check whether n is a power of two
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif

/*
 * Initialize: nothing is allocated yet
 */
static void init_label_index(label_index_t *index) {
  index->data = NULL;
  index->size = 0;
  index->nelems = 0;
  index->ndeleted = 0;
  index->resize_threshold = 0;
  index->cleanup_threshold = 0;
}

/*
 * Delete
 */
static void delete_label_index(label_index_t *index) {
  safe_free(index->data);
  index->data = NULL;
}

/*
 * Reset: empty the index
 */
static void reset_label_index(label_index_t *index) {
  uint32_t i, n;

  n = index->size;
  for (i=0; i<n; i++) {
    index->data[i] = -1;
  }
  index->nelems = 0;
  index->ndeleted = 0;
}


/*
 * First allocation
 */
static void alloc_label_index(label_index_t *index) {
  int32_t *tmp;
  uint32_t i, n;

  n = DEF_LABEL_INDEX_SIZE;
  assert(n <= MAX_LABEL_INDEX_SIZE);

  tmp = (int32_t *) safe_malloc(n * sizeof(int32_t));
  for (i=0; i<n; i++) {
    tmp[i] = -1; // empty
  }
  index->data = tmp;
  index->size = n;
  index->resize_threshold = (uint32_t) (n * LABEL_INDEX_RESIZE_RATIO);
  index->cleanup_threshold = (uint32_t) (n * LABEL_INDEX_CLEANUP_RATIO);
}


/*
 * Add entry i to array a.
 * - i must not be present
 * - name = name for this entry
 * - mask = size of a - 1; the size must be a power of two
 */
static void add_entry(int32_t *a, uint32_t mask, int32_t i, const char *name) {
  uint32_t h;

  h = jenkins_hash_string(name) & mask;
  while (a[h] >= 0) {
    h ++;
    h &= mask;
  }
  a[h] = i;
}

/*
 * Make the index twice as large. Keep the content.
 */
static void resize_label_index(label_index_t *index, const named_term_stack_t *assertions) {
  uint32_t i, n, new_size, mask;
  int32_t j;
  int32_t *tmp;

  assert(is_power_of_two(index->size));

  n = index->size;
  new_size = n << 1;
  if (new_size > MAX_LABEL_INDEX_SIZE) {
    out_of_memory();
  }

  tmp = (int32_t *) safe_malloc(new_size * sizeof(int32_t));
  for (i=0; i<new_size; i++) {
    tmp[i] = -1;
  }

  mask = new_size - 1;
  for (i=0; i<n; i++) {
    j = index->data[i];
    if (j >= 0) {
      assert(j < assertions->top);
      add_entry(tmp, mask, j, assertions->data[j].name);
    }
  }

  safe_free(index->data);
  index->data = tmp;
  index->size = new_size;
  index->ndeleted = 0;
  index->resize_threshold = (uint32_t) (new_size * LABEL_INDEX_RESIZE_RATIO);
  index->cleanup_threshold = (uint32_t) (new_size * LABEL_INDEX_CLEANUP_RATIO);
}
 

/*
 * Cleanup: remove all deletion marks
 */
static void cleanup_label_index(label_index_t *index, const named_term_stack_t *assertions) {
  uint32_t i, n, mask;
  int32_t j;
  int32_t *tmp;

  assert(is_power_of_two(index->size));

  n = index->size;
  tmp = (int32_t *) safe_malloc(n * sizeof(int32_t));
  for (i=0; i<n; i++) {
    tmp[i] = -1;
  }

  mask = n - 1;
  for (i=0; i<n; i++) {
    j = index->data[i];
    if (j >= 0) {
      assert(j < assertions->top);
      add_entry(tmp, mask, j, assertions->data[j].name);
    }
  }

  safe_free(index->data);
  index->data = tmp;
  index->ndeleted = 0;
}


/*
 * Add entry i of assertions to the index:
 * - there must not be an entry with the same name
 */
static void label_index_add(label_index_t *index, int32_t i, const named_term_stack_t *assertions) {
  uint32_t h, mask;

  assert(0 <= i && i < assertions->top);

  if (index->size == 0) {
    alloc_label_index(index);
  }

  assert(is_power_of_two(index->size));
  assert(index->ndeleted + index->nelems < index->size);

  mask  = index->size - 1;
  h = jenkins_hash_string(assertions->data[i].name) & mask;
  while (index->data[h] >= 0) {
    h ++;
    h &= mask;
  }
  
  if (index->data[h] == -2) {
    index->ndeleted --;
  }
  index->data[h] = i;
  index->nelems ++;
  if (index->nelems + index->ndeleted >= index->resize_threshold) {
    resize_label_index(index, assertions);
  }
}


/*
 * Remove entry i from the index
 * - the entry must be present
 */
static void label_index_remove(label_index_t *index, int32_t i, const named_term_stack_t *assertions) { 
  uint32_t h, mask;

  assert(0 <= i && i < assertions->top);
  assert(is_power_of_two(index->size));
  assert(index->ndeleted + index->nelems < index->size);

  mask = index->size - 1;
  h = jenkins_hash_string(assertions->data[i].name) & mask;
  while (index->data[h] != i) {
    h ++;
    h &= mask;
  }

  index->data[h] = -2;
  index->nelems --;
  index->ndeleted ++;
}


/*
 * Search for an entry with the given name
 */
static bool label_index_search(const label_index_t *index, const named_term_stack_t *assertions, const char *name) {
  uint32_t h, mask;
  int32_t j;

  if (index->nelems == 0) {
    return false;
  }

  assert(is_power_of_two(index->size));
  assert(index->ndeleted + index->nelems < index->size);

  mask = index->size - 1;
  h = jenkins_hash_string(name) & mask;

  while (index->data[h] != -1) {
    j = index->data[h];
    if (j >= 0) {
      assert(j < assertions->top);
      if (strcmp(name, assertions->data[j].name) == 0) {
	return true;
      }
    }
    h ++;
    h &= mask;
  }

  return false;
}



/****************
 *  FULL STACK  *
 ***************/

/*
 * Initialize: nothing is allocated yet
 */
void init_labeled_assertion_stack(labeled_assertion_stack_t *s) {
  init_named_term_stack(&s->assertions);
  init_labeled_assertion_trail(&s->trail);
  init_label_index(&s->index);
}

/*
 * Delete: free memory
 */
void delete_labeled_assertion_stack(labeled_assertion_stack_t *s) {
  delete_named_term_stack(&s->assertions);
  delete_labeled_assertion_trail(&s->trail);
  delete_label_index(&s->index);
}

/*
 * Reset: empty the stack and index and trail
 */
void reset_labeled_assertion_stack(labeled_assertion_stack_t *s) {
  reset_named_term_stack(&s->assertions);
  reset_labeled_assertion_trail(&s->trail);
  reset_label_index(&s->index);
}

/*
 * Add pair <t, name> to the stack
 * - name must be a refcount string.
 * - its reference counter is incremented
 */
void add_labeled_assertion(labeled_assertion_stack_t *s, term_t t, char *name) {
  int32_t i;

  i = (int32_t) named_term_stack_top(&s->assertions);
  push_named_term(&s->assertions, t, name);

  assert(s->assertions.data[i].term == t &&
	 s->assertions.data[i].name == name);
  label_index_add(&s->index, i, &s->assertions);
}

/*
 * Start a new level
 */
void labeled_assertions_push(labeled_assertion_stack_t *s) {
  uint32_t n;

  n = named_term_stack_top(&s->assertions);
  labeled_assertion_trail_push(&s->trail, n);
}

/*
 * Remove the top level
 */
void labeled_assertions_pop(labeled_assertion_stack_t *s) {
  uint32_t i, n, top;

  top = named_term_stack_top(&s->assertions);
  n = labeled_assertion_trail_pop(&s->trail);
  for (i=n; i<top; i++) {
    label_index_remove(&s->index, (int32_t) i, &s->assertions);
  }
  if (s->index.ndeleted >= s->index.cleanup_threshold) {
    cleanup_label_index(&s->index, &s->assertions);
  }
  pop_named_terms(&s->assertions, n);
}


/*
 * Check whether name is present
 */
bool labeled_assertions_has_name(const labeled_assertion_stack_t *s, const char *name) {
  return label_index_search(&s->index, &s->assertions, name);
}

