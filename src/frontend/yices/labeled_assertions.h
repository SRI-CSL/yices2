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

/*
 * This extends named_term_stack with push/pop
 * and with a hash table to check whether a label is
 * used in the table. We use this because Yices has a different
 * name space for assertions.
 */

#ifndef __LABELED_ASSERTIONS_H
#define __LABELED_ASSERTIONS_H

#include <stdint.h>
#include <stdbool.h>

#include "frontend/common/named_term_stacks.h"

/*
 * For every push, we keep track of the number of labeled assertions.
 * - this is stored in data[0 ... top-1] where top = number of calls to push
 */
typedef struct labeled_assertion_trail_s {
  uint32_t *data;
  uint32_t top;
  uint32_t size;
} labeled_assertion_trail_t;

#define DEF_LABELED_ASSERTION_TRAIL_SIZE 256
#define MAX_LABELED_ASSERTION_TRAIL_SIZE (UINT32_MAX/sizeof(uint32_t))

/*
 * Index = a hash table
 * - entry in the table are 32bit signed integers
 * - data[k] = -1 means empty
 *   data[k] = -2 means deleted
 *   data[k] = i >= 0 means that i is an index in the named_term_stack
 */
typedef struct label_index_s {
  int32_t *data;
  uint32_t size;
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} label_index_t;

#define DEF_LABEL_INDEX_SIZE 64
#define MAX_LABEL_INDEX_SIZE (UINT32_MAX/sizeof(int32_t))

#define LABEL_INDEX_RESIZE_RATIO 0.65
#define LABEL_INDEX_CLEANUP_RATIO 0.20


/*
 * Assertion stack:
 * - a named stack
 * - a trail
 * - a index array
 */
typedef struct labeled_assertion_stack_s {
  named_term_stack_t assertions;
  labeled_assertion_trail_t trail;
  label_index_t index;
} labeled_assertion_stack_t;


/*
 * Initialize: nothing is allocated yet
 */
extern void init_labeled_assertion_stack(labeled_assertion_stack_t *s);

/*
 * Delete: free memory
 */
extern void delete_labeled_assertion_stack(labeled_assertion_stack_t *s);

/*
 * Reset: empty the stack and index and trail
 */
extern void reset_labeled_assertion_stack(labeled_assertion_stack_t *s);

/*
 * Add pair <t, name> to the stack
 * - name must be a refcount string.
 * - its reference counter is incremented
 */
extern void add_labeled_assertion(labeled_assertion_stack_t *s, term_t t, char *name);

/*
 * Start a new level
 */
extern void labeled_assertions_push(labeled_assertion_stack_t *s);

/*
 * Remove the top level
 */
extern void labeled_assertions_pop(labeled_assertion_stack_t *s);

/*
 * Check whether the trail is empty
 */
static inline bool labeled_assertions_empty_trail(const labeled_assertion_stack_t *s) {
  return s->trail.top == 0;
}

/*
 * Check whether there are some assertions
 */
static inline bool labeled_assertion_stack_is_empty(const labeled_assertion_stack_t *s) {
  return named_term_stack_is_empty(&s->assertions);
}


/*
 * Check whether name is present
 */
extern bool labeled_assertions_has_name(const labeled_assertion_stack_t *s, const char *name);



#endif /* __LABELED_ASSERTIONS_H */
