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
 * Queue for storing assertions sent by egraph to theory solvers.
 *
 * The assertions are of the following forms:
 *   v1 == v2
 *   v1 != v2 with a hint
 *   distinct v[0] ... v[n-1] with a hint
 * where v1, v2, etc. are theory variable. The hint is a composite_t
 * object that the egraph requires to generate explanations.
 *
 * Each assertion is stored as the following data
 * - tag: encode the assertion type (eq, diseq, distinct)
 *        and number of variables (2 or n)
 * - hint: is stored as is for explanation
 * - v[0 ... n-1]: the variables involved
 */


#include "solvers/egraph/egraph_assertion_queues.h"
#include "utils/memalloc.h"


/*
 * Initialize queue: nothing is allocated yet
 */
void init_eassertion_queue(eassertion_queue_t *queue) {
  queue->size = 0;
  queue->top = 0;
  queue->data = NULL;
}


/*
 * Delete
 */
void delete_eassertion_queue(eassertion_queue_t *queue) {
  safe_free(queue->data);
  queue->data = NULL;
}



/*
 * Make enough room in the queue for an object of the given size (in bytes)
 */
static void resize_eassertion_queue(eassertion_queue_t *queue, uint32_t size) {
  uint32_t d, n;

  d = queue->top + size;
  n = queue->size;
  if (d > n) {
    // make n bigger
    if (n == 0) {
      // first allocation
      n = DEF_EASSERTION_QUEUE_SIZE;
    } else {
      n += n>>1; // try to make n 50% larger
    }
    if (d > n) {
      n = d;
    }
    if (n >= MAX_EASSERTION_QUEUE_SIZE) {
      out_of_memory();
    }
    queue->data = (uint8_t* ) safe_realloc(queue->data, n);
    queue->size = n;
  }
}


/*
 * Allocate an assertion descriptor of arity n
 */
static eassertion_t *eassertion_alloc(eassertion_queue_t *queue, uint32_t n) {
  uint8_t *ptr;
  uint32_t size;

  size = sizeof_eassertion(n);
  resize_eassertion_queue(queue, size);
  ptr = queue->data + queue->top;
  queue->top += size;
  assert(queue->top <= queue->size);

  return (eassertion_t *) ptr;
}


/*
 * Add x1 == x2 to the queue
 */
void eassertion_push_eq(eassertion_queue_t *queue, thvar_t x1, thvar_t x2, int32_t id) {
  eassertion_t *a;

  a = eassertion_alloc(queue, 2);
  a->hint = NULL;
  a->tag = mk_var_eq_tag();
  a->id = id;
  a->var[0] = x1;
  a->var[1] = x2;
}


/*
 * Add x1 != x2 to the queue, with hint for explanations
 */
void eassertion_push_diseq(eassertion_queue_t *queue, thvar_t x1, thvar_t x2, composite_t *hint) {
  eassertion_t *a;

  a = eassertion_alloc(queue, 2);
  a->hint = hint;
  a->tag = mk_var_diseq_tag();
  a->id = 0;
  a->var[0] = x1;
  a->var[1] = x2;
}


/*
 * Add (distinct v[0] ... v[n-1]) to the queue with hint for explanations
 */
void eassertion_push_distinct(eassertion_queue_t *queue, uint32_t n, thvar_t *v, composite_t *hint) {
  eassertion_t *a;
  uint32_t i;

  a = eassertion_alloc(queue, n);
  a->hint = hint;
  a->id = 0;
  a->tag = mk_var_distinct_tag(n);
  for (i=0; i<n; i++) {
    a->var[i] = v[i];
  }
}
