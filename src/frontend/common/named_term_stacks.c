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
 * STACKS TO DEAL WITH NAMED TERMS
 */

#include "frontend/common/named_term_stacks.h"
#include "utils/memalloc.h"
#include "utils/refcount_strings.h"

/*
 * Initialize: nothing allocated yet
 */
void init_named_term_stack(named_term_stack_t *s) {
  s->data = NULL;
  s->top = 0;
  s->size = 0;
}


/*
 * Make room for named pairs to be added
 */
static void extend_named_term_stack(named_term_stack_t *s) {
  uint32_t n;

  n = s->size;
  if (n == 0) {
    n = DEF_NAMED_TERM_STACK_SIZE;
    assert(n <= MAX_NAMED_TERM_STACK_SIZE);
    s->data = (named_term_t *) safe_malloc(n * sizeof(named_term_t));
    s->size = n;
  } else {
    n += (n >> 1) + 1;
    if (n > MAX_NAMED_TERM_STACK_SIZE) {
      out_of_memory();
    }
    s->data = (named_term_t *) safe_realloc(s->data, n * sizeof(named_term_t));
    s->size = n;
  }
}


/*
 * Push the pair <t, name>
 * - name must be a refcount string
 * - its reference counter is incremented
 */
void push_named_term(named_term_stack_t *s, term_t t, char *name) {
  uint32_t i;

  i = s->top;
  if (i == s->size) {
    extend_named_term_stack(s);
  }
  assert(i < s->size);
  s->data[i].term = t;
  s->data[i].name = name;
  string_incref(name);
  s->top = i+1;
}


/*
 * Remove pairs from the stack s
 * - n = new top: all pairs in s->data[0 ... n-1] are kept
 */
void pop_named_terms(named_term_stack_t *s, uint32_t n) {
  uint32_t i;

  assert(n <= s->top);

  i = s->top;
  while (i > n) {
    i --;
    string_decref(s->data[i].name);
  }
  s->top = n;
}


/*
 * Deletion
 */
void delete_named_term_stack(named_term_stack_t *s) {
  uint32_t i;

  i = s->top;
  while (i > 0) {
    i --;
    string_decref(s->data[i].name);
  }
  safe_free(s->data);
  s->data = NULL;
}


/*
 * Reset: remove all names then re-initialize
 */
void reset_named_term_stack(named_term_stack_t *s) {
  delete_named_term_stack(s);
  assert(s->data == NULL);
  s->top = 0;
  s->size = 0;
}

