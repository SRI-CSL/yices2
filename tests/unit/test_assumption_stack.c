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

#include <stdio.h>
#include <inttypes.h>

#include "context/assumption_stack.h"

static void show_stack_elem(FILE *f, assumption_elem_t *e) {
  fprintf(f, "{ term = t!%"PRId32", lit = l!%"PRId32", level = %"PRIu32" }", e->term, e->lit, e->level);
}

static void show_stack(FILE *f, assumption_stack_t *s) {
  uint32_t i, n;

  fprintf(f, "stack %p\n", s);
  fprintf(f, "  size  = %"PRIu32"\n", s->size);
  fprintf(f, "  top   = %"PRIu32"\n", s->top);
  fprintf(f, "  level = %"PRIu32"\n", s->level);
  n = s->top;
  if (n == 0) {
    fprintf(f, "  empty stack\n\n");
  } else {
    for (i=0; i<n; i++) {
      fprintf(f, "   data[%"PRIu32"] = ", i);
      show_stack_elem(f, s->data + i);
      fprintf(f, "\n");
    }
    fprintf(f, "\n");
  }
}

static void check_literal_present(assumption_stack_t *s, literal_t l) {
  term_t x;

  x = assumption_term_for_literal(s, l);
  if (x < 0) {
    fprintf(stderr, "*** BUG: failed to find term for literal l!%"PRId32" ***\n", l);
    exit(1);
  }
  if (x + 50 != l) {
    fprintf(stderr, "*** BUG: got term t!%"PRId32" for literal l!%"PRId32" (expected t!%"PRId32") ***\n",
	    x, l, l-50);
    exit(1);
  }
  printf("term for literal l!%"PRId32" = t!%"PRId32"\n", l, x);
}

static void check_term_present(assumption_stack_t *s, term_t x) {
  literal_t l;

  l = assumption_literal_for_term(s, x);
  if (l < 0) {
    fprintf(stderr, "*** BUG: failed to find literal for term t!%"PRId32" ***\n", x);
    exit(1);
  }
  if (l != x + 50) {
    fprintf(stderr, "*** BUG: got literal l!%"PRId32" for term t!%"PRId32" (expected l!%"PRId32") ***\n",
	    l, x, x+50);
    exit(1);
  }
  printf("literal for term t!%"PRId32" = l!%"PRId32"\n", x, l);
}

static void check_literal_absent(assumption_stack_t *s, literal_t l) {
  term_t x;

  x = assumption_term_for_literal(s, l);
  if (x >= 0) {
    fprintf(stderr, "*** BUG: got term t!%"PRId32" for literal l!%"PRId32" (expected nothing) ***\n",
	    x, l);
    exit(1);
  }
  printf("literal l!%"PRId32" not in the stack\n", l);
}

static void check_term_absent(assumption_stack_t *s, term_t x) {
  literal_t l;

  l = assumption_literal_for_term(s, x);
  if (l >= 0) {
    fprintf(stderr, "*** BUG: got literal l!%"PRId32" for term t!%"PRId32" (expected nothing) ***\n",
	    l, x);
    exit(1);
  }
  printf("term t!%"PRId32" not in the stack\n", x);
}

static void check_entry(assumption_stack_t *s, term_t x, literal_t l) {
  term_t x1;
  literal_t l1;

  x1 = assumption_term_for_literal(s, l);
  l1 = assumption_literal_for_term(s, x);

  if (x1 != x) {
    fprintf(stderr, "*** BUG: got term %"PRId32" for literal l!%"PRId32" (expected %"PRId32") ***\n",
	    x1, l, x);
    exit(1);
  }
  if (l1 != l) {
    fprintf(stderr, "*** BUG: got literal %"PRId32" for term t!%"PRId32" (expected %"PRId32") ***\n",
	    l1, x, l);
    exit(1);
  }
}

static assumption_stack_t stack;

int main(void) {
  int32_t i;
  
  init_assumption_stack(&stack);
  printf("--- initial stack ---\n");
  show_stack(stdout, &stack);

  assumption_stack_push(&stack);
  assumption_stack_push(&stack);
  printf("--- after push push ---\n");
  show_stack(stdout, &stack);

  for (i=1; i<=10; i++) {
    assumption_stack_add(&stack, i, 50+i);
  }
  assumption_stack_push(&stack);
  for (i=11; i<=20; i++) {
    assumption_stack_add(&stack, i, 50+i);
  }
 
  printf("--- after 20 additions ---\n");
  show_stack(stdout, &stack);

  printf("--- queries ---\n");
  for (i=1; i<=20; i++) {
    check_term_present(&stack, i);
  }
  check_term_absent(&stack, 51);
  printf("\n");
  for (i=1; i<=20; i++) {
    check_literal_present(&stack, 50+i);
  }
  check_literal_absent(&stack, 1);
  
  printf("\n--- after push ---\n");
  assumption_stack_push(&stack);
  show_stack(stdout, &stack);

  printf("--- after pop ---\n");
  assumption_stack_pop(&stack);
  show_stack(stdout, &stack);
  
  printf("--- after pop ---\n");
  assumption_stack_pop(&stack);
  show_stack(stdout, &stack);

  printf("\n");
  for (i=1; i<=10; i++) {
    check_term_present(&stack, i);
  }
  for (i=11; i<=20; i++) {
    check_term_absent(&stack, i);
  }
  printf("\n");
  for (i=1; i<=10; i++) {
    check_literal_present(&stack, 50+i);
  }
  for (i=11; i<=20; i++) {
    check_literal_absent(&stack, 50+i);
  }

  printf("\n--- after pop ---\n");
  assumption_stack_pop(&stack);
  show_stack(stdout, &stack);

  for (i=1; i<=20; i++) {
    check_term_absent(&stack, i);
  }
  printf("\n");
  for (i=1; i<=20; i++) {
    check_literal_absent(&stack, 50+i);
  }
  
  printf("\n--- after reset ---\n");
  reset_assumption_stack(&stack);
  show_stack(stdout, &stack);

  // force resize
  for (i=1; i<=1000; i++) {
    assumption_stack_add(&stack, i, 1050+i);
  }
  printf("\n--- checking 1000 entries ---\n");
  for (i=1; i<=1000; i++) {
    check_entry(&stack, i, 1050+i);
  }
  printf("\nDONE\n");
  
  delete_assumption_stack(&stack);

  return 0;
}
