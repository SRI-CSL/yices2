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
 * DATA STRUCTURE TO STORE ASSUMPTIONS AND CORES
 */

#include <assert.h>

#include "frontend/common/assumptions_and_core.h"
#include "utils/memalloc.h"


/*
 * Allocate and initialize
 */
assumptions_and_core_t *new_assumptions(term_table_t *terms) {
  assumptions_and_core_t *a;

  a = safe_malloc(sizeof(assumptions_and_core_t));
  a->terms = terms;
  init_assumption_table(&a->table);
  init_ivector(&a->assumptions, 0);
  init_ivector(&a->core, 0);
  a->status = SMT_STATUS_IDLE;
  return a;
}

/*
 * Free the data structures
 */
void free_assumptions(assumptions_and_core_t *a) {
  a->terms = NULL;
  delete_assumption_table(&a->table);
  delete_ivector(&a->assumptions);
  delete_ivector(&a->core);
  safe_free(a);
}



/*
 * Collect all the named terms of stack as assumptions
 * - all terms in stack must be Boolean
 * - this stores all the assumptions in a->assumptions and remove duplicates if any
 */
void collect_assumptions_from_stack(assumptions_and_core_t *a, const named_term_stack_t *stack) {
  uint32_t i, n;

  n = stack->top;
  for (i=0; i<n; i++) {
    assumption_table_add(&a->table, stack->data[i].term, stack->data[i].name, true);
  }
  assumption_table_build_index(&a->table);
  collect_assumptions(&a->table, &a->assumptions);
}

/*
 * Add n signed symbols as assumptions
 * - returns an error code
 *     0 means no error
 *    -1 means undefined term (i.e., not in a->terms)
 *    -2 means that a term is not Boolean
 * - the index of the last signed symbol is returned in *index
 * - if the return code is 0, *index is n
 * - if the return code is negative, *index is between 0 and n-1 and 
 *   it's the index of the symbol that caused the error
 *
 * If the return code is 0, the assumptions are stored (as terms) in
 * a->assumptions, with duplicates removed.
 */
int32_t collect_assumptions_from_signed_symbols(assumptions_and_core_t *a, uint32_t n, const signed_symbol_t *s, uint32_t *index) {
  int32_t code;
  uint32_t i;
  term_t t;

  code = 0;
  for (i=0; i<n; i++) {
    t = get_term_by_name(a->terms, s[i].name);
    if (t == NULL_TERM) {
      code = -1;
      goto done;
    }
    if (! is_boolean_term(a->terms, t)) {
      code = -2;
      goto done;
    }
    t = signed_term(t, s[i].polarity);
    assumption_table_add(&a->table, t, s[i].name, s[i].polarity);
  }
  assumption_table_build_index(&a->table);
  collect_assumptions(&a->table, &a->assumptions);

 done:
  *index = i;
  return code;
}

