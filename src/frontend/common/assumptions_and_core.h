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

#ifndef __ASSUMPTIONS_AND_CORE_H
#define __ASSUMPTIONS_AND_CORE_H

#include "frontend/common/assumption_table.h"
#include "frontend/common/named_term_stacks.h"
#include "parser_utils/term_stack2.h"
#include "solvers/cdcl/smt_core.h"
#include "terms/terms.h"
#include "utils/int_vectors.h"

/*
 * Data structure to deal with assumptions:
 * - terms = relevant term_table
 * - table: store assumptions + names
 * - assumptions: vector of assumed terms
 * - core: unsat core
 * - status: as returned by check_assuming
 */
typedef struct assumptions_and_core_s {
  term_table_t *terms;
  assumption_table_t table;
  ivector_t assumptions;
  ivector_t core;
  smt_status_t status;
} assumptions_and_core_t;


/*
 * Allocate a fresh structure:
 * - status is set to IDLE
 */
extern assumptions_and_core_t *new_assumptions(term_table_t *terms);

/*
 * Free the data structures
 */
extern void free_assumptions(assumptions_and_core_t *a);


/*
 * Collect all the named terms of stack as assumptions
 * - all terms in stack must be Boolean
 * - this stores all the assumptions in a->assumptions and remove duplicates if any
 */
extern void collect_assumptions_from_stack(assumptions_and_core_t *a, const named_term_stack_t *stack);

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
extern int32_t collect_assumptions_from_signed_symbols(assumptions_and_core_t *a, uint32_t n, const signed_symbol_t *s, uint32_t *index);


#endif /* __ASSUMPTIONS_AND_CORE_H */
