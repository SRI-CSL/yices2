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
 * PRINT SMT-CORE STRUCTURE
 */

#ifndef __SMT_CORE_PRINTER_H
#define __SMT_CORE_PRINTER_H

#include <stdio.h>

#include "solvers/cdcl/smt_core.h"

/*
 * Basic objects
 */
extern void print_bval(FILE *f, bval_t b);
extern void print_status(FILE *f, smt_status_t s);
extern void print_bvar(FILE *f, bvar_t x);
extern void print_literal(FILE *f, literal_t l);


/*
 * Clauses
 */
extern void print_unit_clause(FILE *f, literal_t l);
extern void print_binary_clause(FILE *f, literal_t l1, literal_t l2);
extern void print_litarray(FILE *f, uint32_t n, literal_t *a);
extern void print_clause(FILE *f, clause_t *cl);

extern void print_unit_clauses(FILE *f, smt_core_t *core);
extern void print_binary_clauses(FILE *f, smt_core_t *core);
extern void print_problem_clauses(FILE *f, smt_core_t *core);
extern void print_learned_clauses(FILE *f, smt_core_t *core);
extern void print_clauses(FILE *f, smt_core_t *core);
extern void print_all_clauses(FILE *f, smt_core_t *core);
extern void print_lemmas(FILE *f, smt_core_t *core);

/*
 * Core solver state
 */
extern void print_boolean_assignment(FILE *f, smt_core_t *core);
extern void print_conflict(FILE *f, smt_core_t *core);
extern void print_smt_core(FILE *f, smt_core_t *core);


#endif /* __SMT_CORE_PRINTER_H */
