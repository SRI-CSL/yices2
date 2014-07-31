/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
