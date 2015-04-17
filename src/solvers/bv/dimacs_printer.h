/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRINT LITERALS/BITVECTORS/CLAUSES IN THE DIMACS CNF FORMAT
 */

#ifndef __DIMACS_PRINTER_H
#define __DIMACS_PRINTER_H

#include <stdint.h>
#include <stdio.h>

#include "context/context_types.h"
#include "solvers/bv/bvsolver_types.h"
#include "solvers/bv/remap_table.h"
#include "solvers/cdcl/smt_core.h"


/*
 * Print boolean variable x in DIMACS format
 * - we can't use 0 as a variable id, so we print (x+1)
 */
extern void dimacs_print_bvar(FILE *f, bvar_t x);


/*
 * Print literal l in DIMACS format
 * - l is 2 * v + s with 0 <= v < nvars and s=0 or s=1
 * - 0 is not allowed as a variable in DIMACS so we
 *   convert variable v to DIMACS var (v+1)
 */
extern void dimacs_print_literal(FILE *f, literal_t l);


/*
 * Print clause c in DIMACS format:
 * - print all literals then add '0' + newline as end marker
 */
extern void dimacs_print_clause(FILE *f, clause_t *cl);


/*
 * Special cases
 */
extern void dimacs_print_empty_clause(FILE *f);
extern void dimacs_print_unit_clause(FILE *f, literal_t l);
extern void dimacs_print_binary_clause(FILE *f, literal_t l1, literal_t l2);


/*
 * Print all the problem clauses from core
 * First print the DIMACS header:
 *   p cnf <number of variables> <number of clauses>
 */
extern void dimacs_print_core(FILE *f, smt_core_t *core);


/*
 * Print all clauses: original + learned clauses
 * First print the DIMACS header
 */
extern void dimacs_print_full_core(FILE *f, smt_core_t *core);



/*
 * BITVECTORS
 */

/*
 * Print the literal mapped to s in the table
 * - if nothing is mapped to s, print "_"
 */
extern void dimacs_print_pseudo_literal(FILE *f, remap_table_t *table, literal_t s);

/*
 * Same thing for an array of n pseudo literals:
 * - use the format [ x0 ... x_{n-1} ] where x_0 = low order bit = a[0]
 *   and x_{n-1} = high order bit
 * - if one of a[i] is not mapped, it's replaced by "_"
 * - the literals are separated by spaces
 */
extern void dimacs_print_pseudo_litarray(FILE *f, remap_table_t *remap, literal_t *a, uint32_t n);


/*
 * Print the pseudo literal array mapped to bitvariable x
 * - x must be a valid variable
 * - it this is called before bit blasting, we print 'not mapped'
 *   otherwise we print the pseudo literal array mapped to x
 */
extern void dimacs_print_bvvar(FILE *f, bv_solver_t *solver, thvar_t x);



/*
 * TERMS AFTER INTERNALIZATION
 */

/*
 * Print what's mapped to t in the context's internalization table.
 * - if t is mapped to a Boolean, the corresponding DIMACS literal is printed
 * - if t is mapped to a bitvector then the corresponding literal array is printed
 * - otherwise we print "non boolean"
 */
extern void dimacs_print_internalized_term(FILE *f, context_t *ctx, term_t t);


/*
 * Print the mapping for t as a comment:
 * - this prints 'c term-name --> Dimacs value\n"
 */
extern void dimacs_print_term_map(FILE *f, context_t *ctx, term_t t);


/*
 * Same thing for an array of n terms a[0 ... n-1]
 * - print an empty comment line before and after
 */
extern void dimacs_print_term_map_array(FILE *f, context_t *ctx, term_t *a, uint32_t n);



/*
 * CONTEXT AFTER INTERNALIZATION AND BITBLASTING
 */

/*
 * Print the term map for every uninterpreted term present in ctx->intern_tbl
 * then print the core
 */
extern void dimacs_print_bvcontext(FILE *f, context_t *ctx);





#endif /* __DIMACS_PRINTER_H */
