/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Print terms
 */

#ifndef __TERM_PRINTER_H
#define __TERM_PRINTER_H

#include <stdio.h>

#include "io/yices_pp.h"
#include "terms/bvlogic_buffers.h"
#include "terms/terms.h"


/*
 * Term id
 */
extern void print_term_id(FILE *f, term_t t);


/*
 * Polynomials and buffers
 */
extern void print_pprod(FILE *f, pprod_t *r);
extern void print_polynomial(FILE *f, polynomial_t *p);
extern void print_bvpoly(FILE *f, bvpoly_t *p);
extern void print_bvpoly64(FILE *f, bvpoly64_t *p);
extern void print_arith_buffer(FILE *f, rba_buffer_t *b);
extern void print_bvarith_buffer(FILE *f, bvarith_buffer_t *b);
extern void print_bvarith64_buffer(FILE *f, bvarith64_buffer_t *b);
extern void print_bvlogic_buffer(FILE *f, bvlogic_buffer_t *b);


/*
 * Print functions:
 * 1) print_term_name: print the name of t. If t has no name,
 *    then something like 't!12903' is printed.
 *
 * 2) print term_def: print t's name and its definition in
 *    the format  'name := expression'.
 *    If t is a composite term, then t's subterms are not
 *    recursively expanded (to avoid blowing up).
 *
 * 3) print_term_exp: print t's definition as 'expression'
 *    As above, t's subterms are not recursively expanded.
 *
 * 4) print_term: if t has a name then the name is printed,
 *    otherwise, t's definition is printed (not recursively
 *    expanded either)
 *
 * 5) print_term_full: print t's definition, with full recursive
 *    printing of t's subterms. So this can blow up.
 */
extern void print_term_name(FILE *f, term_table_t *tbl, term_t t);
extern void print_term_def(FILE *f, term_table_t *tbl, term_t t);
extern void print_term_exp(FILE *f, term_table_t *tbl, term_t t);
extern void print_term(FILE *f, term_table_t *tbl, term_t t);
extern void print_term_full(FILE *f, term_table_t *tbl, term_t t);


/*
 * Print t's descriptor
 */
extern void print_term_desc(FILE *f, term_table_t *tbl, term_t t);


/*
 * Print all terms in tbl
 */
extern void print_term_table(FILE *f, term_table_t *tbl);


/*
 * Pretty printing:
 * - term expression
 * - fully expanded terms
 * - name
 * - term (name or expression)
 */
extern void pp_term_exp(yices_pp_t *printer, term_table_t *tbl, term_t t);
extern void pp_term_name(yices_pp_t *printer, term_table_t *tbl, term_t  t);
extern void pp_term(yices_pp_t *printer, term_table_t *tbl, term_t t);
extern void pp_term_full(yices_pp_t *printer, term_table_t *tbl, term_t t);


/*
 * Pretty print a term table
 */
extern void pp_term_table(FILE *f, term_table_t *tbl);


/*
 * Direct pretty_printing (without a yices_pp_t object)
 * - f = output file
 * - area = pretty printing area (cf. pretty_printer.h)
 * - if area is NULL, a default area is used:
 *   - default width = 120 characters
 *   - default height = infinite (UINT32_MAX)
 *   - default offset = 0
 *   - stretch  = false
 *   - truncate = false
 */
extern void pretty_print_term_exp(FILE *f, pp_area_t *area, term_table_t *tbl, term_t t);
extern void pretty_print_term_full(FILE *f, pp_area_t *area, term_table_t *tbl, term_t t);

#endif
