/*
 * Print terms
 */

#ifndef __TERM_PRINTER_H
#define __TERM_PRINTER_H

#include <stdio.h>

#include "terms.h"

/*
 * Term id:
 */
extern void print_term_id(FILE *f, term_t t);


/*
 * Polynomials and buffers
 */
extern void print_pprod(FILE *f, pprod_t *r);
extern void print_polynomial(FILE *f, polynomial_t *p);
extern void print_bvpoly(FILE *f, bvpoly_t *p);
extern void print_bvpoly64(FILE *f, bvpoly64_t *p);
extern void print_arith_buffer(FILE *f, arith_buffer_t *b);
extern void print_bvarith_buffer(FILE *f, bvarith_buffer_t *b);
extern void print_bvarith64_buffer(FILE *f, bvarith64_buffer_t *b);


/*
 * Print
 * - term expression
 * - only the name
 * - term definition as 'name := expression'
 * - print term: print t's name or the expression if t has no name
 */
extern void print_term_exp(FILE *f, term_table_t *tbl, term_t t);
extern void print_term_name(FILE *f, term_table_t *tbl, term_t t);
extern void print_term_def(FILE *f, term_table_t *tbl, term_t t);

extern void print_term(FILE *f, term_table_t *tbl, term_t t);


/*
 * Print all terms in tbl
 */
extern void print_term_table(FILE *f, term_table_t *tbl);


#endif
