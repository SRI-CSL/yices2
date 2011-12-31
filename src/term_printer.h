/*
 * Print terms
 */

#ifndef __TERM_PRINTER_H
#define __TERM_PRINTER_H

#include <stdio.h>

#include "yices_pp.h"
#include "terms.h"
#include "bvlogic_buffers.h"


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
extern void print_arith_buffer(FILE *f, arith_buffer_t *b);
extern void print_bvarith_buffer(FILE *f, bvarith_buffer_t *b);
extern void print_bvarith64_buffer(FILE *f, bvarith64_buffer_t *b);
extern void print_bvlogic_buffer(FILE *f, bvlogic_buffer_t *b);

// list of monomials: for bvmlist and bvmlist64, n = number of bits
extern void print_mlist(FILE *f, mlist_t *p);
extern void print_bvmlist(FILE *f, bvmlist_t *p, uint32_t n);
extern void print_bvmlist64(FILE *f, bvmlist64_t *p, uint32_t n);


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
 * - name
 * - term (name or expression)
 */
extern void pp_term_exp(yices_pp_t *printer, term_table_t *tbl, term_t t);
extern void pp_term_name(yices_pp_t *printer, term_table_t *tbl, term_t  t);
extern void pp_term(yices_pp_t *printer, term_table_t *tbl, term_t t);

/*
 * Pretty print a term table
 */
extern void pp_term_table(FILE *f, term_table_t *tbl);


#endif
