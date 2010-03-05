/*
 * Print terms and types and other internal objects
 */

#ifndef __TERM_PRINTER_H
#define __TERM_PRINTER_H

#include <stdio.h>
#include "terms.h"
#include "eq_abstraction.h"


// name
extern void print_arith_var(FILE *f, arith_var_t v);
extern void print_bv_var(FILE *f, bv_var_t v);
extern void print_term_id(FILE *f, term_t t);
extern void print_type_id(FILE *f, type_t tau);

// bitvector and arithmetic objects
extern void print_arith_varprod(FILE *f, varprod_t *p);
extern void print_bv_varprod(FILE *f, varprod_t *p);
extern void print_polynomial(FILE *f, polynomial_t *p);
extern void print_monarray(FILE *f, monomial_t *p);
extern void print_arith_buffer(FILE *f, arith_buffer_t *b);
extern void print_bvarith_expr(FILE *f, bvarith_expr_t *e);
extern void print_bvarith_buffer(FILE *f, bvarith_buffer_t *b);
extern void print_bvlogic_expr(FILE *f, bvlogic_expr_t *e);
extern void print_bvlogic_buffer(FILE *f, bvlogic_buffer_t *b);

// warning; this can explode (recursively prints subterms)
extern void print_type(FILE *f, type_t tau);
extern void print_typedef(FILE *f, type_t tau);
extern void print_fulltype(FILE *f, type_t tau);

extern void print_term(FILE *f, term_t t);
extern void print_termdef(FILE *f, term_t t);
extern void print_fullterm(FILE *f, term_t t);

extern void print_bit_expr(FILE *f, bit_t b);
extern void print_vars_of_bit_expr(FILE *f, bit_t b);

// non-recursive print
extern void print_term_shallow(FILE *f, term_t t);


// print names of term or type 
extern void print_term_name(FILE *f, term_t t);
extern void print_type_name(FILE *f, type_t tau);

// details about individual objects
extern void print_type_data(FILE *f, type_t tau);
extern void print_term_data(FILE *f, term_t t);
extern void print_bv_var_data(FILE *f, bv_var_t v);
extern void print_arith_var_data(FILE *f, arith_var_t v);

// partitions in eq_abstraction
extern void print_epartition(FILE *f, epartition_t *p);

// print all
extern void print_all_types(FILE *f);
extern void print_all_terms(FILE *f);
extern void print_all_bv_vars(FILE *f);
extern void print_all_arith_vars(FILE *f);


// bit vector components
extern void print_all_root_bit_exprs(FILE *f);

#endif
