/*
 * PRINT CONTEXT
 */

#ifndef __CONTEXT_PRINTER_H
#define __CONTEXT_PRINTER_H

#include <stdio.h>

#include "context.h"


/*
 * Internal structures used in flattening/simplifications/internalization
 */
extern void print_context_subst_eqs(FILE *f, context_t *ctx);
extern void print_context_top_eqs(FILE *f, context_t *ctx);
extern void print_context_top_atoms(FILE *f, context_t *ctx);
extern void print_context_top_formulas(FILE *f, context_t *ctx);
extern void print_context_top_interns(FILE *f, context_t *ctx);

// substitution and internalization mapping
// stored in the internalization table
extern void print_context_intern_subst(FILE *f, context_t *ctx);
extern void print_context_intern_mapping(FILE *f, context_t *ctx);


/*
 * Pretty printing: display the result of flattening + variable elimination
 */
extern void pp_context(FILE *f, context_t *ctx);


#endif /* __CONTEXT_PRINTER_H */
