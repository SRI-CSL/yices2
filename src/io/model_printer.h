/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * DISPLAY A MODEL
 */

/*
 * The code for displaying a model used to be in model.c
 * but it couldn't print the value of "x" if "x" is in the model's
 * alias table.
 *
 * This is a more general version: it can print the value assigned
 * to x if x is in the alias or map table. This requires the evaluator.
 */

#ifndef __MODEL_PRINTER_H
#define __MODEL_PRINTER_H

#include <stdio.h>
#include <stdbool.h>

#include "terms/terms.h"
#include "model/models.h"
#include "io/yices_pp.h"


/*
 * Print the assignment for t in model
 * - the format is (= t's name <value>)
 * - t must be an uninterpreted term
 * - if t has no value in the model (as defined by map_term), then
 *   the function prints some garbage (= t's name ???)
 * - if t doesn't have an explicit name, then a default name is used
 *   in the format "t!<decimal number>"
 */
extern void model_print_term_value(FILE *f, model_t *model, term_t t);


/*
 * Print the model
 * - one line per term, in the form (= term-name <value>)
 * - only the terms present in the model->map are displayed
 * - for functions, print the map
 *
 * Also print the map of all functions that occur in any <value>.
 *
 * Example:
 * - if term "x" is mapped to tuple of functions then we may
 * see something like:
 *   (= x (tuple fun!1 fun!2))
 *
 * Then we should also print the map of fun!1 and fun!2.
 */
extern void model_print(FILE *f, model_t *model);


/*
 * Print model, including the aliased terms
 * - one line per term as above
 * - if model->has_alias is true, then the value of all terms in
 *   the alias table is displayed
 * - if model->has_alias is false, then this is the same as model_print
 */
extern void model_print_full(FILE *f, model_t *model);


/*
 * Variants: use the pretty printer
 */
extern void model_pp_term_value(yices_pp_t *printer, model_t *model, term_t t);
extern void model_pp(yices_pp_t *printer, model_t *model);
extern void model_pp_full(yices_pp_t *printer, model_t *model);


#endif /* __MODEL_PRINTER_H */
