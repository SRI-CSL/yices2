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

#include "terms.h"
#include "models.h"
#include "yices_pp.h"


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
 * If high_order is true, also print the map of all functions that occur 
 * as argument of a <value> printed before.
 *
 * Example:
 * - if term "x" is mapped to tuple of functions then we may 
 * see something like:
 *   (= x (tuple fun!1 fun!2))
 *
 * Then we should also print the map of fun!1 and fun!2.
 */
extern void model_print(FILE *f, model_t *model, bool high_order);


/*
 * Print model, including the aliased terms
 * - one line per term as above
 * - if model->has_alias is true, then the value of all terms in
 *   the alias table is displayed
 * - if model->has_alias is false, then this is the same as model_print
 *
 * high_order flag: as above
 */
extern void model_print_full(FILE *f, model_t *model, bool high_order);


/*
 * Variants: use the pretty printer
 */
extern void model_pp_term_value(yices_pp_t *printer, model_t *model, term_t t);
extern void model_pp(yices_pp_t *printer, model_t *model, bool high_order);
extern void model_pp_full(yices_pp_t *printer, model_t *model, bool high_order);


#endif /* __MODEL_PRINTER_H */
