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

#include "io/yices_pp.h"
#include "model/models.h"
#include "terms/terms.h"


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
extern void model_print(FILE *f, model_t *model, pp_lang_t lang);

/*
 * Print model, including the aliased terms
 * - one line per term as above
 * - if model->has_alias is true, then the value of all terms in
 *   the alias table is displayed
 * - if model->has_alias is false, then this is the same as model_print
 */
extern void model_print_full(FILE *f, model_t *model, pp_lang_t lang);

/*
 * Print the values of all terms in array a
 * - n = number of terms in a
 * - this first prints the value of these terms in the form
 *    (= <term name> <value>)
 * - this uses a simple lookup to find the value of a[i] in the model's internal map.
 *   So every term a[i] should be defined in the model.
 * - then the function prints the value of all function terms that occur
 *   in a value (cf., model_print).
 */
extern void model_print_terms(FILE *f, model_t *model, const term_t *a, uint32_t n, pp_lang_t lang);

/*
 * Evaluate and print the values of all terms in array a
 * - n = number of terms in a
 * - This first prints the values of these terms in the form
 *     (= <term name> <value>)
 *   where <term name> = name of a[i].
 *   If a[i] doesn't have a name, we print a name like "t!xxx" where xxx is an integer (it's equal to a[i]).
 * _ Then we print the function terms that occur in any <value>.
 *
 * - This is the more general than model_print_terms, since it can handle more than
 *   uninterpreted terms.
 */
extern void model_print_eval_terms(FILE *f, model_t *model, const term_t *a, uint32_t n, pp_lang_t lang);

/*
 * Variants: use a pretty printer
 */
extern void model_pp_term_value(yices_pp_t *printer, model_t *model, term_t t);
extern void model_pp(yices_pp_t *printer, model_t *model);
extern void model_pp_full(yices_pp_t *printer, model_t *model);
extern void model_pp_terms(yices_pp_t *printer, model_t *model, const term_t *a, uint32_t n);
extern void model_pp_eval_terms(yices_pp_t *printer, model_t *model, const term_t *a, uint32_t n);

#endif /* __MODEL_PRINTER_H */
