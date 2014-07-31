/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRETTY PRINTER FOR A MODEL USING THE SMT2 SYNTAX
 */

#ifndef __SMT2_MODEL_PRINTER_H
#define __SMT2_MODEL_PRINTER_H

#include "io/yices_pp.h"
#include "model/models.h"

/*
 * Print model:
 * - for every term in the models' internal map:
 *   print (= <term name> <value>)
 *   where value is in the SMT2 syntax
 * - if any <value> is an uninterpreted function
 *   or array, this is followed by the function
 *   definition.
 * This version ignores the alias map (if any).
 */
extern void smt2_pp_model(yices_pp_t *printer, model_t *model);


/*
 * Full model: same as above but also print the value
 * of terms that are stored in the mdodle's alias_map/
 */
extern void smt2_pp_full_model(yices_pp_t *printer, model_t *model);

#endif /* __SMT2_MODEL_PRINTER_H */
