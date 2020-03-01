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
 * PRETTY PRINTER FOR A MODEL USING THE SMT2 SYNTAX
 */

#ifndef __SMT2_MODEL_PRINTER_H
#define __SMT2_MODEL_PRINTER_H

#include "frontend/smt2/smt2_printer.h"
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
extern void smt2_pp_model(smt2_pp_t *printer, model_t *model);

/*
 * Full model: same as above but also print the value
 * of terms that are stored in the model's alias_map.
 */
extern void smt2_pp_full_model(smt2_pp_t *printer, model_t *model);


#endif /* __SMT2_MODEL_PRINTER_H */
