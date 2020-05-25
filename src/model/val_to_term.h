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
 * CONVERSION OF CONCRETE VALUES TO CONSTANT TERMS
 */

#ifndef __VAL_TO_TERM_H
#define __VAL_TO_TERM_H

#include <stdint.h>
#include <setjmp.h>

#include "model/concrete_values.h"
#include "terms/term_manager.h"
#include "terms/terms.h"
#include "utils/int_hash_map.h"
#include "utils/int_stack.h"


/*
 * Error codes: all are negative
 * - NULL_TERM is -1, so we start with -2
 */
enum {
  CONVERT_INTERNAL_ERROR = -2,
  CONVERT_UNKNOWN_VALUE = -3,
  CONVERT_NOT_PRIMITIVE = -4,
  CONVERT_FUNCTION = -5,
  CONVERT_FAILED = -6,
};


/*
 * To do the conversion:
 * - vtbl = table of concrete values
 * - terms = table of terms
 * + auxiliary structures:
 * - cache = keeps mapping of values already visited
 * - stack of integer arrays
 * - env = jump buffer for exceptions
 */
typedef struct val_converter_s {
  value_table_t *vtbl;
  term_manager_t *manager;
  term_table_t *terms;
  int_hmap_t cache;
  int_stack_t stack;
  jmp_buf env;
} val_converter_t;


/*
 * Initialization for vtbl + terms
 */
extern void init_val_converter(val_converter_t *convert, value_table_t *vtbl, term_manager_t *mgr, term_table_t *terms);


/*
 * Reset: empty the cache
 */
extern void reset_val_converter(val_converter_t *convert);


/*
 * Free memory
 */
extern void delete_val_converter(val_converter_t *convert);


/*
 * Convert v to a constant term
 * - return an error (<0) if the conversion fails
 */
extern term_t convert_value(val_converter_t *convert, value_t v);


/*
 * Quick conversion: try to convert v to a constant term
 * - return an error code < 0 if the conversion fails
 * - return CONVERT_NOT_PRIMITIVE if v is a tuple (not primitive but
 *   could be converted using the previous function).
 *
 * Primitive values are: Booleans, arithmetic and bitvector constants,
 * + constants of scalar and uninterpreted types.
 */
extern term_t convert_simple_value(term_table_t *terms, value_table_t *vtbl, value_t v);


/*
 * Convert v to a constant term
 * - this tries convert_simple_value first then use a val_converter if needed.
 * - return a negative code if there's an error (same codes as convert_value)
 */
extern term_t convert_value_to_term(term_manager_t *mgr, term_table_t *terms, value_table_t *vtbl, value_t v);


/*
 * In-place conversion of values b[0 ... n-1] to constant terms
 * - on entry: every b[i] must be a value index in vtbl
 *   on exit: b[i] is a constant term in terms, or a negative error code
 *            if the conversion failed for b[i].
 *
 * - returns the number of values that could be successfully converted to terms
 *   (this is an integer between 0 and n).
 */
extern uint32_t convert_value_array(term_manager_t *mgr, term_table_t *terms, value_table_t *vtbl, uint32_t n, int32_t *b);


/*
 * Recursive conversion of primitive and tuple terms
 * - raise an exception via longjmp if the conversion fails.
 */
extern term_t convert_val(val_converter_t *convert, value_t v);

#endif /* __VAL_TO_TERM_H */
