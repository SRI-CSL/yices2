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
 * CONVERSION OF CONSTANT TERMS TO CONCRETE VALUES
 */

#ifndef __TERM_TO_VAL_H
#define __TERM_TO_VAL_H

#include <stdint.h>
#include <setjmp.h>

#include "model/concrete_values.h"
#include "terms/terms.h"
#include "utils/int_hash_map.h"
#include "utils/int_stack.h"

/*
 * Error codes: -1 means null_value so we start with -2
 */
enum {
  TERM2VAL_INTERNAL_ERROR = -2,
  TERM2VAL_NOT_CONSTANT = -3,
};


/*
 * To do the conversion:
 * - terms = table of terms
 * - vtbl = table of concrete values
 * - cache = keeps mapping for terms already visited
 * - stack of integer arrays
 * - env = jump buffer for exceptions
 */
typedef struct term_converter_s {
  term_table_t *terms;
  value_table_t *vtbl;
  int_hmap_t cache;
  int_stack_t stack;
  jmp_buf env;
} term_converter_t;


/*
 * Initialize for terms + vtbl
 */
extern void init_term_converter(term_converter_t *convert, term_table_t *terms, value_table_t *vtbl);

/*
 * Reset: empty the cache
 */
extern void reset_term_converter(term_converter_t *convert);

/*
 * Free memory
 */
extern void delete_term_converter(term_converter_t *convert);

/*
 * Convert term t to a value
 * - t must be a valid term in convert->terms
 * - return an error if the conversion fails (including if t is not a constant)
 */
extern value_t convert_term_to_val(term_converter_t *convert, term_t t);


#endif /* __TERM_TO_VAL_H */
