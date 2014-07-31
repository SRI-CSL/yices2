/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CONVERSION OF CONCRETE VALUES TO CONSTANT TERMS
 */

#ifndef __VAL_TO_TERM_H
#define __VAL_TO_TERM_H

#include <stdint.h>
#include <setjmp.h>

#include "utils/int_stack.h"
#include "utils/int_hash_map.h"
#include "terms/terms.h"
#include "model/concrete_values.h"


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
  term_table_t *terms;
  int_hmap_t cache;
  int_stack_t stack;
  jmp_buf env;
} val_converter_t;


/*
 * Initialization for vtbl + terms
 */
extern void init_val_converter(val_converter_t *convert, value_table_t *vtbl, term_table_t *terms);


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



#endif /* __VAL_TO_TERM_H */
