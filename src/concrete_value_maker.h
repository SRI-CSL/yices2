/*
 * BUILD VALUES OF GIVEN TYPES
 */

#ifndef __CONCRETE_VALUE_MAKER_H
#define __CONCRETE_VALUE_MAKER_H

#include <stdbool.h>

#include "concrete_values.h"


/*
 * Return a value of type tau built in vtbl
 * - tau must be a ground type
 */
extern value_t vtbl_make_object(value_table_t *vtbl, type_t tau);

/*
 * Attempt to construct to distinct values of type tau in vtbl.
 * - if that succeeds, store the two values in a[0] and a[1] and return true
 * - return false otherwise (i.e., when tau is a singleton type).
 * - tau must be a ground type
 */
extern bool vtbl_make_two_objects(value_table_t *vtbl, type_t tau, value_t a[2]);

/*
 * Return a fresh rational value:
 * - this value is different from any other rational already present
 *   in vtbl
 */
extern value_t vtbl_make_fresh_rational(value_table_t *vtbl);

/*
 * Return a fresh integer value:
 * - this value is different from any other rational already present
 *   in vtbl
 */
extern value_t vtbl_make_fresh_integer(value_table_t *vtbl);

/*
 * Attempt to build a fresh bitvector value of n bits
 * - if all 2^n values are present in vtbl, return null_value
 * - otherwise, create a bitvector value distinct from all other values
 *   of the same type and return it.
 */
extern value_t vtbl_make_fresh_bv(value_table_t *vtbl, uint32_t n);

/*
 * Fresh constant of uninterpreted or scalar type
 * - tau must be an uninterpreted or scalar type
 * - return null_value if tau is a scalar type and all constants of that
 *   type already occur in vtbl.
 */
extern value_t vtbl_make_fresh_const(value_table_t *table, type_t tau);


/*
 * Create a fresh value of type tau:
 * - return null_value if that fails (i.e., tau is finite and all values
 *   or type tau are already present)
 */
extern value_t vtbl_make_fresh_value(value_table_t *vtbl, type_t tau);


#endif /* __CONCRETE_VALUE_MAKER */
