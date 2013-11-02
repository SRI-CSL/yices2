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


#endif /* __CONCRETE_VALUE_MAKER */
