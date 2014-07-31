/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BUILD FRESH VALUES OF GIVEN TYPES
 */

#ifndef __FRESH_VALUE_MAKER_H
#define __FRESH_VALUE_MAKER_H

#include <stdint.h>
#include <stdbool.h>

#include "model/concrete_values.h"


/*
 * Data structure to keep track of the number of elements of a finite
 * type tau[0] x ... x tau[n-1]
 * - arity = n
 * - card = cardinal of the product type
 * - count = enumeration index: it's known that all tuples of index
 *   in [0 ... count-1] exist in the value table
 * - tau[0 ... n-1] = actual type indices
 *
 * We also use this for scalar types (then arity = 1)
 */
typedef struct tuple_counter_s {
  uint32_t arity;
  uint32_t card;
  uint32_t count;
  type_t tau[0]; // real size = arity
} tuple_counter_t;

#define MAX_TUPLE_COUNTER_ARITY ((UINT32_MAX-sizeof(tuple_counter_t))/sizeof(type_t))


/*
 * Vector of these counters
 */
typedef struct tup_counter_vector_s {
  tuple_counter_t **data;
  uint32_t nelems;
  uint32_t size; // size of the array data
} tup_counter_vector_t;

#define TUPLE_COUNTER_VECTOR_DEF_SIZE 8
#define TUPLE_COUNTER_VECTOR_MAX_SIZE (UINT32_MAX/sizeof(tuple_counter_t *))


/*
 * Counters for bitvector constants
 * - bsize = number of bits
 * - count = enumeration index
 * - every constant of bsize bits and value < count are known
 *   to be present in vtbl.
 */
typedef struct bv_counter_s {
  uint32_t bsize;
  uint32_t count;
} bv_counter_t;


/*
 * Vector of these counters
 */
typedef struct bv_counter_vector_s {
  bv_counter_t *data;
  uint32_t nelems;
  uint32_t size;
} bv_counter_vector_t;

#define BV_COUNTER_VECTOR_DEF_SIZE 8
#define BV_COUNTER_VECTOR_MAX_SIZE (UINT32_MAX/sizeof(bv_counter_vector_t))


/*
 * Fresh-value maker:
 * - attached to a value_table vtbl and a type_table types
 * - keep vectors for the counter structures:
 *   - one for tuple  (also used for scalar types)
 *   - one for bitvectors
 * - global counter for the integer constants
 * + auxiliary buffer for building bitvector constants
 *
 * NOTE: we assume that the number of records is small
 */
typedef struct fresh_val_maker_s {
  value_table_t *vtbl;
  type_table_t *types;
  tup_counter_vector_t tuples;
  bv_counter_vector_t bvs;
  bvconstant_t aux;
  int32_t int_count;
} fresh_val_maker_t;


/*
 * Initialize: nothing allocated yet
 */
extern void init_fresh_val_maker(fresh_val_maker_t *maker, value_table_t *vtbl);

/*
 * Delete: free all records
 */
extern void delete_fresh_val_maker(fresh_val_maker_t *maker);




/*
 * Return a fresh integer:
 * - this value is different from any other integer already present
 */
extern value_t make_fresh_integer(fresh_val_maker_t *maker);

static inline value_t make_fresh_rational(fresh_val_maker_t *maker) {
  return make_fresh_integer(maker);
}

/*
 * Attempt to build a fresh bitvector value of n bits
 * - if all 2^n values are present in vtbl, return null_value
 * - otherwise, create a bitvector value distinct from all other values
 *   of the same type and return it.
 */
extern value_t make_fresh_bv(fresh_val_maker_t *maker, uint32_t n);

/*
 * Fresh constant of uninterpreted or scalar type
 * - tau must be an uninterpreted or scalar type
 * - return null_value if tau is a scalar type and all constants of that
 *   type already occur in vtbl.
 */
extern value_t make_fresh_const(fresh_val_maker_t *maker, type_t tau);

/*
 * Fresh tuple of type tau
 * - tau must be a tuple type
 * - return null_value if tau is finite and all tuples of that type
 *   already exist
 */
extern value_t make_fresh_tuple(fresh_val_maker_t *maker, type_t tau);

/*
 * Fresh function to type tau
 * - tau must be a function type
 * - return null_value if tau is finite and all functions of that type
 *   already exist
 */
extern value_t make_fresh_function(fresh_val_maker_t *maker, type_t tau);

/*
 * Create a fresh value of type tau:
 * - return null_value if that fails (i.e., tau is finite and all values
 *   or type tau are already present)
 */
extern value_t make_fresh_value(fresh_val_maker_t *maker, type_t tau);


#endif /* __FRESH_VALUE_MAKER */
