/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * DESCRIPTORS OF CONCRETE VALUES
 */

/*
 * In the API, we export model values using the yval_t data
 * structure. This structure stores a node_id = same as a value_t
 * in a concrete_value table + a tag that defines the node type.
 *
 * The types yval_tag_t, yval_t, and yval_vector_t are defined in
 * yices_types.h.
 */

#ifndef __YVAL_H
#define __YVAL_H

#include "model/concrete_values.h"
#include "yices_types.h"

/*
 * Vectors of descriptors
 */
#define DEF_YVAL_VECTOR_SIZE 20
#define MAX_YVAL_VECTOR_SIZE (UINT32_MAX/sizeof(yval_t))
#define YVAL_VECTOR_REDUCE_THRESHOLD 16384

extern void init_yval_vector(yval_vector_t *v);
extern void yval_vector_push(yval_vector_t *v, int32_t id, yval_tag_t tag);
extern void reset_yval_vector(yval_vector_t *v);
extern void delete_yval_vector(yval_vector_t *v);


/*
 * Convert a concrete value type to a yval_tag_t
 */
extern yval_tag_t tag_for_valkind(value_kind_t kind);

/*
 * Build a yval_t descriptor for value v defined in tbl
 * - v must be a valid index in tbl
 */
extern void get_yval(value_table_t *tbl, value_t v, yval_t *d);

/*
 * Expand a tuple v:
 * - a must be an array large enough to store n values where n = arity of v
 */
extern void yval_expand_tuple(value_table_t *tbl, value_t v, yval_t *a);

/*
 * Expand a mapping m:
 * - a must be an array large enough to store n values where n = arity of m
 * - the domain of m is stored in a[0 ... n-1] and the value is stored in *v
 * (i.e., m is of the form [a_0 ... a_n-1 -> v])
 */
extern void yval_expand_mapping(value_table_t *tbl, value_t m, yval_t *a, yval_t *v);

/*
 * Expand a function object f
 * - the default value is stored in *def
 * - the mappings defining f are stored in vector v (no duplicates)
 */
extern void yval_expand_function(value_table_t *tbl, value_t f, yval_vector_t *v, yval_t *def);

/*
 * Expand an update object f
 * - the default value is stored in *def
 * - the mappings defining f are stored in vector v (no duplicates)
 */
extern void yval_expand_update(value_table_t *tbl, value_t f, yval_vector_t *v, yval_t *def);


#endif /* __YVAL_H */
