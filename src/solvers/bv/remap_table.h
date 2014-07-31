/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/******************************
 *  LITERAL RE-MAPPING TABLE  *
 *****************************/

#ifndef __REMAP_TABLE_H
#define __REMAP_TABLE_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "utils/bitvectors.h"
#include "utils/refcount_int_arrays.h"
#include "solvers/cdcl/smt_core.h"


/*
 * The first step in bit-blasting is to assign literals
 * to the bit-vector variables. We want to avoid creating
 * redundant literals, i.e., create l1 and l2 then later
 * assert that l1 and l2 are equal.
 *
 * For this purpose, we use a level of indirection. We map bit-vector
 * variables to (arrays of) pseudo-literals then map pseudo-literals
 * to literals in the bit-solver as needed.  Pseudo literals are
 * integer labels with a polarity bits, just like normal literals, but
 * nothing is created in the bitsolver for a pseudo literal. The role
 * of the pseudo literals is to record when two bits are equal before
 * they are turned into literals.
 *
 * Example:
 * - u is a bitvector variable of size 32 (BVTAG_VAR)
 * - b0 is (bvselect u 0)
 * - b1 is (bvselect u 1)
 * - b2 is (bvselect u 2)
 * - v is [BIT_ARRAY b1 b2]: extract two bits out of u
 * - w is [BIT_ARRAY b0 b0]
 * - t is [BIT_ARRAY ~b1 ~b1 true]
 * - v and w are asserted equal.
 * Then we can deduce from this that b0 = b1 = b2.
 * So we need just one pseudo literal x for v, w, and t:
 *   b0 --> x
 *   b1 --> x
 *   b2 --> x
 *   v --> [x x]
 *   w --> [x x]
 *   t --> [~x ~x tt]
 *
 * To deal with equality constraints like (v == w) we substitute
 * pseudo literals of w with pseudo literals of v. The remapping
 * table stores the mapping from pseudo-literals to real literals
 * and the substitution.
 *
 * Table components:
 * - nvars = number of pseudo variables
 *   for each v in 0, .., nvars-1, there are two pseudo literals,
 *   namely, pos_lit(v) and neg_lit(w).
 * - merge_bit[v] = mark to distinguish substituted/root variables
 * - map[v] = mapping for v:
 *   initially, merge_bit[v] = 0, map[v] = null_literal
 *   after a substitution v := l,  we set merge_bit[v] = 1, map[v] = l
 *   after bit blasting v is assigned a literal l0, then we set
 *   map[v] = l0.
 *
 * We enforce remap[0] = true_literal. If l is the pseudo true_literal or
 * false_literal, then the corresponding real literal is equal to l.
 *
 *
 * Support for push/pop:
 * - when variable v is remapped either to a pseudo literal l or to
 *   a real literal l0, then we push s onto the undo stack
 * - for each level: we keep track of nvars and top of the undo stack
 */

/*
 * Undo stack:
 * - element in the stack are variables
 * - top = top of the stack
 * - size = full size of array data
 */
typedef struct remap_undo_stack_s {
  uint32_t size;
  uint32_t top;
  int32_t *data;
} remap_undo_stack_t;

#define DEF_REMAP_UNDO_SIZE 100
#define MAX_REMAP_UNDO_SIZE (UINT32_MAX/sizeof(int32_t))


/*
 * Trail stack:
 * - for each level, we keep track of the top of the undo_stack
 *   and the size of the remap (i.e., last variables
 *   that was mapped to anything) on entry to that level.
 */
typedef struct remap_trail_elem_s {
  uint32_t undo_top;
  uint32_t map_top;
} remap_trail_elem_t;

typedef struct remap_trail_s {
  uint32_t size;
  uint32_t top;
  remap_trail_elem_t *data;
} remap_trail_t;

#define DEF_REMAP_TRAIL_SIZE 30
#define MAX_REMAP_TRAIL_SIZE (UINT32_MAX/sizeof(remap_trail_elem_t))


/*
 * Remap table:
 * - the current map is defined by map[0 ... nvars - 1]
 *   and by merge_bit[0 ... nvars - 1]
 * - for any variable x, we have
 *   remap[x] = map[x]        if 0 <= x < nvars
 *   remap[x] = null_literal  otherwise
 * - if 0 <= x < nvars and merge_bit[x] is 1 then map[x] is a pseudo literal
 *   otherwise map[x] is a real literal in the core.
 * - prev_top = value of nvars before the preceding push (or 0 initially)
 *   when we write something in map[x] then x must be saved only if
 *   0 <= x < prevtop
 * - size = full size of the remap and merge_bit arrays
 */
typedef struct remap_table_s {
  literal_t *map;
  byte_t *merge_bit;
  uint32_t nvars;
  uint32_t prev_top;
  uint32_t size;
  remap_undo_stack_t undo;
  remap_trail_t trail;
} remap_table_t;

#define DEF_REMAP_TABLE_SIZE 100
#define MAX_REMAP_TABLE_SIZE (UINT32_MAX/sizeof(literal_t))




/****************
 *  OPERATIONS  *
 ***************/

/*
 * Initialization: create a table of default size
 * - var 0 is mapped to true_literal
 */
extern void init_remap_table(remap_table_t *table);


/*
 * Delete table
 */
extern void delete_remap_table(remap_table_t *table);


/*
 * Reset the table (empty)
 */
extern void reset_remap_table(remap_table_t *table);


/*
 * Start a new level
 */
extern void remap_table_push(remap_table_t *table);


/*
 * Backtrack to the previous level
 * (the trail stack must be non-empty)
 */
extern void remap_table_pop(remap_table_t *table);


/*
 * Set level n: equivalent to calling push n times
 * - this can be used to set the initial level after
 *   the table is created.
 */
extern void remap_table_set_level(remap_table_t *table, uint32_t n);



/*
 * PSEUDO-LITERAL ALLOCATION
 */

/*
 * Create a fresh pseudo literal l = pos_lit(v) where v is a fresh
 * variable.
 * - map[v] is null_literal, merge_bit[v] is 0
 */
extern literal_t remap_table_fresh_lit(remap_table_t *table);

/*
 * Allocate and initialize an array of n fresh pseudo literals.
 * - all literals in the array are initialized as in fresh_lit above.
 * - the array is allocated using refcount_int_array
 */
extern literal_t *remap_table_fresh_array(remap_table_t *table, uint32_t n);


/*
 * Decrement the reference counter (a must be allocated with the previous
 * function or with refcount_int_array).
 */
static inline void remap_table_free_array(literal_t *a) {
  int_array_decref(a);
}



/*
 * MERGING/SUBSTITUTIONS
 */

/*
 * - the pseudo-literals can be organized into equivalence classes
 * - this is done by the merge operation below
 * - each equivalence class has a representative (its root).
 */

/*
 * Find the root of pseudo literal l
 * - l must be in the table (and non-null)
 */
extern literal_t remap_table_find_root(remap_table_t *table, literal_t l);

/*
 * Check whether l is a root pseudo literal
 */
static inline bool remap_table_is_root(remap_table_t *table, literal_t l) {
  assert(0 <= var_of(l) && var_of(l) < table->nvars);
  return !tst_bit(table->merge_bit, var_of(l));
}

/*
 * Check whether l1 and l2 can be merged
 * - l1 and l2 must be roots
 * - return true if l1 is different from l2 and not(l2) and if
 *   l1 or l2 has no assignment.
 */
extern bool remap_table_mergeable(remap_table_t *table, literal_t l1, literal_t l2);


/*
 * Merge l1 and l2:
 * - both must be roots and l1 must be different from l2 and not(l2)
 * - if remap[l1] != null_literal, we use l2 := l1
 * - otherwise, we map l1 to l2
 */
extern void remap_table_merge(remap_table_t *table, literal_t l1, literal_t l2);




/*
 * LITERAL ASSIGNMENT
 */

/*
 * - the table stores a mapping from pseudo literals to real literals
 * - all pseudo literals in the same class are mapped to the same literal
 * - the class of 'true_literal' is always mapped to true_literal
 * - all other classes are mapped to null_literal by default
 * - this assignment is changed by calling the assign function below
 */

/*
 * Assign l1 to the class of l
 * - l1 must be a non-null 'real' literal
 * - the class must not be assigned to anything yet
 * - this assigns map[root(l)] := l1
 */
extern void remap_table_assign(remap_table_t *table, literal_t l, literal_t l1);

/*
 * Auxiliary function used below:
 * - flip the polarity bit of l if sgn is 1 and l is non-null
 * - keep l unchanged otherwise
 */
static inline literal_t xor_sign(literal_t l, uint32_t sgn) {
  return (l == null_literal) ? l : (l ^ sgn);
}

/*
 * Return the literal assigned to the class of l
 * return null_literal if no literal is assigned to the class
 */
static inline literal_t remap_table_find(remap_table_t *table, literal_t l) {
  l = remap_table_find_root(table, l);
  return xor_sign(table->map[var_of(l)], sign_of_lit(l));
}




#endif /* __REMAP_TABLE_H */
