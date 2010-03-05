/******************************
 *  LITERAL RE-MAPPING TABLE  *
 *****************************/

#ifndef __REMAP_TABLE_H
#define __REMAP_TABLE_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "bitvectors.h"
#include "memalloc.h"
#include "smt_core.h"


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
 * - merge_bit[v] = mark to distinguish subsituted/root variables
 * - remap[v] = mapping for v:
 *   initially, merge_bit[v] = 0, remap[v] = null_literal
 *   after a substitution v := l,  we set merge_bit[v] = 1, remap[v] = l
 *   after bit blasting v is assigned a literal l0, then we set
 *   remap[v] = l0.
 *
 * We enforce remap[0] = true_literal. If l is the pseudo true_literal or
 * false_literal, then the corresponding real literal is equal to l.
 */
typedef struct remap_table_s {
  uint32_t nvars;
  uint32_t size;
  literal_t *remap;
  byte_t *merge_bit;  
} remap_table_t;

#define DEF_REMAP_TABLE_SIZE 100
#define MAX_REMAP_TABLE_SIZE (UINT32_MAX/sizeof(literal_t))



/****************
 *  OPERATIONS  *
 ***************/

/*
 * Initialization: create a table of default size
 * - create var 0 mapped to true_literal
 */
extern void init_remap_table(remap_table_t *table);


/*
 * Delete table
 */
extern void delete_remap_table(remap_table_t *table);


/*
 * Create a fresh pseudo literal
 */
extern literal_t remap_table_fresh_lit(remap_table_t *table);


/*
 * Allocate and initialize an array of n fresh pseudo literals.
 */
extern literal_t *remap_table_fresh_array(remap_table_t *table, uint32_t n);


/*
 * Delete array a created by the previous function
 */
static inline void remap_table_free_array(literal_t *a) {
  safe_free(a);
}



/*
 * MERGING
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
 */
static inline void remap_table_assign(remap_table_t *table, literal_t l, literal_t l1) {
  assert(l1 != null_literal);
  l = remap_table_find_root(table, l);
  assert(table->remap[var_of(l)] == null_literal);
  table->remap[var_of(l)] = l1 ^ sign_of_lit(l);
}


/*
 * Auxiliary function used below: 
 * - flip the polary bit of l if sgn is 1 and l is non-null
 * - keep l unchanged otherwise
 */
static inline literal_t xor_sign(literal_t l, uint32_t sgn) {
  return (l == null_literal) ? l : (l ^ sgn);
}

/*
 * Return the literal assigned to to the class of l 
 * return null_literal if no literal is assigned to the class
 */
static inline literal_t remap_table_find(remap_table_t *table, literal_t l) {
  l = remap_table_find_root(table, l);
  return xor_sign(table->remap[var_of(l)], sign_of_lit(l));
}




#endif /* __REMAP_TABLE_H */
