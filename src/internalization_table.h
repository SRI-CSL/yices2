/*
 * MAPPING OF TERMS TO SOLVER OBJECTS
 */

#ifndef __INTERNALIZATION_TABLE_H
#define __INTERNALIZATION_TABLE_H

/*
 * An internalization table keeps track of variable substitutions and
 * of the internal object (egraph term or other) mapped to terms.  The
 * table stores a partition of term indices in a union-find data
 * structure.  All the elements of an equivalence class are equal and
 * mapped to the same solver object.  Each class contains a
 * distinguished root element. All elements other than the root are
 * uninterpreted term indices (i.e., variables).
 *
 * - For a root r we store: 
 *      map[r] = object mapped to the class (or NULL)
 *     type[r] = type of the class
 *     rank[r] = an 8bit value for balancing the union-find structure
 *
 *   If rank[r] is 255 then the root is frozen. This means either that
 *   r is not an uninterpreted term or that r is mapped to a non-NULL object.
 *   It's not possible to merge two classes whose roots are both frozen.
 *
 *   If rank[r] is less than 255, then the root is free. This means
 *   that r is an uninterprreted term and is not mapped to any object
 *   yet (i.e., map[r] = NULL). The class of r contains has size >=
 *   2^rank[r] and all elements in the class are uninterpreted. It's
 *   possible to merge the class of r with another class.
 *
 * - a non-root i must be an uninterpreted term index and map[i] is the 
 *   parent of i in the union-find tree.
 *
 * To distinguish between roots and non-roots, we use the sign bit:
 *   map[i] < 0  if i is a root, and the object mapped to i is obtained
 *               by clearing the sign bit.
 *   map[i] >= 0 if i is not a root, then map[i] is a term (term index + polarity bit)
 *
 * For boolean classes, the polarity bit is significant. It's used for both
 * the terms and the internalization object:
 * 1) if r is the root of a boolean class then the low-order bit of map[r] is the 
 *    polarity bit of r's internalization value.
 *    if map[r] = x, then pos_term(r) --> x and neg_term(r) --> not(x).
 * 2) if i is not a root then map[i] is a boolean term t
 *    pos_term(i) --> t and neg_term(i) --> not(t).
 */

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "int_hash_sets.h"
#include "int_queues.h"
#include "backtrack_arrays.h"
#include "terms.h"


/*
 * To support push and pop, we use backtrackable arrays.
 * The auxiliary queue and cache are used in "occurs-check"
 * to prevent circular subsitutions.
 */
typedef struct intern_tbl_s {
  int32_array_t map;
  int32_array_t type;
  uint8_array_t rank;
  term_table_t *terms;
  type_table_t *types;

  int_hset_t *cache;  // allocated on demand
  int_queue_t *queue; // allocated on demand
} intern_tbl_t;



/*
 * Marker for NULL: map[i] = NULL_MAP means i is not internalized yet.
 */
#define NULL_MAP (-INT32_MAX)


/*
 * Initialization:
 * - n = initial size of all map/type/rank (0 means use default sizes)
 * - terms = attached term table
 * - the table stores the empty mapping
 */
extern void init_intern_tbl(intern_tbl_t *tbl, uint32_t n, term_table_t *terms);

/*
 * Delete: free memory
 */
extern void delete_intern_tbl(intern_tbl_t *tbl);


/*
 * Reset to the empty tblitution
 */
extern void reset_intern_tbl(intern_tbl_t *tbl);


/*
 * Push/pop
 */
extern void intern_tbl_push(intern_tbl_t *tbl);
extern void intern_tbl_pop(intern_tbl_t *tbl);




/*
 * ACCESS TO ROOTS
 */

/*
 * Check whether i is a root: this returns true if i is not 
 * present in the table.
 */
static inline bool intern_tbl_is_root_idx(intern_tbl_t *tbl, int32_t i) {
  assert(good_term_idx(tbl->terms, i));
  return ai32_read(&tbl->map, i) < 0;
}

static inline bool intern_tbl_is_root(intern_tbl_t *tbl, term_t t) {
  return intern_tbl_is_root_idx(tbl, index_of(t));
}


/*
 * Get the root of t's class
 * - this returns t if t is not in the table
 * - side effect: applies path compression.
 */
extern term_t intern_tbl_get_root(intern_tbl_t *tbl, term_t t);


/*
 * Variant implementation: don't apply path compression.
 */
extern term_t intern_tbl_find_root(intern_tbl_t *tbl, term_t t);




/*
 * INTERNALIZATION MAPPING
 */

/*
 * Check whether r is mapped to something (i.e., not NULL_MAP)
 */
static inline bool intern_tbl_root_is_mapped(intern_tbl_t *tbl, term_t t) {
  assert(intern_tbl_is_root(tbl, t));
  return ai32_read(&tbl->map, index_of(t)) != NULL_MAP;
}								  

/*
 * Object mapped to r: clear the sign bit
 */
static inline int32_t intern_tbl_map_of_root(intern_tbl_t *tbl, term_t t) {
  assert(intern_tbl_is_root(tbl, t));
  return ai32_read(&tbl->map, index_of(t)) & INT32_MAX;
}

/*
 * Type of r's class (return the type of r if r is not in tbl)
 */
extern type_t intern_tbl_type_of_root(intern_tbl_t *tbl, term_t t);


/*
 * Map r to object x
 * - x must be non-negative and strictly smaller than INT32_MAX
 *   the low order bit of x is interpreted as a polarity bit.
 * - r must be a root, not mapped to anything yet
 */
extern void intern_tbl_map_root(intern_tbl_t *tbl, term_t r, int32_t x);



/*
 * SUBSTITUTIONS
 */

/*
 * Check whether r is a free root:
 * - r must be a root
 * - if r is in the table, return true if rank[r] < 255, 
 *   otherwise, return true if r is uninterpreted.
 */
extern bool intern_tbl_root_is_free(intern_tbl_t *tbl, term_t r);


/*
 * Check whether the substitution [r1 := r2] is valid
 * - both r1 and r2 must be roots and they must have compatible types.
 * - r2 must not be a constant term.
 * - returns true if r1 is a free root, and the substitution does not 
 *   create a cycle.
 *
 * NOTE: if r2 is a constant, the next function should be used instead.
 */
extern bool intern_tbl_valid_subst(intern_tbl_t *tbl, term_t r1, term_t r2);


/*
 * Check whether the substitution [r1 := r2] is valid. 
 * - r1 must be a root and r2 must be a constant
 * - returns true if r1 is a free root and 
 *   if r2's type is a subtype of r1's class type.
 *
 * (e.g., x := 1/2 is not a valid substitution if x is an integer variable).
 */
extern bool intern_tbl_valid_const_subst(intern_tbl_t *tbl, term_t r1, term_t r2);


/*
 * Add the substitution [r1 := r2] to the table.
 * The substitution must be valid.
 */
extern void intern_tbl_add_subst(intern_tbl_t *tbl, term_t r1, term_t r2);


/*
 * Merge the classes of r1 and r2
 * - both r1 and r2 must be free roots and have compatible types
 *
 * This adds either the substitution [r1 := r2] or [r2 := r1]
 */
extern void intern_tbl_merge_classes(intern_tbl_t *tbl, term_t r1, term_t r2);


#endif /* __INTERNALIZATION_TABLE_H */
