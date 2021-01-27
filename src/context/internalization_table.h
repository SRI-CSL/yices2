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
 *   that r is an uninterpreted term and is not mapped to any object
 *   yet (i.e., map[r] = NULL). The class of r has size >= 2^rank[r]
 *   and all elements in the class are uninterpreted. It's possible to
 *   merge r's class with another class.
 *
 *   The table is a partial map. The domain is defined by the set of 
 *   terms r such that type[r] != NULL_TYPE. If type[r] is NULL_TYPE,
 *   then r is implicitly considered to be a root (cf. intern_tbl_is_root
 *   and intern_tbl_get_root).
 *
 * - a non-root i must be an uninterpreted term index and map[i] is the
 *   parent of i in the union-find tree.
 *
 * To distinguish between roots and non-roots, we use the sign bit:
 *   map[i] < 0  if i is a root, and the object mapped to i is obtained
 *               by clearing the sign bit.
 *   map[i] >= 0 if i is not a root, then map[i] is a term (term index + polarity bit)
 *
 * For boolean classes, the polarity bit is significant: the
 * substitution may map a boolean index 'i' to term '(not t)'. Then
 * the root of 'i' is '(not t)'.
 *
 * The type of a class (attached to the class root) is the intersection type
 * of all the class elements. If the root is not frozen this is the exact
 * type of the class.
 *
 * WARNING: If a root r is frozen, then type[r] is guaranteed to be a
 * supertype of the class's type, but type[r] may be inexact. Finding
 * the exact type of frozen classes would require dynamically
 * recomputing the types as classes are merged. For example, given
 * the declarations:
 *   x :: real
 *   i :: int
 *   r := 3 x + 1
 * then r has type real. But if we merge x and i (i.e., assert x == i),
 * then the type of r becomes int.  We don't do this dynamic type computation.
 * Type[r] is set when r is added to a class, and it remain unchanged,
 * independent of substitutions like x == i.
 */

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "terms/terms.h"
#include "utils/backtrack_arrays.h"
#include "utils/int_hash_sets.h"
#include "utils/int_queues.h"
#include "solvers/egraph/egraph_base_types.h"


/*
 * To support push and pop, we use backtrackable arrays.
 * The auxiliary queue and cache are used in "occurs-check"
 * to prevent circular substitutions.
 */
typedef struct intern_tbl_s {
  int32_array_t map;
  int32_array_t type;
  uint8_array_t rank;
  term_table_t *terms;
  type_table_t *types;

  int_hset_t *cache;  // allocated on demand
  int_queue_t *queue; // allocated on demand

  int_hmap_t reverse_map;   // map from occurence to term
} intern_tbl_t;



/*
 * Marker for NULL: map[i] = NULL_MAP means i is not internalized yet.
 */
#define NULL_MAP (-1)


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
 * Reset to the empty table
 */
extern void reset_intern_tbl(intern_tbl_t *tbl);


/*
 * Push/pop
 */
extern void intern_tbl_push(intern_tbl_t *tbl);
extern void intern_tbl_pop(intern_tbl_t *tbl);



/*
 * Get a bound on the number of terms in tbl:
 * - if n = intern_tbl_num_terms(tbl) then terms of
 *   index >= n are roots and not mapped to anything
 */
static inline uint32_t intern_tbl_num_terms(intern_tbl_t *tbl) {
  return tbl->map.top;
}


/*
 * ACCESS TO ROOTS
 */

/*
 * Check whether t is in the table
 */
static inline bool intern_tbl_term_present(intern_tbl_t *tbl, term_t t) {
  assert(good_term(tbl->terms, t));  
  return ai32_read(&tbl->type, index_of(t)) != NULL_TYPE;
}


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
 * For a root index k, the id of the corresponding solver object is
 * stored in the 31 low-order bits of map[k]. The sign bit of map[k]
 * is 1.  Because NULL_MAP is -1, id must be between 0 and
 * INT32_MAX-1.
 *
 * For Boolean classes, we use the convention that map[k] is the
 * object mapped to r = pos_term(k). So all operations that extract or
 * set the map of r require a term r of positive polarity (so we use k =
 * index_of(r)).
 */


/*
 * Check whether r is mapped to something (i.e., not NULL_MAP)
 * - r must be a root (it may have negative polarity).
 */
static inline bool intern_tbl_root_is_mapped(intern_tbl_t *tbl, term_t r) {
  assert(intern_tbl_is_root(tbl, r));
  return ai32_read(&tbl->map, index_of(r)) != NULL_MAP;
}

/*
 * Type of r's class (return the type of r if r is not in tbl)
 * - r must be a root (it may have negative polarity)
 */
extern type_t intern_tbl_type_of_root(intern_tbl_t *tbl, term_t r);


/*
 * Check whether r's class is integer
 * - r must be a root
 */
static inline bool intern_tbl_is_integer_root(intern_tbl_t *tbl, term_t r) {
  return intern_tbl_type_of_root(tbl, r) == int_type(tbl->types);
}


/*
 * Get the object mapped to r: clear the sign bit
 * - r must be a root and must have positive polarity
 */
static inline int32_t intern_tbl_map_of_root(intern_tbl_t *tbl, term_t r) {
  assert(is_pos_term(r) && intern_tbl_is_root(tbl, r));
  return ai32_read(&tbl->map, index_of(r)) & INT32_MAX;
}


/*
 * Map r to object x
 * - x must be non-negative and strictly smaller than INT32_MAX
 * - r must be a root, not mapped to anything yet, and must have positive
 *   polarity.
 */
extern void intern_tbl_map_root(intern_tbl_t *tbl, term_t r, int32_t x);


/*
 * Map r to a new object x
 * - x must be non-negative and strictly smaller than INT32_MAX
 * - r must be a root, mapped to something, and must have positive polarity
 */
extern void intern_tbl_remap_root(intern_tbl_t *tbl, term_t r, int32_t x);

/*
 * Return the term mapped to occurence x (if any)
 */
extern term_t intern_tbl_reverse_map(intern_tbl_t *tbl, occ_t x);


/*
 * SUBSTITUTIONS
 */

/*
 * Check whether r is a free root:
 * - r must be a root (may have negative polarity)
 * - if r is in the table, return true if rank[r] < 255,
 *   otherwise, return true if r is uninterpreted.
 */
extern bool intern_tbl_root_is_free(intern_tbl_t *tbl, term_t r);

#if 0

// NOT USED
/*
 * Check whether the substitution [r1 := r2] is valid
 * - both r1 and r2 must be roots and they must have compatible types.
 * - r1 must have positive polarity.
 * - r2 must not be a constant term.
 * - returns true if r1 is a free root, and the substitution does not
 *   create a cycle.
 *
 * NOTE: if r2 is a constant, the next function should be used instead.
 */
extern bool intern_tbl_valid_subst(intern_tbl_t *tbl, term_t r1, term_t r2);
#endif

/*
 * Check whether the substitution [r1 := r2] is valid.
 * - r1 must be a root and r2 must be a constant
 * - r1 must have positive polarity
 * - returns true if r1 is a free root and
 *   if r2's type is a subtype of r1's class type.
 *
 * (e.g., x := 1/2 is not a valid substitution if x is an integer variable).
 */
extern bool intern_tbl_valid_const_subst(intern_tbl_t *tbl, term_t r1, term_t r2);

/*
 * Check whether the substitution [r1 := r2] is sound
 * - r1 must be a root
 * - r2 must be frozen
 * - returns true if r1 is a free root and r2's type is a subtype of r1's class type
 *
 * E.g., if r1 has integer type and r2 has real type then the substitution is not
 * sound.
 */
extern bool intern_tbl_sound_subst(intern_tbl_t *tbl, term_t r1, term_t r2);

/*
 * Add the substitution [r1 := r2] to the table.
 * The substitution must be valid.
 */
extern void intern_tbl_add_subst(intern_tbl_t *tbl, term_t r1, term_t r2);


/*
 * Merge the classes of r1 and r2
 * - both r1 and r2 must be free roots and have compatible types
 * - if both r1 and r2 are boolean, they may have arbitrary polarity
 * This adds either the substitution [r1 := r2] or [r2 := r1]
 */
extern void intern_tbl_merge_classes(intern_tbl_t *tbl, term_t r1, term_t r2);


/*
 * SUPPORT FOR GARBAGE COLLECTION
 */

/*
 * Mark all terms in the domain of tbl as roots for the next call to term_table_gc.
 * Also mark all types stored in type[x] for x in tbl.
 */
extern void intern_tbl_gc_mark(intern_tbl_t *tbl);


#endif /* __INTERNALIZATION_TABLE_H */
