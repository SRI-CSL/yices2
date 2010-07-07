/*
 * TABLE TO STORE A TERM SUBSTITUTION
 */

#ifndef __SUBST_TABLE_H
#define __SUBST_TABLE_H

/*
 * A substitution table is a union-find data structure:
 * - the table stores a term partitions
 * - each class in the partition contains terms that are known to be equal
 * - each class has a representative (root)
 * - all terms in a class, except possibly the root, is an uninterpreted term
 * - each class has a type, which is the intersection type of the class's elements
 *   (example if x has type <int, real> and y has type <real, int>, then a class
 *    that contains both x and y has type <int, int>).
 *
 * If t is stored in that table, then subst(t) is the root of t's class.
 */

#include <stdbool.h>
#include <stdint.h>
#include <assert.h>

#include "int_hash_sets.h"
#include "int_queues.h"
#include "int_vectors.h"
#include "backtrack_arrays.h"
#include "terms.h"


/*
 * A term t is a 32bit integer that includes a term idx + a polarity bit.
 * The polarity bit is 0 except for boolean terms. For a boolean index i, 
 * there are two terms 2i and 2i+1 that denote i and (not i), respectively.
 *
 * The subst_table consists of three arrays indexed by i:
 * - parent[i] = is a term
 * - type[i] = type label
 * - rank[i] = an 8bit value (for keeping the union-find structure balanced)
 * - i is the root of its class if we have parent[i] == i, and then type[i]
 *   is the type of the class.
 * - i is not in a class if  parent[i] is NULL_TERM
 *
 * Special code:
 * - if rank[i] is 255, then i is a root and it's not an uninterpreted term.
 *
 * Other components: 
 * - terms and types = pointer to the term and type tables
 *
 * We use backtrackable arrays for implementing push/pop
 * - the queue and cache are used to detect substitution cycles
 */
typedef struct subst_table_s {
  int32_array_t parent;
  int32_array_t type;
  uint8_array_t rank;
  term_table_t *terms;
  type_table_t *types;

  ivector_t aux_vector;
  int_hset_t *cache; // allocated on demand
  int_queue_t *queue; // allocated on demand
} subst_table_t;




/*
 * Initialize:
 * - n = initial size of all tables (0 means use default sizes)
 * - terms = attached term table
 * - the table stores the empty substitution
 */
extern void init_subst_table(subst_table_t *subst, uint32_t n, term_table_t *terms);


/*
 * Delete: free memory
 */
extern void delete_subst_table(subst_table_t *subst);


/*
 * Reset to the empty substitution
 */
extern void reset_subst_table(subst_table_t *subst);


/*
 * Push/pop
 */
extern void subst_table_push(subst_table_t *subst);
extern void subst_table_pop(subst_table_t *subst);


/*
 * Check whether t is present in the substitution table
 * - t must be an uninterpreted term
 * - t must have positive polarity
 */
static inline bool subst_table_member(subst_table_t *subst, term_t t) {
  assert(is_pos_term(t) && term_kind(subst->terms, t) == UNINTERPRETED_TERM);
  return ai32_read(&subst->parent, index_of(t)) != NULL_TERM;
}



/*
 * Parent of a term t:
 * - if t has positive polarity then parent(t) = parent(index_of(t))
 * - if t has negative polarity then parent(t) = opposite of parent(index_of(t))
 */
static inline term_t subst_table_parent(subst_table_t *subst, term_t t) {
  return ai32_read(&subst->parent, index_of(t)) ^ polarity_of(t);
}

/*
 * Check whether t is present and root of its class
 */
static inline bool subst_table_is_root(subst_table_t *subst, term_t t) {
  return subst_table_parent(subst, t) == t;
}


/*
 * Get the term mapped to t in the substitution table
 * - t must be an uninterpreted term and have positive polarity
 * - return t if t is not present in the table
 *   return the root of t's class otherwise (which may be t itself)
 * Side effect: applies path compression
 */
extern term_t subst_value(subst_table_t *subst, term_t t);


/*
 * Variant implementation: don't use path compression
 */
extern term_t find_subst_value(subst_table_t *subst, term_t t);


/*
 * Get the substitution type for r
 * - r must be a root in the substitution table
 */
static inline type_t subst_type(subst_table_t *subst, term_t r) {
  assert(subst_table_is_root(subst, r));
  return ai32_get(&subst->type, index_of(r));
}



/*
 * Check whether the substitution [t := v] is valid:
 * - t must be an uninterpreted term
 * - v must be a valid term of type compatible with t's type
 *
 * The substitution is valid if the following conditions are satisfied:
 * - there's no existing substitution for t: either t is not in the
 *   table or all terms in t's class are uninterpreted.
 * - replacing t by v does not introduce a cycle.
 */
extern bool subst_is_valid(subst_table_t *subst, term_t t, term_t v);


/*
 * Add the substitution [t := v] to the table.
 * - t must be uninterpreted and either root of its class or absent
 * - v must be a valid term of type compatible with t's type, 
 *   and it must be root of its class or absent from subst.
 * - the substitution must be valid.
 */
extern void subst_table_add(subst_table_t *subst, term_t t, term_t v);


/*
 * Merge the classes of t and v:
 * - both must be uninterpreted and either root of their class or absent
 *   from the substitution table.
 * - this adds the substitution [t := v] or [v := t]
 */
extern void subst_table_merge(subst_table_t *subst, term_t t, term_t v);


#endif /* __SUBST_TABLE_H */
