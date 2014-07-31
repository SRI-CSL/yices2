/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Support for handling arithmetic equalities of the form x = y + k
 * where x and y are variables and k is a constant.
 */

/*
 * When we connect the Simplex solver and the Egraph, equality
 * constraints propagated from the Egraph get turned into rows of the
 * form z = x - y in the tableau, with the constraint 0 <= z <= 0
 * asserted on z.  We also get equalities of the same form but with
 * constraints a <= z <= a where a is a non-zero rational.
 *
 * We want to propagate equalities in the other direction (from
 * Simplex to the egraph). A relatively simple technique is to
 * focus on offset equalities and propagate their consequences.
 *
 * Example: if egraph term t1 is mapped to p1 = x1 + 2 x2 + 1 in
 * Simplex and term t2 is mapped to p2 = x3 + 2 x2 + 2 in Simplex,
 * then we can propagate t1 == t2 to the Egraph when the offset
 * equality (x1 == x3 + 1) is asserted.
 *
 * To support this, we keep the polynomials p1 and p2 normalized
 * modulo a set of offset equalities. We use data structures similar
 * to the Egraph.
 *
 * We keep variables stored into equivalence classes: the class
 * contains a root variable r, all other variables in the class are
 * equal to r + a constant.  When a new offset equality is asserted,
 * we merge two equivalence classes.
 *
 * To propagate equalities to the Egraph, we store polynomials in a
 * hash table that uses equality modulo the offset classes.  This is
 * cheap to implement, since we just apply a variable substitution of
 * the form x := r + k (replace x by its root + offset pair).
 */

#ifndef __OFFSET_EQUALITIES_H
#define __OFFSET_EQUALITIES_H

#include <stdint.h>
#include <stdbool.h>

#include "utils/bitvectors.h"
#include "utils/object_stores.h"
#include "utils/int_vectors.h"
#include "terms/rationals.h"
#include "terms/polynomials.h"
#include "terms/poly_buffer.h"
#include "solvers/egraph/egraph_base_types.h"


/*
 * Resizable array to map external variables (i.e., variables in the
 * Simplex solver) to internal indices (either polynomial indices or
 * offset variables).
 * - data[x] = -1 by default
 */
typedef struct {
  int32_t *data;
  uint32_t size;
} remap_array_t;

#define DEF_REMAP_ARRAY_SIZE 200
#define MAX_REMAP_ARRAY_SIZE (UINT32_MAX/sizeof(int32_t))


/*
 * Dependency records
 * ------------------
 * Given a polynomial index i, we keep track of the offset variables that
 * occur with a non-zero coefficient in poly[i]'s normal form.
 *
 * Conversely, given an offset variable x, we keep in dep[x] the index
 * of all polynomials that contain x. If x is such a variable, then
 * 'i' occurs at some position 'k' in index vector dep[x].
 *
 * In vars[i], we store the root variable 'x' and the index 'k'
 * - i.e., we maintain the invariant:
 *    dep[x][k] = i <==> vars[i] contains a dependency record <x. k>
 *
 * To support this, vars[i] is an array of pairs <x. k> + header information.
 *
 * For dep[x], we use a resizable array.
 * - the indices of polynomials that depend on x are stored in dep[x]->data[k]
 * - when the dependency is removed, then data[k] is set to a negative value
 * - the negative elements in array data encode a free list.
 */

// record for vars[i]
typedef struct var_rec_s {
  int32_t var;   // x
  uint32_t idx;  // k
} var_rec_t;

typedef struct var_array_s {
  uint32_t size;      // size of the array
  uint32_t ndeps;     // number of records in use
  var_rec_t data[0];  // actual size is defined at allocation time
} var_array_t;

#define MAX_VAR_ARRAY_SIZE ((UINT32_MAX - sizeof(var_array_t))/sizeof(var_rec_t))


/*
 * Data structure for dep[x]
 * - size = size of array data
 * - elements are stored in data[0 ... nelems - 1]
 * - free_list = start of the free list
 *
 * A free_list index k is encoded using negative numbers:
 * - if data[i] is free then the index i is encoded as (i + INT32_MIN)
 * - the end marker for the free list is MAX_DEP_ARRAY_SIZE
 */
typedef struct dep_s {
  uint32_t size;
  uint32_t nelems;
  int32_t free_list;
  int32_t data[0];
} dep_t;

#define DEF_DEP_ARRAY_SIZE 20
#define MAX_DEP_ARRAY_SIZE ((UINT32_MAX - sizeof(dep_t))/sizeof(int32_t))


/*
 * Encoding/decoding of index i into negative numbers
 */
static inline int32_t encode_idx(int32_t i) {
  assert(0 <= i && i <= MAX_DEP_ARRAY_SIZE);
  return i + INT32_MIN;
}

static inline int32_t decode_idx(int32_t i) {
  assert(i < 0);
  return i - INT32_MIN;
}


/*
 * Tracked polynomials
 * -------------------
 * - polynomials are indexed from 0 to npolys - 1
 * - each polynomial represents a triple (t, x, p)
 *   - t is an egraph term
 *   - x is the arithmetic variable attached to t in the arithmetic solver
 *   - p is the definition of x
 *       there are two cases:
 *       if x is a free variable in the arithmetic solver, then p is 1.x
 *       otherwise, x denotes a polynomial q in the arithmetic solver then
 *       p is the same as q
 *
 * The variables of p are variables defined in the arithmetic solver.
 * Each of them is internally renamed to an offset variable. The mapping
 * from arithmetic to offset variables is stored in the offset table.
 *
 * The normal form of p is obtained by replacing the variables of p by
 * corresponding offset variables then substituting these offset
 * variables by their definition (root + k). Two polynomials are equal
 * modulo a set of offset equalities if their normal forms are the
 * same.
 *
 * We keep track of whether i is present in the hash table or not:
 * - if bit active is 1, then i is present in the hash table
 *   it is also attached to the dependency vectors.
 * - if bit active is 0, then i is not present in the hash table
 *   and not attached to the dependency vectors.
 *   This means that either i has just been created and its normal form
 *   has not been computed yet, or that i is equal to another polynomial j
 *   present in the hash table. If i is inactive, then it must be in
 *   the inactive_queue (or in the to_process vector).
 *
 * If i must be processed, then it's stored in the 'to_process' vector.
 * - mark[i] keeps track of this (mark[i] == 1 iff i is in the to_process vector)
 *
 * For each index i in 0 to npolys - 1, we store:
 * - eterm[i] = egraph term that i represents (i.e., t)
 * - def[i] = polynomial p
 * - hash[i] = hash code of p's normal form
 * - vars[i] = offset variables that occur in p
 * - active[i] = active bit
 * - mark[i] = mark bit
 *
 * When the triple (t, x, p) is registered, we also store that i
 * corresponds to variable 'x' in the var2poly map.
 *
 * We use an object store to allocate polynomials (when we need to
 * construct p := 1.x for some variable x).
 */
typedef struct offset_poly_table_s {
  uint32_t npolys;
  uint32_t size;    // size of arrays eterm, hash, def, vars
  eterm_t *eterm;
  polynomial_t **def;
  uint32_t *hash;
  var_array_t **vars;
  byte_t *active;
  byte_t *mark;
  remap_array_t var2poly;   // mapping from variable to poly id
  object_store_t pstore;    // store for polynomial construction
} offset_poly_table_t;

#define DEF_OFFSET_POLY_TABLE_SIZE 40
#define MAX_OFFSET_POLY_TABLE_SIZE ((UINT32_MAX)/sizeof(polynomial_t *))


/*
 * Offset variable table
 * ---------------------
 * - offset variables are indexed from 0 to nvars - 1
 * - index 0 has a special interpretation. It denotes 'zero'.
 *   This is used to process equalities of the form x == constant
 *   (we turn this into the offset equality x = zero + constant).
 *
 * - variables are grouped into equivalence classes: x and y
 *   are in the same class if (x - y) is a constant. To represent
 *   these classes: we pick a root variable 'r' in each class,
 *   then for every variable x, we store the root of x's class and
 *   the offset of x relative to this root. All variables in the
 *   same class are linked together in a circular list.
 *
 * - to generate explanations, we keep a merge tree per class.
 *   - edges in the merge tree are indices in the offset equality queue.
 *   - equality x := y + k forms an edge from x to y, labeled by k.
 *   - we store in edge[x] the edge that goes from x to its parent in
 *     the merge tree.
 *   - the root 'r' of x's class is also the root of x's merge tree,
 *     and it has edge[r] = -1.
 *
 * - for each variable we store
 *     desc[x] = descriptor of x
 *     edge[x] = index of the equality from x to its parent in the merge tree
 *     dep[x] = vector of polynomial indices (see index_vectors.h)
 *
 * - if x is a root we have
 *     desc[x].root = x
 *     desc[x].offset = 0
 *     edge[x] = -1
 *
 * - if x is not a root
 *     desc[x].root = r
 *     desc[x].offset = k
 *     edge[x] = index of an equality in the equality queue
 *
 * We also keep the renaming of arithmetic variables in var2offset_var.
 */
typedef struct offset_desc_s {
  int32_t next;
  int32_t root;
  rational_t offset;
} offset_desc_t;

typedef struct offset_table_s {
  uint32_t nvars;
  uint32_t size;
  offset_desc_t *desc;
  int32_t *edge;
  dep_t **dep;
  remap_array_t var2offset_var;
} offset_table_t;

#define DEF_OFFSET_TABLE_SIZE 100
#define MAX_OFFSET_TABLE_SIZE (UINT32_MAX/sizeof(offset_desc_t))


/*
 * Hash table for normalized polynomials
 * - data[i] stores a pair [hash-code, polynomial index]
 *   where the polynomial index is an index in the offset_poly_table
 *   and hash is the hash code of that polynomial
 * - index = -1 means that data[i] is not used
 * - index = -2 means that data[i] is deleted
 */
typedef struct offset_hash_elem_s {
  int32_t index;
  uint32_t hash;
} offset_hash_elem_t;

typedef struct offset_hash_table_s {
  offset_hash_elem_t *data;
  uint32_t size;              // must be a power of 2
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} offset_hash_table_t;

#define DEF_OFFSET_HASH_TABLE_SIZE 64
#define MAX_OFFSET_HASH_TABLE_SIZE (UINT32_MAX/sizeof(offset_hash_elem_t))

#define OFFSET_HASH_TABLE_RESIZE_RATIO 0.6
#define OFFSET_HASH_TABLE_CLEANUP_RATIO 0.2


/*
 * Queue of offset equalities
 * --------------------------
 *
 * An offset equality is of the form x := y + c where x and y are both
 * in the offset_table and c is a constant. Each equality also has
 * an integer 'id' that's used to build explanations. When an equality
 * is asserted, it must be given a unique id.
 *
 * - eq[i] is an asserted equality (for 0 <= i < top)
 *   id[i] = corresponding id
 * - top = top of the stack
 * - prop_ptr = start of the propagation queue
 * - size = size of arrays eq and id
 *
 * The equalities are organized by decision levels.
 */
typedef struct offset_eq_s {
  int32_t lhs;       // the variable x that gets eliminated
  int32_t rhs;       // the variable y
  rational_t offset; // the constant c
} offset_eq_t;

typedef struct offset_equeue_s {
  offset_eq_t *eq;
  int32_t *id;
  uint32_t prop_ptr;
  uint32_t top;
  uint32_t size;

  uint32_t *level_index;
  uint32_t nlevels;
} offset_equeue_t;

#define DEF_OFFSET_EQUEUE_SIZE 100
#define MAX_OFFSET_EQUEUE_SIZE (UINT32_MAX/sizeof(offset_eq_t))


/*
 * Undo stack
 * ----------
 *
 * - when we process equality (x := y + k), we find rx := x's root
 *   then we change the descriptors of all elements in rx's class
 *   and we add an edge from x to y in the merge trees.
 * - when we backtrack, we need to revert this. It's enough to keep
 *   track of x and rx.
 * We store both in the undo stack.
 */
typedef struct offset_undo_s {
  int32_t saved_var;   // x
  int32_t saved_root;  // rx
} offset_undo_t;

typedef struct offset_undo_stack_s {
  offset_undo_t *data;
  uint32_t top;
  uint32_t size;
} offset_undo_stack_t;

#define DEF_OFFSET_UNDO_SIZE 100
#define MAX_OFFSET_UNDO_SIZE (UINT32_MAX/sizeof(offset_undo_t))


/*
 * Inactive polynomials
 */
typedef struct inactive_poly_queue_s {
  int32_t *data;
  uint32_t top;
  uint32_t size;
} inactive_poly_queue_t;

#define DEF_INACTIVE_QUEUE_SIZE 100
#define MAX_INACTIVE_QUEUE_SIZE (UINT32_MAX/sizeof(int32_t))


/*
 * Stack for backtracking:
 * -----------------------
 *
 * For every decision level, we keep
 * - the current top of the queues above:
 *   data[k].eq_ptr = pointer to the first equality asserted at level k (in offset_equeue)
 *   data[k].undo_ptr = pointer to the first undo record pushed at level k (in undo_stack)
 *   data[k].inactive_ptr = pointer to the first inactive poly at level k
 */
typedef struct level_record_s {
  uint32_t eq_ptr;
  uint32_t undo_ptr;
  uint32_t inactive_ptr;
} level_record_t;

typedef struct offset_level_stack_s {
  level_record_t *data;
  uint32_t size;
} offset_level_stack_t;

#define DEF_OFFSET_LEVEL_STACK_SIZE 40
#define MAX_OFFSET_LEVEL_STACK_SIZE (UINT32_MAX/sizeof(level_record_t))


/*
 * Out-of-order polynomials
 * - if a polynomial i is added during the search (at decision level k > base_level)
 *   then we may discover that (i == j) for some other polynomial j
 * - this equality will be reported first at level k (first call to propagate after
 *   i is added) but it may be true at levels < k.
 * - to deal with this, we store all polynomials added during the search to
 *   the following recheck structure. When we backtrack to decision level <= k, we
 *   move all polynomials added at levels > k to the process queue.
 *
 * Each element in the recheck queue stores a polynomial id + the decision level at
 * which this polynomial was added.
 */
typedef struct recheck_elem_s {
  int32_t id;
  uint32_t level;
} recheck_elem_t;

typedef struct recheck_queue_s {
  recheck_elem_t *data;
  uint32_t top;  // top of the queue
  uint32_t size; // size of the data array
} recheck_queue_t;

#define DEF_RECHECK_QUEUE_SIZE 20
#define MAX_RECHECK_QUEUE_SIZE (UINT32_MAX/sizeof(recheck_elem_t))


/*
 * Trail stack for push/pop
 * - for each base-level we record
 *   the number of polys in ptable
 *   the number of variables in vtable
 *   the current propagation pointer
 */
typedef struct offset_trail_s {
  uint32_t npolys;
  uint32_t nvars;
  uint32_t prop_ptr;
} offset_trail_t;

typedef struct offset_trail_stack_s {
  offset_trail_t *data;
  uint32_t top;
  uint32_t size;
} offset_trail_stack_t;

#define DEF_OFFSET_TRAIL_SIZE 20
#define MAX_OFFSET_TRAIL_SIZE (UINT32_MAX/sizeof(offset_trail_t))


/*
 * When an equality is discovered between two polynomials, a
 * callback function is called:
 * - first argument = a generic void * pointer
 * - second and third argument = the two eterms that have become equal
 */
typedef void (*eq_notifier_t)(void *aux, eterm_t t1, eterm_t t2);


/*
 * Full offset-equality solver
 * - when a polynomial is created or its normal form needs to
 *   be recomputed, we store in in vector 'to_process' and we mark it
 * - conflict_eq = index of the first equality in queue that caused a conflict
 *               (or -1 if there's no conflict).
 */
typedef struct offset_manager_s {
  void *external;
  eq_notifier_t notify_eq;

  uint32_t base_level;
  uint32_t decision_level;
  int32_t conflict_eq;

  offset_poly_table_t ptable;
  offset_table_t vtable;
  offset_hash_table_t htbl;
  offset_equeue_t queue;
  offset_undo_stack_t undo;
  inactive_poly_queue_t inactives;
  offset_level_stack_t stack;
  offset_trail_stack_t tstack;

  recheck_queue_t recheck;
  ivector_t to_process;

  poly_buffer_t buffer1;
  poly_buffer_t buffer2;
  rational_t aux;

} offset_manager_t;



/*
 * Initialize
 * - ext: external object passed as argument to notifier
 * - f: the callback
 */
extern void init_offset_manager(offset_manager_t *m, void *ext, eq_notifier_t f);

extern void delete_offset_manager(offset_manager_t *m);

extern void reset_offset_manager(offset_manager_t *m);


/*
 * Start a new base level
 */
extern void offset_manager_push(offset_manager_t *m);


/*
 * Restore the previous level
 */
extern void offset_manager_pop(offset_manager_t *m);


/*
 * Record the triple (t, x, p) as a polynomial to monitor
 * - t = egraph term
 * - x = arithmetic variable (must be the theory variable of t)
 * - p = either x's definition or NULL
 *
 * If p is NULL, then the internal definition will be 1.x
 */
extern void record_offset_poly(offset_manager_t *m, eterm_t t, thvar_t x, polynomial_t *p);


/*
 * Push equality (x == y + k) into the queue
 * - id = unique id for this equality
 * - if y is -1, the assertion is interpreted as x == k
 * - if x is -1. the assertion is interpreted as y + k == 0
 * - otherwise both x and y must be arithmetic variables.
 * - the equality is ignored if x or y are not mapped to an offset variable in m
 */
extern void assert_offset_equality(offset_manager_t *m, thvar_t x, thvar_t y, rational_t *k, int32_t id);


/*
 * Process all equalities in the queue
 * - if two monitored polynomials become equal, the notify_eq function is called
 * - return false if a conflict is detected
 * - return true otherwise
 */
extern bool offset_manager_propagate(offset_manager_t *m);


/*
 * Collect the ids of equalities that caused a conflict
 * - this can be used to get an explanation when propagate returns false
 * - the ids are added to vector v (v is not reset)
 */
extern void offset_manager_explain_conflict(offset_manager_t *m, ivector_t *v);


/*
 * Build an explanation for (x == y)
 * - x and y must be present in the internal poly table
 *   and they must have equal normal form
 * - this function collect the ids of equalities that imply x == y into vector v
 *   (v is not reset)
 */
extern void offset_manager_explain_equality(offset_manager_t *m, thvar_t x, thvar_t y, ivector_t *v);


/*
 * Increase decision level
 * - record the current size of the propagation queue
 */
extern void offset_manager_increase_decision_level(offset_manager_t *m);


/*
 * Backtrack to decision level k
 * - remove all equalities asserted at levels > k
 */
extern void offset_manager_backtrack(offset_manager_t *m, uint32_t k);


#endif /* __OFFSET_EQUALITIES_H */
