/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Construction and operations on composite objects.
 */

#ifndef __COMPOSITES_H
#define __COMPOSITES_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "solvers/egraph/egraph_types.h"
#include "utils/use_vectors.h"
#include "utils/arena.h"


/*******************
 *  CONSTRUCTORS   *
 ******************/

/*
 * (apply f a[0] ... a[n-1])
 * (update f a[0] ... a[n-1] v)
 * (tuple a[0] ... a[n-1])
 * (eq t1 t2)
 * (distinct a[0] ... a[n-1])
 * (ite t1 t2 t3)
 * (or a[0] ... a[n-1])
 * (lambda t tag)
 *
 * For lambda terms: tag is an integer that's used to distinguish lambda terms
 * with different domains.
 *
 * hash is set to 0
 * id is set to null_eterm
 * for every child, hook is set to no_ptr
 */

/*
 * Long-term composites: allocated using safe_malloc
 * Must be deleted explicitly using safe_free
 */
extern composite_t *new_apply_composite(occ_t f, uint32_t n, occ_t *a);
extern composite_t *new_update_composite(occ_t f, uint32_t n, occ_t *a, occ_t v);
extern composite_t *new_tuple_composite(uint32_t n, occ_t *a);
extern composite_t *new_eq_composite(occ_t t1, occ_t t2);
extern composite_t *new_distinct_composite(uint32_t n, occ_t *a);
extern composite_t *new_ite_composite(occ_t t1, occ_t t2, occ_t t3);
extern composite_t *new_or_composite(uint32_t n, occ_t *a);
extern composite_t *new_lambda_composite(occ_t t, int32_t tag);

/*
 * Temporary composites: allocated in arena m
 * Deleted when arena_pop is called
 */
extern composite_t *arena_apply_composite(arena_t *m, occ_t f, uint32_t n, occ_t *a);
extern composite_t *arena_update_composite(arena_t *m, occ_t f, uint32_t n, occ_t *a, occ_t v);
extern composite_t *arena_tuple_composite(arena_t *m, uint32_t n, occ_t *a);
extern composite_t *arena_eq_composite(arena_t *m, occ_t t1, occ_t t2);
extern composite_t *arena_distinct_composite(arena_t *m, uint32_t n, occ_t *a);
extern composite_t *arena_ite_composite(arena_t *m, occ_t t1, occ_t t2, occ_t t3);
extern composite_t *arena_or_composite(arena_t *m, uint32_t n, occ_t *a);
extern composite_t *arena_lambda_composite(arena_t *m, occ_t t, int32_t tag);

/*
 * Variants for or and distinct: do not allocate the hook parts
 * - these composites cannot be attached to the parents vectors
 */
extern composite_t *new_distinct_composite_var(uint32_t n, occ_t *a);
extern composite_t *new_or_composite_var(uint32_t n, occ_t *a);



/**************************
 *  HASH-CONSING SUPPORT  *
 *************************/

/*
 * Syntactic equality:
 * check whether  c == (apply f a[0] ... a[n-1]) etc.
 */
extern bool equal_apply(composite_t *c, occ_t f, uint32_t n, occ_t *a);
extern bool equal_update(composite_t *c, occ_t f, uint32_t n, occ_t *a, occ_t v);
extern bool equal_tuple(composite_t *c, uint32_t n, occ_t *a);
extern bool equal_eq(composite_t *c, occ_t t1, occ_t t2);
extern bool equal_distinct(composite_t *c, uint32_t n, occ_t *a);
extern bool equal_ite(composite_t *c, occ_t t1, occ_t t2, occ_t t3);
extern bool equal_or(composite_t *c, uint32_t n, occ_t *a);
extern bool equal_lambda(composite_t *c, occ_t t, int32_t tag);

/*
 * Hash (not the same as the internal c->hash, used for congruence)
 */
extern uint32_t hash_apply(occ_t f, uint32_t n, occ_t *a);
extern uint32_t hash_update(occ_t f, uint32_t n, occ_t *a, occ_t v);
extern uint32_t hash_tuple(uint32_t n, occ_t *a);
extern uint32_t hash_eq(occ_t t1, occ_t t2);
extern uint32_t hash_distinct(uint32_t n, occ_t *a);
extern uint32_t hash_ite(occ_t t1, occ_t t2, occ_t t3);
extern uint32_t hash_or(uint32_t n, occ_t *a);
extern uint32_t hash_lambda(occ_t t, int32_t tag);

extern uint32_t hash_composite(composite_t *c);


/********************
 *  PARENT VECTORS  *
 *******************/

/*
 * Attach c to the use vectors u, using labeling label
 * - if c->child[i] = t, then c is added to u[k]
 *   where k = class of t = class_of(label[term_of(t)])
 */
extern void attach_composite(composite_t *c, elabel_t *label, use_vector_t *u);

/*
 * Converse operation: remove c from the use vectors u
 */
extern void detach_composite(composite_t *c, elabel_t *label, use_vector_t *u);

/*
 * Remove c from the use vectors, except u[r0]
 */
extern void separate_composite(composite_t *c, elabel_t *label, use_vector_t *u, class_t r0);

/*
 * Replacements for separate/attach to improve performance
 * in egraph's process_equality (not used yet).
 */
extern void unhook_composite(composite_t *c, elabel_t *label, class_t r0);
extern void hook_composite(composite_t *c, elabel_t *label, use_vector_t *u, class_t r0);


/*
 * Hide c from the use vectors:
 * - c stays in the use vectors but it's marked as invalid
 */
extern void hide_composite(composite_t *c, elabel_t *label, use_vector_t *u);


/*
 * Converse operation: clear the marks
 */
extern void reveal_composite(composite_t *c, elabel_t *label, use_vector_t *u);



/***************************
 *  SIGNATURE COMPUTATION  *
 **************************/

/*
 * Initialize/delete signature buffer s
 */
extern void init_sign_buffer(signature_t *s);
extern void delete_sign_buffer(signature_t *s);

/*
 * Store signature of c into s:
 * - label must map term ids to class labels
 */
extern void signature_composite(composite_t *c, elabel_t *label, signature_t *s);

/*
 * Specialized versions, faster if the type of c is known
 * - signature_basic is for apply/update/tuple terms
 */
extern void signature_basic(composite_t *c, elabel_t *label, signature_t *s);
extern void signature_eq(composite_t *c, elabel_t *label, signature_t *s);
extern void signature_ite(composite_t *c, elabel_t *label, signature_t *s);
extern void signature_distinct(composite_t *c, elabel_t *label, signature_t *s);
extern void signature_or(composite_t *c, elabel_t *label, signature_t *s);
extern void signature_lambda(composite_t *c, elabel_t *label, signature_t *s);

static inline void signature_apply(composite_t *c, elabel_t *label, signature_t *s) {
  assert(composite_kind(c) == COMPOSITE_APPLY);
  signature_basic(c, label, s);
}

static inline void signature_update(composite_t *c, elabel_t *label, signature_t *s) {
  assert(composite_kind(c) == COMPOSITE_UPDATE);
  signature_basic(c, label, s);
}

static inline void signature_tuple(composite_t *c, elabel_t *label, signature_t *s) {
  assert(composite_kind(c) == COMPOSITE_TUPLE);
  signature_basic(c, label, s);
}



/*
 * Compute a hash of signature s
 */
extern uint32_t hash_signature(signature_t *s);

/*
 * Check whether s1 and s2 are equal
 */
extern bool equal_signatures(signature_t *s1, signature_t *s2);

/*
 * Check whether s is equal to c's signature.
 * - aux must be distinct from s and initialized.
 * - it's used as an auxiliary buffer if c is (or ...) or (distinct ...)
 */
extern bool signature_matches(composite_t *c, signature_t *s, signature_t *aux, elabel_t *label);





/**********************************
 *  SUPPORT FOR THE ARRAY SOLVER  *
 *********************************/

/*
 * Support for the array-theory solver:
 * - given c = (apply f i_1 ... i_n) compute a signature of c with f replaced by g
 * - i.e., this builds the signature of (apply g i_1 ... i_n)
 */
extern void signature_modified_apply(composite_t *c, eterm_t g, elabel_t *label, signature_t *s);


/*
 * Variant: compute the signature of c with f replaced by the glabel
 */
extern void signature_modified_apply2(composite_t *c, elabel_t glabel, elabel_t *label, signature_t *s);



/*
 * Check whether two apply composites have the same argument tuple (modulo the egraph)
 * - c must be of the form (apply f i_1 ... i_n)
 *   d must be of fhe form (apply g j_i ... j_m)
 * - return true if n == m and label[i_1] = label[j_1], ..., label[i_n] = label[j_m]
 */
extern bool same_arg_signature(composite_t *c, composite_t *d, elabel_t *label);


/*
 * Compute a hash code of c's argument tuple
 * - c must be of the form (apply f i_1 ... i_n)
 * - return a hash computed based on n and label[i_1], ..., label[i_n]
 * - so if same_arg_signature(c, d, label) is true then
 *   hash_arg_signature(c, label) = hash_arg_signature(d, label).
 */
extern uint32_t hash_arg_signature(composite_t *c, elabel_t *label);





/**********************
 *  CONGRUENCE TABLE  *
 *********************/

/*
 * Initialization.
 * - n = initial size, must be a power of 2
 * - if n = 0 the default size is used.
 */
extern void init_congruence_table(congruence_table_t *tbl, uint32_t n);

/*
 * Delete
 */
extern void delete_congruence_table(congruence_table_t *tbl);

/*
 * Reset: remove all composites
 */
extern void reset_congruence_table(congruence_table_t *tbl);


/*
 * Remove a composite c from tbl.
 * - c must be present in the table, otherwise the function loops
 * - c->hash must be equal to the hash of its signature
 */
extern void congruence_table_remove(congruence_table_t *tbl, composite_t *c);

/*
 * Remove c from tbl if it's present (no change otherwise)
 * - tbl must not be full
 * - c->hash must be equal to the hash of its signature
 * returned value:
 * - true if c was present (and has been removed)
 * - false if c was not present
 */
extern bool congruence_table_remove_if_present(congruence_table_t *tbl, composite_t *c);


/*
 * Add composite c to tbl
 * - c must not be present
 * - c->hash must be equal to the hash of its signature
 */
extern void congruence_table_add(congruence_table_t *tbl, composite_t *c);

/*
 * Search for a composite of signature s
 * - return NULL_COMPOSITE if there's none.
 */
extern composite_t *congruence_table_find(congruence_table_t *tbl, signature_t *s, elabel_t *label);


/*
 * Search for a composite congruent to (eq t1 t2)
 * - return NULL_COMPOSITE if there's none
 */
extern composite_t *congruence_table_find_eq(congruence_table_t *tbl, occ_t t1, occ_t t2, elabel_t *label);

/*
 * Search for a composite of signature s and return it
 * If there's none add c to the hash table and return c
 * - s must contain the signature of c
 * - side effect: c->hash is set to hash(s)
 */
extern composite_t *congruence_table_get(congruence_table_t *tbl, composite_t *c, signature_t *s, elabel_t *label);


/*
 * Check whether c is stored in the table (i.e., whether c is a congruence root)
 * - no side effect on c: c->hash is not changed
 */
extern bool congruence_table_is_root(congruence_table_t *tbl, composite_t *c, elabel_t *label);


#endif /* __COMPOSITES_H */
