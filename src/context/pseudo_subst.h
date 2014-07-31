/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CANDIDATE TERM SUBSTITUTION.
 */

/*
 * If variable elimination is enabled, the context attempts to
 * eliminate variable X in equalities of the form (X == term).
 *
 * On large benchmarks, it's too expensive to check every time whether
 * X occurs in term. Instead, variable elimination is done in three
 * phases:
 *
 * 1) do the cheap substitutions: (X == Y) or (X == constant)
 *    record all other possible substitutions (X == term) into
 *    a subst_eq vector.
 *
 * 2) process the subst_eq vector: if equality (X == term) in that
 *    vector is still a possible substitution (i.e., X is still free)
 *    then record the substitution [X := term] as a candidate.
 *
 * 3) apply a global cycle detection algorithm and remove all
 *    candidate substitutions that cause cycles.
 *
 * The data structures defined here are used to record the candidate
 * substitutions.
 */

#ifndef __PSEUDO_SUBST_H
#define __PSEUDO_SUBST_H

#include <stdbool.h>
#include <stdint.h>

#include "terms/terms.h"


/*
 * Substitution triple:
 * - a top-level equality is a Boolean term e that's equivalent to
 *   an equality (t1 == t2). It's a candidate substitution if
 *   one of t1 or t2 is a variable X (UNINTERPRETED_TERM).
 * - each triple below stores (X == t) + the equality term e.
 */
typedef struct subst_triple_s {
  term_t var;   // X
  term_t map;   // t
  term_t eq;    // equality term
} subst_triple_t;


/*
 * Bank for triple allocation:
 * - list of blocks
 * - each block contains ST_BANK_SIZE triples
 * We want to be able so scan the all set of triples in
 * chronological order.
 */
#define ST_BANK_SIZE 650

typedef struct st_block_s {
  struct st_block_s *next;
  subst_triple_t data[ST_BANK_SIZE];
} st_block_t;

typedef struct st_bank_s {
  st_block_t *tail;  // last block (or NULL)
  st_block_t *head;  // first block (or NULL)
  uint32_t free_idx; // index of the first free block in tail
                     // (ST_BANK_SIZE if the last block is full or NULL)
} st_bank_t;



/*
 * Pseudo substitution:
 * - a hash table that maps a variable X to the
 *   triple s such that s->var == X
 * - a bank for allocating triples
 */
typedef struct pseudo_subst_s {
  subst_triple_t **data;
  uint32_t size;   // must be a power of 2
  uint32_t nelems;
  uint32_t resize_threshold;

  st_bank_t bank;
} pseudo_subst_t;


// Default and maximal size + resize ratio
#define PSEUDO_SUBST_DEF_SIZE 256
#define PSEUDO_SUBST_MAX_SIZE (UINT32_MAX/sizeof(subst_triple_t *))

#define PSEUDO_SUBST_RESIZE_RATIO 0.7




/*
 * INITIALIZATION/DELETION
 */

/*
 * Initialize subst:
 * - n = initial size of the hash table
 *   if n =0, the default size is used
 * - the bank is empty.
 */
extern void init_pseudo_subst(pseudo_subst_t *subst, uint32_t n);


/*
 * Delete everything
 */
extern void delete_pseudo_subst(pseudo_subst_t *subst);


/*
 * Reset: empty the table
 */
extern void reset_pseudo_subst(pseudo_subst_t *subst);




/*
 * SEARCH AND ADDITION
 */

/*
 * Find the triple of variable equal to x in subst
 * - return NULL if there's no such triple
 */
extern subst_triple_t *pseudo_subst_find(pseudo_subst_t *subst, term_t x);


/*
 * Search for a triple with variable x in subst. If such a triple
 * is found, return it. Otherwise create a fresh record, add it
 * to the table, and return it.
 * - the fresh record is initialized with var = x, map = NULL_TERM,
 *   and eq = NULL_TERM.
 */
extern subst_triple_t *pseudo_subst_get(pseudo_subst_t *subst, term_t x);


/*
 * Return the term mapped to x by the pseudo substitution
 * - return x itself it x is not in the hash table
 */
static inline term_t pseudo_subst_of_var(pseudo_subst_t *subst, term_t x) {
  subst_triple_t *s;

  s = pseudo_subst_find(subst, x);
  return (s == NULL) ? x : s->map;
}


/*
 * Check whether x is mapped to anything
 */
static inline bool pseudo_subst_var_is_mapped(pseudo_subst_t *subst, term_t x) {
  return pseudo_subst_find(subst, x) != NULL;
}



/*
 * ITERATOR
 */

/*
 * Apply function f(aux, s) to all substitution triples s in subst
 * - aux is an arbitrary pointer provided by the caller
 * - f must not have side effects on subst
 */
typedef void (*pseudo_subst_iterator_t)(void *aux, subst_triple_t *s);

extern void pseudo_subst_iterate(pseudo_subst_t *subst, void *aux, pseudo_subst_iterator_t f);



#endif /* __PSEUDO_SUBST_H */
