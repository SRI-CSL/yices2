/*
 * Low-level objects in egraph
 * (We need to separate these typedefs from the full egraph_types.h
 *  to break circular dependencies between include files).
 */

#ifndef __EGRAPH_BASE_TYPES_H
#define __EGRAPH_BASE_TYPES_H

#include "smt_core_base_types.h"


/***************************
 *  TERMS AND OCCURRENCES  *
 **************************/

typedef int32_t eterm_t;
typedef int32_t occ_t;

/*
 * Maximal number of egraph terms
 * - no more than 2^30 terms
 * - we also want to compute (nterms * sizeof(void *)) without overflow
 * The following limit is safe (but not optimal).
 */
#define MAX_ETERMS (INT32_MAX>>3)

/*
 * Conversion between terms and occurrences:
 * - polarity bit is the low-order bit of a occurrence:
 * 0 means positive, 1 means negative
 */
static inline occ_t pos_occ(eterm_t t) {
  return (t << 1);
}

static inline occ_t neg_occ(eterm_t t) {
  return (t << 1) | 1;
}

// polarity 0 --> pos_occ(t), polarity 1 --> neg_occ(t)
static inline occ_t mk_occ(eterm_t t, uint32_t polarity) {
  assert((polarity & ~1) == 0);
  return (t << 1) | polarity;
}

static inline eterm_t term_of_occ(occ_t x) {
  return x>>1;
}

static inline uint32_t polarity_of_occ(occ_t x) {
  return ((uint32_t) x) & 1;
}

static inline bool is_pos_occ(occ_t x) {
  return polarity_of_occ(x) == 0;
}

static inline bool is_neg_occ(occ_t x) {
  return polarity_of_occ(x) != 0;
}

// complement of x = same term, opposite polarity
static inline eterm_t opposite_occ(occ_t x) {
  return x ^ 1;
}

/*
 * Predefined term and occurrence ids
 */
enum {
  null_eterm = -1,
  true_eterm = 0,

  null_occurrence = -1,
  true_occ = 0,  // pos_occ(true_eterm)
  false_occ = 1, // neg_occ(true_eterm)
};


/*
 * Occurrence code for a boolean x
 */
static inline occ_t bool2occ(bool x) {
  assert(x == 0 || x == 1);
  return x ^ 1;
}


/*
 * Theory variables are integer too. null_thvar means no variable attached
 */
typedef int32_t thvar_t;

enum {
  null_thvar = -1,
};




/*****************
 *   ATOM TAGS   *
 ****************/

/*
 * The egraph may need to propagate atoms to the arithmetic or bitvector solvers.
 * We mark these atoms using a tag in the two lower order bits of atom pointers.
 */
typedef enum atm_tag {
  EGRAPH_ATM_TAG = 0,
  ARITH_ATM_TAG  = 1,
  BV_ATM_TAG     = 2,
} atm_tag_t;

#define ATM_TAG_MASK ((size_t) 0x3)

/*
 * Get the tag of atm
 */
static inline atm_tag_t atom_tag(void *atm) {
  return ((size_t) atm) & ATM_TAG_MASK;
}

/*
 * Remove the tag of atm
 */
static inline void *untag_atom(void *atm) {
  return (void *) (((size_t) atm) & ~ATM_TAG_MASK);
}

/*
 * Attach a tag to a an atom pointer
 */
static inline void *tagged_egraph_atom(void *atm) {
  assert((((size_t) atm) & ATM_TAG_MASK) == 0);
  return (void *)(((size_t) atm) | EGRAPH_ATM_TAG);
}

static inline void *tagged_arith_atom(void *atm) {
  assert((((size_t) atm) & ATM_TAG_MASK) == 0);
  return (void *)(((size_t) atm) | ARITH_ATM_TAG);
}

static inline void *tagged_bv_atom(void *atm) {
  assert((((size_t) atm) & ATM_TAG_MASK) == 0);
  return (void *)(((size_t) atm) | BV_ATM_TAG);
}



#endif /* EGRAPH_BASE_TYPES */
