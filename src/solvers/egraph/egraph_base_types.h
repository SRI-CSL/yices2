/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Low-level objects in egraph
 * (We need to separate these typedefs from the full egraph_types.h
 *  to break circular dependencies between include files).
 */

#ifndef __EGRAPH_BASE_TYPES_H
#define __EGRAPH_BASE_TYPES_H

#include "solvers/cdcl/smt_core_base_types.h"


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



/*************
 *  CLASSES  *
 ************/

/*
 * Class ids and labels are signed integers
 * A label is a class id + a polarity bit
 */
typedef int32_t class_t;
typedef int32_t elabel_t;

static inline elabel_t pos_label(class_t i) {
  return (i << 1);
}

static inline elabel_t neg_label(class_t i) {
  return (i << 1) | 1;
}

static inline class_t class_of(elabel_t l) {
  return l >> 1;
}

static inline uint32_t sign_of(elabel_t l) {
  return ((uint32_t) l) & 1;
}

static inline bool is_pos_label(elabel_t l) {
  return sign_of(l) == 0;
}

static inline bool is_neg_label(elabel_t l) {
  return sign_of(l) != 0;
}

static inline elabel_t opposite_label(elabel_t l) {
  return l ^ 1;
}

/*
 * Predefined class and labels
 */
enum {
  null_class = -1,
  null_label = -1,

  bool_constant_class = 0,

  true_label = 0,   // pos_label(0)
  false_label = 1,  // neg_label(0)
};



/****************
 *  COMPOSITES  *
 ***************/

/*
 * Different types of composite terms
 *
 * TODO? Possible optimization: we could use a special tag for
 * equality between boolean terms.
 */
typedef enum composite_kind {
  COMPOSITE_APPLY,
  COMPOSITE_UPDATE,
  COMPOSITE_TUPLE,
  COMPOSITE_EQ,
  COMPOSITE_ITE,
  COMPOSITE_DISTINCT,
  COMPOSITE_OR,
  COMPOSITE_LAMBDA,
} composite_kind_t;


/*
 * Composite structures:
 * - tag = arity + kind
 * - hash = 32bit hash code used for congruence closure
 * - id = term t: c->id = t iff body[t] = c
 * - array of children
 *
 * For a composite of arity n, child has n elements to store the children
 * and (optionally) n more elements (hooks).
 * - the children ids (occ_t) are in cmp->child[0 ... n-1]
 * - the hooks are in cmp->child[n ... 2n-1]
 * - the hooks are indices into use vectors:
 *   if cmp is stored in parents[c] at some index k, i.e., we have
 *      cmp->child[i] = t   label[t] = c  parents[c]->data[k] = cmp
 *   then k is stored in cmp->child[i + n]
 * - if cmp has several children in class c the hook is set on
 *   the first child of class c. The other hooks are negative.
 * - this makes it easy and cheap to remove cmp from its parents
 *
 * A lambda composite cmp is of the form (lambda t) where t is a term
 * occurrence
 * - cmp has arity one but the array child has three elements:
 *   cmp->child[0] = t
 *   cmp->child[1] = hook as above
 *   cmp->child[2] = an integer tag (intended to encode the domain of the lambda term)
 */
typedef struct composite_s {
  uint32_t tag;
  uint32_t hash;
  eterm_t id;
  int32_t child[0]; // real size depends on arity
} composite_t;

/*
 * Special indices for child[i + n]
 */
enum {
  no_ptr = -1,    // means not in a use vector
  duplicate_ptr = -2, // means another child has the same class
};

/*
 * 32 bit tags:
 * 3 low-order bits encode the type,
 * 29 high-order bits encode the arity.
 */
#define CTAG_BITS 3
#define CTAG_MASK ((((uint32_t) 1) << CTAG_BITS) - 1)
#define CTAG_ARITYMASK (~CTAG_MASK)

/*
 * Arity must fit in 29 bits. We also need to ensure
 * (sizeof(composite_t) + 2.n * sizeof(int32_t)) does not overflow
 */
#define MAX_COMPOSITE_ARITY ((UINT32_MAX>>CTAG_BITS)-sizeof(composite_t))


/*
 * Tag constructors:
 * - for variable arity terms, n = number of children
 * - n == 0 is allowed
 */
static inline uint32_t mk_composite_tag(composite_kind_t k, uint32_t n) {
  assert(n <= MAX_COMPOSITE_ARITY);
  return (n << CTAG_BITS) | k;
}

static inline uint32_t mk_apply_tag(uint32_t n) {
  return mk_composite_tag(COMPOSITE_APPLY, n);
}

static inline uint32_t mk_update_tag(uint32_t n) {
  return mk_composite_tag(COMPOSITE_UPDATE, n);
}

static inline uint32_t mk_tuple_tag(uint32_t n) {
  return mk_composite_tag(COMPOSITE_TUPLE, n);
}

static inline uint32_t mk_eq_tag(void) {
  return mk_composite_tag(COMPOSITE_EQ, 2);
}

static inline uint32_t mk_lambda_tag(void) {
  return mk_composite_tag(COMPOSITE_LAMBDA, 1);
}

static inline uint32_t mk_distinct_tag(uint32_t n) {
  return mk_composite_tag(COMPOSITE_DISTINCT, n);
}

static inline uint32_t mk_ite_tag(void) {
  return mk_composite_tag(COMPOSITE_ITE, 3);
}

static inline uint32_t mk_or_tag(uint32_t n) {
  return mk_composite_tag(COMPOSITE_OR, n);
}


/*
 * Extract kind and arity from a tag
 */
static inline composite_kind_t tag_kind(uint32_t tag) {
  return (composite_kind_t) (tag & CTAG_MASK);
}

static inline uint32_t tag_arity(uint32_t tag) {
  return (uint32_t) (tag >> CTAG_BITS);
}


/*
 * Extract components of a composite
 */
static inline composite_kind_t composite_kind(composite_t *c) {
  return tag_kind(c->tag);
}

static inline uint32_t composite_arity(composite_t *c) {
  return tag_arity(c->tag);
}

static inline occ_t composite_child(composite_t *c, uint32_t i) {
  assert(i < composite_arity(c));
  return c->child[i];
}

static inline int32_t *composite_hooks(composite_t *c) {
  return c->child + composite_arity(c);
}

static inline int32_t lambda_composite_tag(composite_t *c) {
  assert(composite_kind(c) == COMPOSITE_LAMBDA);
  return c->child[2];
}


/*
 * Fake pointers (body of constants and variables)
 * - low-order bit is 1
 * - for a constant, we pack an integer id + 2 bit tag into the pointer
 */
#define VARIABLE_BODY ((composite_t *)1)
#define CONSTANT_TAG ((size_t) 3)

static inline composite_t *mk_constant_body(int32_t i) {
  return (composite_t *) ((((size_t) i) << 2) | CONSTANT_TAG);
}

static inline bool atomic_body(composite_t *c) {
  return (((size_t) c) & 0x1) != 0;
}

static inline bool composite_body(composite_t *c) {
  return ! atomic_body(c);
}

static inline bool constant_body(composite_t *c) {
  return (((size_t) c) & 0x3) == CONSTANT_TAG;
}

static inline int32_t constant_body_id(composite_t *c) {
  assert(constant_body(c));
  return (int32_t) (((size_t) c) >> 2);
}






/***********
 *  ATOMS  *
 **********/

/*
 * An egraph atom is a pair <t, v>, where t is a boolean term in the egraph
 * and v is the corresponding boolean variable in the core
 * - the atom <t, v> is attached to variable v in the core
 * - asserting v causes (t == true) to be pushed into the egraph queue;
 *   asserting (not v) causes (t == false) to be pushed into the queue.
 * - the egraph can detect that atoms are equal, by congruence. To deal
 *   with this, we store the atoms into equivalence classes (via a circular
 *   linked list). If <t1, v1> and <t2, v2> are in the same class then
 *   either t1 == t2 or t1 == (not t2).
 */
typedef struct atom_s atom_t;

struct atom_s {
  eterm_t eterm;   // egraph term
  bvar_t boolvar;  // core variable
  atom_t *next;    // successor in the class
};


/*
 * Atom objects are allocated via an object store
 * ATOM_BANK_SIZE is the number of atoms per object-store bank
 */
#define ATOM_BANK_SIZE 256





/******************
 *  EGRAPH TYPES  *
 *****************/

/*
 * Bool and tuple are interpreted internally by the egraph
 * The other types are used for propagating equalities and disequalities
 * to theory solvers. They identify the theory solver to contact:
 * - int/real: arithmetic solver
 * - bv: bitvector solver
 * - others: specific subsolver (for now, the only known solver is the
 *   function theory solver).
 */
typedef enum etype_s {
  // etypes with satellite solvers
  ETYPE_INT,      // 0
  ETYPE_REAL,     // 1
  ETYPE_BV,       // 2
  ETYPE_FUNCTION, // 3

  // etypes internal to the egraph
  ETYPE_BOOL,     // 4
  ETYPE_TUPLE,    // 5
  ETYPE_NONE,     // 6

} etype_t;

#define NUM_ETYPES     (ETYPE_NONE + 1)
#define NUM_SATELLITES (ETYPE_FUNCTION + 1)

/*
 * tau is an arithmetic type if tau == 0 or 1
 */
static inline bool is_arith_etype(etype_t tau) {
  assert(ETYPE_INT <= tau && tau <= ETYPE_NONE);
  return tau <= 1;
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
