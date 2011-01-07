/*
 * DATA STRUCTURES FOR THE BITVECTOR SOLVER
 */

/*
 * Version 2: pure bit-blasting/no subsolver. All bit-blasting
 * is done directly in the core.
 * 
 * For each variable x, we store
 * - bit_size[x] = number of bits in x
 * - kind[x] = tag that defines how the definition is to 
 *             be interpreted
 * - def[x] = definition of x 
 * - eterm[x] = attached egraph term (optional)
 * - map[x] = literal or array of literals (bit blasting)
 *
 * Bit vector atoms are of three kinds:
 * - bveq x y
 * - bvge x y: x <= y, where x and y are interpreted 
 *   as unsigned integers
 * - bvsge x y: x <= y, where x and y are as signed
 *   integers
 */

#ifndef __BVSOLVER_TYPES_H
#define __BVSOLVER_TYPES_H

#include <stdint.h>
#include <setjmp.h>

#include "int_hash_tables.h"
#include "arena.h"
#include "int_vectors.h"
#include "bvpoly_buffer.h"
#include "bvbound_cache.h"
#include "bit_blaster.h"
#include "cache.h"
#include "small_bvsets.h"
#include "rb_bvsets.h"
#include "egraph_assertion_queues.h"

#include "smt_core.h"
#include "egraph.h"
#include "context.h"




/********************
 *  VARIABLE TABLE  *
 *******************/

/*
 * Tags for kind[x]
 * - variables (no definition)
 * - constants (small/large bitvector constants)
 * - bit expressions
 * - array of bit expressions
 * - binary and unary operators (arithmetic + shift)
 */
typedef enum bvvar_tag {
  BVTAG_VAR,           // uninterpreted bitvector
  BVTAG_CONST64,       // constant represented as a 64bit unsigned integer
  BVTAG_CONST,         // constant represented as an array of 32bit words 
  BVTAG_POLY64,        // polynomial with small coefficients
  BVTAG_POLY,          // polynomial with large coefficients 
  BVTAG_PPROD,         // power product
  BVTAG_BIT_ARRAY,     // array of literals
  BVTAG_ITE,           // if-then-else (mux)
  BVTAG_UDIV,          // quotient in unsigned division
  BVTAG_UREM,          // remainder in unsigned division
  BVTAG_SDIV,          // quotient in signed division (rounding towards 0)
  BVTAG_SREM,          // remainder in signed division (rounding towards 0)
  BVTAG_SMOD,          // remainder in floor division (rounding towards -infinity)
  BVTAG_SHL,           // shift left
  BVTAG_LSHR,          // logical shift right
  BVTAG_ASHR,          // arithmetic shift right
} bvvar_tag_t;


/*
 * Descriptor for (if c then x else y)
 */
typedef struct bv_ite_s {
  literal_t cond;
  thvar_t left;
  thvar_t right;
} bv_ite_t;


/*
 * Descriptor (definition)
 */
typedef union bvvar_desc_u {
  uint64_t   cnst64;     // for const64
  uint32_t   *cnst;      // for big constants
  bvpoly64_t *poly64;    // poly with 64bit coefficients
  bvpoly_t   *poly;      // poly with large coefficients
  thvar_t    op[2];      // two variable operands
  bv_ite_t   *ite;       // if-then-else
} bvvar_desc_t;


/*
 * Variable table
 * - nvars = number of variables
 * - size = size of arrays bit_size, kind, def, map 
 *        = size of eterm if eterm isn't NULL
 * - kind[x] is used both to store the tag for x and to mark x
 *   marking is done by setting the high-order bit of kind[x] to 1
 * - the mark indicates whether or not bit-blasting has been done on x
 */
typedef struct bv_vartable_s {
  uint32_t nvars;
  uint32_t size;

  // definition, size, etc.
  uint32_t *bit_size;
  uint8_t *kind;
  bvvar_desc_t *def;
  eterm_t *eterm;

  // mapping to literals
  literal_t *map;

  // hash consing
  int_htbl_t htbl;
} bv_vartable_t;


#define DEF_BVVARTABLE_SIZE 100
#define MAX_BVVARTABLE_SIZE (UINT32_MAX/sizeof(bvvar_desc_t))


/*
 * Extract the tag out of kind[x]
 */
static inline bvvar_tag_t tag_of_kind(uint8_t k) {
  return (bvvar_tag_t) (k & ((uint8_t) 0x7F));
}

static inline bool kind_is_marked(uint8_t k) {
  return (k & ((uint8_t) 0x80)) != 0;
}




/*
 * ACCESS TO VARIABLE ATTRIBUTES
 */
static inline bool valid_bvvar(bv_vartable_t *table, thvar_t x) {
  return 0 <= x && x < table->nvars;
}

static inline bvvar_tag_t bvvar_tag(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  return tag_of_kind(table->kind[x]);
}

static inline bool bvvar_is_marked(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  return kind_is_marked(table->kind[x]);
}

static inline uint32_t bvvar_bitsize(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  return table->bit_size[x];
}

static inline bool bvvar_is_uninterpreted(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_VAR;
}

static inline bool bvvar_is_const64(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_CONST64;
}

static inline bool bvvar_is_const(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_CONST;
}

static inline bool bvvar_is_poly64(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_POLY64;
}

static inline bool bvvar_is_poly(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_POLY;
}

static inline bool bvvar_is_pprod(bv_vartbale_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_PPROD
}


/*
 * Check whether variable x is mapped to something
 */
static inline bool bvvar_is_mapped(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  return table->map[x] != NULL;
}


/*
 * Set/clear the mark on x
 */
static inline void bvvar_set_mark(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  table->kind[x] |= ((uint8_t) 0x80);
}

static inline void bvvar_clr_mark(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  table->kind[x] &= ((uint8_t) 0x7F);
}




/****************
 *  ATOM TABLE  *
 ***************/

/*
 * Tags for atom types
 * - each atom maps an external boolean variable (in the core)
 *   to a constraint on two variables x and y.
 * - there are three kinds of atoms: eq, ge, sge 
 */
typedef enum bvatm_tag {
  BVEQ_ATM,     // (x == y)
  BVUGE_ATM,    // (x >= y) unsigned
  BVSGE_ATM,    // (x >= y) signed
} bvatm_tag_t;


/*
 * Atom structure:
 * - the header encodes the tag + a mark
 * - lit is a literal in the core.
 *   if lit == true_literal, the atom is true at the toplevel
 *   if lit == false_literal, the atom is false at the toplevel
 *   otherwise the atom is attached to a boolean variable v 
 *   in the core and lit is pos_lit(v).
 * - left/right are x and y
 */
typedef struct bvatm_s {
  uint32_t header;
  literal_t lit;
  thvar_t left;
  thvar_t right;
} bvatm_t;



/*
 * Access to tag and mark
 * - the two low order bits of the header contain the tag
 * - the next bit is the mark
 */
static inline bvatm_tag_t bvatm_tag(bvatm_t *atm) {
  return (bvatm_tag_t) (atm->header & 0x3);
}

static inline bool bvatm_is_eq(bvatm_t *atm) {
  return bvatm_tag(atm) == BVEQ_ATM;
}

static inline bool bvatm_is_ge(bvatm_t *atm) {
  return bvatm_tag(atm) == BVUGE_ATM;
}

static inline bool bvatm_is_sge(bvatm_t *atm) {
  return bvatm_tag(atm) == BVSGE_ATM;
}

static inline bool bvatm_is_marked(bvatm_t *atm) {
  return (atm->header & 0x4) != 0;
}

static inline void bvatm_set_mark(bvatm_t *atm) {
  atm->header |= 0x4;
}


/*
 * Boolean variable of atm
 * - if lit == null_literal, return null_bvar
 */
static inline bvar_t bvatm_bvar(bvatm_t *atm) {
  return var_of(atm->lit);
}


/*
 * Conversions between void* pointers and atom indices
 * - an atom index is packed into a void * pointer, with a two-bit tag 
 *   to indicate that it's an bitvector atom (cf. egraph_base_types.h)
 * - there's no loss of data even if pointers are 32 bits (because
 *   the tag is 2bits and i is less than MAX_BVATOMTABLE_SIZE (i.e., 2^32/16)
 */
static inline void *bvatom_idx2tagged_ptr(int32_t i) {
  return tagged_bv_atom((void *)((size_t) (i << 2)));
}

static inline int32_t bvatom_tagged_ptr2idx(void *p) {
  return (int32_t)(((size_t) p) >> 2);
}




/*
 * Table
 */
typedef struct bv_atomtable_s {
  uint32_t natoms;
  uint32_t size;
  bvatm_t *data;

  int_htbl_t htbl;  // for hash consing
} bv_atomtable_t;


#define DEF_BVATOMTABLE_SIZE 100
#define MAX_BVATOMTABLE_SIZE (UINT32_MAX/sizeof(bv_atom_t))







/********************
 *  PUSH/POP STACK  *
 *******************/

/*
 * For every push: keep track of the number of variables and atoms
 * on entry to the new base level
 */
typedef struct bv_trail_s {
  uint32_t nvars;
  uint32_t natoms;
} bv_trail_t;

typedef struct bv_trail_stack_s {
  uint32_t size;
  uint32_t top;
  bv_trail_t *data;
} bv_trail_stack_t;

#define DEF_BV_TRAIL_SIZE 20
#define MAX_BV_TRAIL_SIZE (UINT32_MAX/sizeof(bv_trail_t))





/***********************
 *  LEMMAS/CACHE TAG   *
 **********************/

/*
 * Experiment: simpler approach to deal with equality and
 * disequalities from the egraph.
 *
 * We can force the egraph and bv_solver to agree by
 * generating lemmas of the form (eq t1 t2) <=> (bveq x1 x2),
 * where t1 and t2 are egraph terms
 *   and x1 and x2 are the corresponding bit-vector variables.
 *
 * To avoid generating several times the same lemma, we keep
 * the pair (x1, x2) in a cache, with the tag BVEQUIV_LEMMA.
 *
 * Other tags:
 * in egraph_types.h: 
 *   DISTINCT_LEMMA = 0
 *   ACKERMANN_LEMMA = 1
 * in simplex_types.h
 *   TRICHOTOMY_LEMMA = 2
 */
typedef enum bv_lemma_tag {
  BVEQUIV_LEMMA = 3,
} bv_lemma_tag_t;

typedef enum bv_lemma_flag {
  ACTIVE_BV_LEMMA = 1, // anything non-zero will do
} bv_lemma_flag_t;



/***********************
 * SETS OF USED VALUES *
 **********************/

/*
 * When building models, the egraph may need fresh bitvector values.
 * A value is fresh if it's distinct from the values assigned to all
 * the bitvector variables.
 * 
 * To generate fresh values of type (bitvector k), we build the set of
 * used values of that type and search for something not in the set.
 * Depending on k, we use different data structures to store the set:
 * - k <= SMALL_BVSET_LIMIT: use small_bvset_t
 * - k > SMALL_BVSET_LIMIT: use red-black trees
 *
 * The used_bvval structure store pairs <bitsize k, set>
 */

// ptr is either a pointer to a small_bvset_t or to a rb_bvset_t
// depending on bitsize
typedef struct bvset_s {
  uint32_t bitsize;
  void *ptr;
} bvset_t;

typedef struct used_bvval_s {
  bvset_t *data;
  uint32_t nsets;
  uint32_t size;
} used_bvval_t;

#define SMALL_BVSET_LIMIT 13

#define USED_BVVAL_DEF_SIZE 8
#define USED_BVVAL_MAX_SIZE (UINT32_MAX/sizeof(bvset_t))




/************
 *  SOLVER  * 
 ***********/

typedef struct bv_solver_s {
  /*
   * Attached smt core + egraph
   */
  smt_core_t *core;
  egraph_t *egraph;

  /*
   * Base level and decision level
   */
  uint32_t base_level;
  uint32_t decision_level;

  /*
   * Variable + atom tables
   */
  bv_vartable_t vtbl;
  bv_atomtable_t atbl;

  /*
   * Cache for bounds on variables: allocated on demand
   */
  bvbound_cache_t *bounds;

  /*
   * Optional cache for lemmas: allocated on demand
   */
  cache_t *cache;

  /*
   * Data structures for bit-blasting
   * - the flag bit_blasted is true after all constraints 
   *   and atoms are translated to clauses in the core
   * - blaster + remap table are allocated  
   *   during bit blasting
   */
  bit_blaster_t *blaster;
  remap_table_t *remap;
  bool bit_blasted;

  /*
   * Queue of egraph assertions
   */
  eassertion_queue_t egraph_queue;
  
  /*
   * Push/pop stack
   */
  bv_trail_stack_t trail_stack;

  /*
   * Auxiliary buffers for internalization
   */
  bvpoly_buffer_t buffer;
  vpbuffer_t prod_buffer;
  ivector_t aux_vector;
  bvconstant_t aux1;
  bvconstant_t aux2;
  // buffers for bit-blasting
  ivector_t a_vector;
  ivector_t b_vector;


  /*
   * Sets for generating fresh values
   */
  used_bvval_t used_vals;

  /*
   * Jump buffer for exception handling during internalization
   */
  jmp_buf *env;

} bv_solver_t;



#endif /* __BVSOLVER_TYPES_H */
