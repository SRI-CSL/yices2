/*
 * DATA STRUCTURES FOR THE BITVECTOR SOLVER
 */

/*
 * Version 2: pure bit-blasting/no subsolver. All bit-blasting
 * is done directly in the core.
 * 
 * The solver stores a set of bit-vector and bit variables.
 * A bit-variable is a boolean.
 *
 * For each variable x, we store
 * - bit_size[x] = number of bits in x
 * - kind[x] = tag that defines how the definition is to 
 *             be interpreted
 * - def[x] = definition of x 
 * - eterm[x] = attached egraph term (optional)
 * - map[x] = literal or array of literals (bit blasting)
 *
 * We also store boolean objects (bits) in the table
 * (same representation as in bit_expr.h)
 * - x is a boolean if bit_size[x] = 0
 */

#ifndef __BVSOLVER_TYPES_H
#define __BVSOLVER_TYPES_H

#include <stdint.h>
#include <setjmp.h>

#include "int_hash_tables.h"
#include "int_queues.h"
#include "arena.h"
#include "int_vectors.h"
#include "bv_constants.h"
#include "bvpoly_buffer.h"
#include "internalization_map.h"
#include "remap_table.h"
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
  BVTAG_SMALL_CONST,   // constant represented as a 64bit unsigned integer
  BVTAG_BIG_CONST,     // constant represented as an array of 32bit words 
  BVTAG_TRUE,          // boolean constant
  BVTAG_SELECT,        // (bit i x) = bit i of variable x
  BVTAG_XOR,           // (xor x y): x and y are variable indices with polarity
  BVTAG_OR,            // (or x y): same thing
  BVTAG_BIT,           // [x]: where x is a bit variable + polarity
  BVTAG_BIT_ARRAY,     // [x_0, ..., x_{n-1}]: x_i is a variable + polarity
  BVTAG_ADD,
  BVTAG_SUB,
  BVTAG_NEG,
  BVTAG_MUL,
  BVTAG_UDIV,
  BVTAG_UREM,
  BVTAG_SDIV,
  BVTAG_SREM,
  BVTAG_SMOD,
  BVTAG_SHL,           // shift left
  BVTAG_LSHR,          // logical shift right
  BVTAG_ASHR,          // arithmetic shift right
  BVTAG_ITE,           // if-then-else (mux)
} bvvar_tag_t;



/*
 * Descriptor for (bit i x)
 */
typedef struct bv_select_s {
  uint32_t idx;   // i
  thvar_t var;    // x
} bv_select_t;

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
  uint64_t ival;     // for small const
  bv_select_t sel;   // bit i of x
  thvar_t op[2];     // two variable operands
  bit_t bop[2];      // two bit operands (for OR/XOR)
  bit_t bval;        // array of 1 bit
  uint32_t *pval;    // for big const = array of N words where N = ceil(nbits/32)
  bit_t *bit;        // array of n bits
  bv_ite_t *ite;     // if-then-else
} bvvar_desc_t;


/*
 * Conversion after bit-blasting:
 * - bitvector variables are mapped to arrays of literals in bit_solver.
 * - bit variables are mapped to literals in bit_solver.
 *
 * To store the mapping, we use a union type
 * - for a bivector variable of size > 1, map.array is an array of literals
 * - for a bitector variable of size 1 or a bit variable, map.lit is a single 
 *   literal.
 */
typedef union bvvar_map_u {
  literal_t *array;
  literal_t lit;
} bvvar_map_t;


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
  bvvar_map_t *map;

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
 * Bits are represented as in bit_expr.h
 * - format = [0|var id|sign_bit]
 * - sign bit = 0 means positive polarity
 * - sign bit = 1 means negative polarity
 */
static inline thvar_t var_of_bit(bit_t x) {
  return (x>>1);
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

static inline bool bvvar_is_small_const(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_SMALL_CONST;
}

static inline bool bvvar_is_big_const(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_BIG_CONST;
}

static inline bool bvvar_is_uninterpreted(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_VAR;
}

static inline uint64_t small_const_value(bv_vartable_t *table, thvar_t x) {
  assert(bvvar_is_small_const(table, x));
  return table->def[x].ival;
}

static inline uint32_t *big_const_value(bv_vartable_t *table, thvar_t x) {
  assert(bvvar_is_big_const(table, x));
  return table->def[x].pval;
}

static inline bool valid_bitvar(bv_vartable_t *table, thvar_t x) {
  return valid_bvvar(table, x) && bvvar_bitsize(table, x) == 0;
}

static inline bool valid_bit(bv_vartable_t *table, bit_t x) {
  return valid_bitvar(table, var_of_bit(x));
}


/*
 * Check whether variable x is mapped to something
 */
static inline bool bvvar_is_mapped(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  if (table->bit_size[x] <= 1) {
    return table->map[x].lit != null_literal;
  } else {
    return table->map[x].array != NULL;
  }
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




/***************
 *  PARTITION  *
 **************/

/*
 * The partition is a union-find data structure that encodes the 
 * top-level equalities. This is similar to the union-find structure used
 * in context.c, except that we don't keep type[x].
 *
 * Each index in the table is a variable x (defined in the bv_vartable)
 * - parent[x] is -1 if x is not in the table
 * - parent[x] = term equal of x 
 * Parent[x] is a bitvector variable y of same size as x, such that (x == y) 
 * was asserted as an axiom. Variable x is a root iff parent[x] == x.
 *
 * To balance the partitions, we use an 8bit rank, meaningful only if x is a
 * root. Rank[x] is close to the log of the size of its class. 
 * A variable x can be marked so that it always stays root of its class. This is 
 * done by setting rank[x] == 255.
 *
 * For push/pop, we keep track of the merge operations in a trail stack.
 * We don't use path compression so that it's easy to undo a merge.
 * Each element in the trail stack consists of a variable y + a bit.
 *
 * When the classes of x and y are merged and x is chosen as root of the 
 * of the combined class, then 
 *  - parent[y] is set to x
 *  - rank[x] remains unchanged or is incremented
 * We store y in the trail stack and save 1 bit to remenber whether
 * rank[x] was incremented or not.
 * When y is added initially, it's the unique element of its class
 * so parent[y] is set to y. We also push y on the trail stack at that 
 * point (with bit 0).
 */

/*
 * Trailer stack for push/pop
 * - the stack is in data[0... top-1]. It's organized in frames.
 * - size = size of the full data array
 * - top = top of the stack
 * - top_frame = start of the top frame
 *   if top_frame = k then the top frame is data[k+1, ..., top-1]
 *   and data[k] = index of the previous frame
 */
typedef struct bv_ptrail_s {
  uint32_t size;
  uint32_t top;
  int32_t top_frame;
  int32_t *data;
} bv_ptrail_t;

#define DEF_BVTRAIL_SIZE 100
#define MAX_BVTRAIL_SIZE (UINT32_MAX/sizeof(int32_t))

/*
 * Partition table:
 * - size = size of arrays parent and rank
 * - nelems = 1 + the largest x present in the table
 * - level = base level = number of calls to push
 * - trail = trail stack
 * - if level is 0, the trail stack is not used
 */
typedef struct bv_partition_s {
  uint32_t nelems;
  uint32_t size;
  int32_t *parent;
  uint8_t *rank;
  uint32_t level;
  bv_ptrail_t trail;
} bv_partition_t;


#define DEF_BVPARTITION_SIZE 100
#define MAX_BVPARTITION_SIZE (UINT32_MAX/sizeof(int32_t))




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








/***********************
 *  PROPAGATION QUEUE  *
 **********************/

/*
 * We can do boolean propagation before bit blasting. Boolean
 * propagation can be triggered by the top-level equalities.  For
 * example, if x is (bitarray b0 ... bn) and y is a constant, then,
 * after the top-level equality (x == y) is asserted, we can assign a
 * truth-value to the bits b0 ... bn. By propagating further from
 * there, we can discover that some atoms are true/false.
 *
 * To implement Boolean propagation we use a propagation queue (queue
 * of integers) + an array that stores the truth value of bit variables.
 *
 * TODO: clean this up. We should be able to use the literal mapping in
 * the variable table rather than an additional truth assignment here.
 */
typedef struct bv_prop_queue_s {
  uint32_t nvars;    // value is defined for x such that 0 <= x < nvars
  uint32_t size;     // size = size of the array value
  bool unsat;        // flag true if a conflict is discovered by propagation
  uint8_t *value;  
  int_queue_t queue; // store bit-variables to process  
} bv_prop_queue_t;


#define DEF_BV_PROPQUEUE_SIZE 100
#define MAX_BV_PROPQUEUE_SIZE (UINT32_MAX/sizeof(uint8_t))





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
   * - pointer to the bitvector manager for all input 
   *   bvarith/bvlogic expr
   * - pointer to the node_table used by the bvlogic expressions
   * - node_map: used as a cache when internalizing bvlogic expression
   *   keeps a mapping from external node ids (in table nodes) to internal
   *   bits (in vtbl).
   * - partition table for top-level equalities
   */
  bv_var_manager_t *bv_manager;
  node_table_t *nodes;
  bv_vartable_t vtbl;
  bv_atomtable_t atbl;
  itable_t node_map;
  bv_partition_t partition;

  /*
   * Cache for bounds on variables: allocated on demand
   */
  bvbound_cache_t *bounds;

  /*
   * Propagation queue: allocated on demand
   */
  bv_prop_queue_t *queue;

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
