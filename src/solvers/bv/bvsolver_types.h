/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * DATA STRUCTURES FOR THE BITVECTOR SOLVER
 */

/*
 * Version 2: pure bit-blasting/no subsolver. All bit-blasting
 * is done directly in the core.
 *
 * For each variable x, we store
 * - bit_size[x] = number of bits in x
 * - kind[x] = tag so that we know how to interpret def[x]
 * - def[x] = definition of x
 * - eterm[x] = attached egraph term (optional)
 * - map[x] = array of literals (bit blasting)
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

#include "utils/int_vectors.h"
#include "terms/bvpoly_buffers.h"
#include "terms/power_products.h"
#include "solvers/bv/remap_table.h"
#include "solvers/bv/bit_blaster.h"
#include "solvers/bv/merge_table.h"
#include "solvers/egraph/egraph_assertion_queues.h"
#include "utils/cache.h"

#include "solvers/bv/bv_vartable.h"
#include "solvers/bv/bv_atomtable.h"
#include "solvers/bv/bv_intervals.h"
#include "solvers/bv/bvconst_hmap.h"
#include "solvers/bv/bvexp_table.h"
#include "solvers/bv/bvpoly_compiler.h"

#include "solvers/cdcl/smt_core.h"
#include "solvers/egraph/egraph.h"
#include "context/context.h"





/*****************
 *  BOUND QUEUE  *
 ****************/

/*
 * A bound on a variable 'x' is an atom (x >= a) where a is a constant,
 * and the atom is either true or false at the top-level.
 * - the bounds on x are stored in a queue
 * - each element in the queue is an atom index
 * - the start of the list is stored in queue->bounds[x]
 * - we also store disequalities (x != 0) in the list
 */

/*
 * Bound descriptor: atom index + index of the predecessor
 * element in the queue pointer
 */
typedef struct bv_bound_s {
  int32_t atom_id;
  int32_t pre;
} bv_bound_t;


/*
 * Queue:
 * - data = array of bound descriptors
 * - top = index in data = number of elements in the queue
 * - size = total size of the array
 * To store the lists:
 * - bound = array of indices
 * - bsize = size of this array
 * For a variable 0 <= x < vtbl->nvars
 * - if x < bsize then bound[x] = index of the last
 *   bound asserted on x.
 *   If bound[x] = k then data[k].atom_id is the bound
 *   and data[k].pre = previous bound on x.
 *   The list is terminated by -1.
 * - if x >= bsize then there's no bound on x
 */
typedef struct bv_bound_queue_s {
  bv_bound_t *data;
  int32_t *bound;
  uint32_t top;
  uint32_t size;
  uint32_t bsize;
} bv_bound_queue_t;


#define DEF_BV_BOUND_QUEUE_SIZE 50
#define MAX_BV_BOUND_QUEUE_SIZE (UINT32_MAX/sizeof(bv_bound_t))

#define DEF_BV_BOUND_NUM_LISTS 100
#define MAX_BV_BOUND_NUM_LISTS (UINT32_MAX/sizeof(int32_t))




/***********************************
 *  INTERVAL COMPUTATION BUFFERS   *
 **********************************/

/*
 * For computing enclosing intervals on a bitvector expression,
 * we may need a stack of bv_intervals and a bv_aux_buffer structure.
 * These are stored in the following structure.
 *
 * Initially, this is set to:
 * - data = NULL
 * - buffers = NULL
 * - size = 0
 *
 * When the first interval is requested the stack and aux_buffers
 * are allocated.
 */
typedef struct bv_interval_stack_s {
  bv_interval_t *data;
  bv_aux_buffers_t *buffers;
  uint32_t size;
  uint32_t top;
} bv_interval_stack_t;


#define DEF_BV_INTV_STACK_SIZE 6
#define MAX_BV_INTV_STACK_SIZE (UINT32_MAX/sizeof(bv_interval_t))




/*********************
 *  VARIABLE QUEUES  *
 ********************/

/*
 * To handle push/pop and delayed bitblasting, we keep track
 * of variables that require special processing on pop.
 *
 * One queue stores the variables x for which the context
 * called bv_solver_select_bit or bv_solver_set_bit, and
 * that are not bit-vector constants or bit-arrays.
 * For such an x,  a literal l = (select x i) was
 * returned to the context, so 'x' must be considered
 * a top-level variable when bit-blasting. Also, this
 * means that x has a pseudo map attached, and this pseudo
 * map must be preserved by bv_solver_pop.
 *
 * Another queue stores the variables 'x' that were created at some level
 * k but were bit-blasted at a later stage (at level k' > k).
 * When we backtrack from level k', we must cleanup the array of literals
 * attached to x in the variable table, unless 'x' is also in the
 * select queue for this level.
 */
typedef struct bv_queue_s {
  thvar_t *data;
  uint32_t size;
  uint32_t top;
} bv_queue_t;


#define DEF_BV_QUEUE_SIZE 100
#define MAX_BV_QUEUE_SIZE (UINT32_MAX/sizeof(thvar_t))



/********************
 *  PUSH/POP STACK  *
 *******************/

/*
 * For every push, we keep track of the number of variables and atoms
 * on entry to the new base level, the size of the bound queue, and
 * the size of the queue of select vars and delayed bitblasting + the
 * number of bitblasted atoms.
 */
typedef struct bv_trail_s {
  uint32_t nvars;
  uint32_t natoms;
  uint32_t nbounds;
  uint32_t nselects;
  uint32_t ndelayed;
  uint32_t nbblasted;
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
 * Experimental: simpler approach to deal with equality and
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




/*****************
 *  STATISTICS   *
 ****************/

typedef struct bv_stats_s {
  uint32_t eq_atoms;
  uint32_t on_the_fly_atoms;
  uint32_t ge_atoms;
  uint32_t sge_atoms;
  uint32_t equiv_lemmas;
  uint32_t equiv_conflicts;
  uint32_t half_equiv_lemmas;
  uint32_t interface_lemmas;
} bv_stats_t;


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
   * Bitblast flag: false when new variables/assertions are added
   * true after the constraints have been bitblasted (converted to CNF).
   * - bbptr = number of atoms that have already been bitblasted
   */
  bool bitblasted;
  uint32_t bbptr;

  /*
   * Variable + atom tables
   */
  bv_vartable_t vtbl;
  bv_atomtable_t atbl;

  /*
   * Expanded forms
   */
  bvexp_table_t etbl;

  /*
   * Table to merge equal variables
   */
  mtbl_t mtbl;

  /*
   * Bound queue
   */
  bv_bound_queue_t bqueue;

  /*
   * Data structures for bit-blasting: all are allocated as needed
   */
  bvc_t *compiler;
  bit_blaster_t *blaster;
  remap_table_t *remap;

  /*
   * Queue of egraph assertions
   */
  eassertion_queue_t egraph_queue;

  /*
   * Cache for lemmas: allocated on demand
   */
  cache_t *cache;

  /*
   * Statistics
   */
  bv_stats_t stats;

  /*
   * Queues of select and delayed variables
   */
  bv_queue_t select_queue;
  bv_queue_t delayed_queue;

  /*
   * Push/pop stack
   */
  bv_trail_stack_t trail_stack;


  /*
   * Auxiliary buffers for internalization and simplification
   */
  bvpoly_buffer_t buffer;
  pp_buffer_t prod_buffer;
  ivector_t aux_vector;
  bvconstant_t aux1;
  bvconstant_t aux2;
  bvconstant_t aux3;

  // buffers for computing expanded forms
  bvarith_buffer_t exp_buffer;
  bvarith64_buffer_t exp64_buffer;

  // buffers for computing intervals
  bv_interval_stack_t intv_stack;

  // buffers for bit-blasting
  ivector_t a_vector;
  ivector_t b_vector;


  /*
   * For model construction: mapping of variables to constants
   * - allocated on demand
   */
  bvconst_hmap_t *val_map;

  /*
   * Jump buffer for exception handling during internalization
   */
  jmp_buf *env;

} bv_solver_t;



#endif /* __BVSOLVER_TYPES_H */
