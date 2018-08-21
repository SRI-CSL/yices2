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
 * STAND-ALONE SAT SOLVER
 */

/*
 * This is a new implementation based on Hadrien Barral's work.
 * Hadrien's original code is in sat_solver.h/sat_sover.c.
 * This is a cleanup but similar implementation.
 */

#ifndef __NEW_SAT_SOLVER_H
#define __NEW_SAT_SOLVER_H

#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>
#include <assert.h>

#include "utils/tag_map.h"


/****************
 *  UTILITIES   *
 ***************/

/*
 * We use arrays of 32bit integers in several places.
 * The following macro is intended to define the maximal
 * number of elements in such an array (assuming we store the
 * array size as an unsigned 32bit integer).
 *
 * Not sure this definition is portable, but it should work
 * with gcc and clang.
 */
#if (SIZE_MAX/4) < UINT32_MAX
#define MAX_ARRAY32_SIZE (SIZE_MAX/4)
#else
#define MAX_ARRAY32_SIZE UINT32_MAX
#endif



/************************************
 *  BOOLEAN VARIABLES AND LITERALS  *
 ***********************************/

/*
 * Boolean variables: integers between 1 and nvars.
 * Literals: integers between 2 and 2nvar + 1.
 *
 * For a variable x, the positive literal is 2x, the negative
 * literal is 2x + 1.
 *
 * Variable index 0 is reserved. The corresponding literals
 * 0 and 1 denote true and false, respectively.
 */
typedef uint32_t bvar_t;
typedef uint32_t literal_t;


/*
 * Maximal number of boolean variables.
 * That's also the maximal size of any clause.
 */
#define MAX_VARIABLES (UINT32_MAX >> 2)
#define MAX_CLAUSE_SIZE MAX_VARIABLES

/*
 * Conversions from variables to literals
 */
static inline literal_t pos(bvar_t x) {
  return (x << 1);
}

static inline literal_t neg(bvar_t x) {
  return (x << 1) + 1;
}

static inline bvar_t var_of(literal_t l) {
  return l>>1;
}

// sign: 0 --> positive, 1 --> negative
static inline int32_t sign_of(literal_t l) {
  return l & 1;
}

// negation of literal l
static inline literal_t not(literal_t l) {
  return l ^ 1;
}

// check whether l1 and l2 are opposite
static inline bool opposite(literal_t l1, literal_t l2) {
  return (l1 ^ l2) == 1;
}

// true if l has positive polarity (i.e., l = pos(x))
static inline bool is_pos(literal_t l) {
  return !(l & 1);
}

static inline bool is_neg(literal_t l) {
  return (l & 1);
}


/*
 * Assignment values for a variable:
 * - we use four values to encode the truth value of x
 *   when x is assigned and the preferred value when x is
 *   not assigned.
 * - value[x] is interpreted as follows
 *   val_undef_false = 0b00 --> x not assigned, preferred value = false
 *   val_undef_true  = 0b01 --> x not assigned, preferred value = true
 *   val_false = 0b10       --> x assigned false
 *   val_true =  0b11       --> x assigned true
 *
 * The preferred value is used when x is selected as a decision variable.
 * Then we assign x to true or false depending on the preferred value.
 * This is done by setting bit 1 in value[x].
 */
typedef enum bval {
  BVAL_UNDEF_FALSE = 0,
  BVAL_UNDEF_TRUE = 1,
  BVAL_FALSE = 2,
  BVAL_TRUE = 3,
} bval_t;


// check whether val is undef_true or undef_false
static inline bool is_unassigned_val(bval_t val) {
  return (val & 0x2) == 0;
}

// check whether val is val_undef_true or val_true
static inline bool true_preferred(bval_t val) {
  return (val & 0x1) != 0;
}

// opposite value of v: flip the low order bit
static inline bval_t opposite_val(bval_t val) {
  return val ^ 1;
}


/********************
 *  INTEGER VECTOR  *
 *******************/

/*
 * This is a resizable array of unsigned integers
 * - capacity = maximal size
 * - size = current size
 * - data = array
 */
typedef struct vector_s {
  uint32_t *data;
  uint32_t capacity;
  uint32_t size;
} vector_t;

// Default and maximal size
#define DEF_VECTOR_SIZE 64
#define MAX_VECTOR_SIZE (UINT32_MAX/sizeof(uint32_t))



/*******************
 *  INTEGER QUEUE  *
 ******************/

/*
 * This is a circular buffer:
 * - data = array to store the integers
 * - capacity = size of this array
 * - head, tail = indices between 0 and capacity - 1
 *
 * If head = tail, the queue is empty.
 * If head < tail, the queue's content is data[head ... tail - 1]
 * If head > tail, the queue's content is data[head, ... size - 1]
 * plus data[0 ... tail-1].
 */
typedef struct queue_s {
  uint32_t *data;
  uint32_t capacity;
  uint32_t head;
  uint32_t tail;
} queue_t;

// Default and maximal size
#define DEF_QUEUE_SIZE 64
#define MAX_QUEUE_SIZE (UINT32_MAX/sizeof(literal_t))



/*********************************************
 *  STACK FOR DEPTH-FIRST GRAPH EXPLORATION  *
 ********************************************/

/*
 * This is used in two places.
 *
 * 1) Minimization of the learned clauses after a conflict
 *
 * The implication graph is formed by the true literals.
 * There's an edge in this graph from l0 to l1 if l1 is implied by
 * a clause that contains l0:
 * - either l1 is implied by the clause { l1, ~l0 }
 * - or l1 is implied by a clause of the form { l1, ... ~l0, ... }
 *
 * To explore this graph backward, we use a stack. Each element of
 * the stack contains a boolean variable var + an index i.
 * - the var is an assigned variable and represents a literal l1 in the graph
 * - the index i is the index of the next antecedents of l1 to explore.
 *
 * If l1 is implied by a binary clause { l1, ~l0 } then it has one antecedent
 * (of index 0). If l1 is implied by a clause with n literals then if has
 * n-1 antecedents, indexed from 0 to n-2.
 *
 * 2) Search for strongly connected components in a the binary implication
 * graph.
 *
 * This graph is formed by the binary clauses in the problem. Given a binary
 * clause {l0, l1}, there's an edge from ~l0 to l1 and from ~l1 to l0. To
 * explore this graph, we use the watch vectors: watch[l0] contains all the
 * clauses of the form {l0, l1} (i.e., the successors of ~l0 in the binary
 * implication graph). To enumerate the successors of ~l0, we store an index
 * i in the vector watch[l0].
 */
typedef struct gstack_elem_s {
  uint32_t vertex;
  uint32_t index;
} gstack_elem_t;

typedef struct gstack_s {
  gstack_elem_t *data;
  uint32_t top;
  uint32_t size;
} gstack_t;

#define DEF_GSTACK_SIZE 20
#define MAX_GSTACK_SIZE (UINT32_MAX/sizeof(gstack_elem_t))



/*****************
 *  CLAUSE POOL  *
 ****************/

/*
 * Clauses are stored in a big array of integers.
 *
 * Each clause consists of
 * - header: clause length + auxiliary data
 * - for a learned clause, the auxiliary data is the clause's activity.
 * - for a problem clause, the auxiliary data is a bitmask to accelerate
 *   subsumption checks.
 * - the rest is an array of literals
 * - the first two elements of this array are the watched literals.
 *
 * The pool is divided into three regions:
 * - data[0 ... learned-1]           contains the problem clauses
 * - data[learned_base ... size - 1] contains the learned clauses
 * - data[size ... capacity-1]       unused
 *
 * Each clause is identified by an index i:
 * - data[i]   is the clause length
 * - data[i+1] is the auxiliary data
 * - data[i+2] is the first watched literal
 * - data[i+3] is the second watched literal
 * - data[i+4 ... i+n+2] = rest of the clause = array of n-2 literals
 *   where n = data[i] = clause length.
 *
 * Each clause starts at an index that's a multiple of 4. This ensures
 * that header + two watched literals are in the same cache line.
 *
 * If a clause starts at index i, the next clause starts
 * at index j = ((i + data[i] + 2 + 3) & ~3). That's i + length of the
 * clause + size of the header rounded up to the next multiple of 4.
 *
 * Simplification/in-processing may delete or shrink a clause. This
 * introduces gaps in the data array.  To deal with these gaps, we add
 * padding blocks. A padding block at index i is a block of unused
 * elements in the array.  Its length is a multiple of four.  The
 * first two elements of a padding block are as follows:
 * - data[i] = 0
 * - data[i+1] = length of the padding block.
 * This distinguishes padding blocks from clauses since a clause starts with
 * data[i] >= 2.
 *
 * Some operations require marking clauses. We do this by setting the high-order
 * bit of the length field to 1. This is safe as a clause can't have more than
 * MAX_VARIABLES literals and that's less than 2^31.
 */

// clause structure
typedef struct clause_s {
  uint32_t len;
  union {
    uint32_t d;
    float f;
  } aux;
  literal_t c[0]; // real size is equal to len
} clause_t;

/*
 * Pool structure:
 * - capacity = length of the array data
 * - invariants:
 *     learned <= size <= capacity
 *     available = capacity - size
 *     padding = number of padding cells
 *     learned, size, capacity, available, padding are all multiple of four.
 * - counters: number of clauses/literals
 */
typedef struct clause_pool_s {
  uint32_t *data;
  uint32_t learned;
  uint32_t size;
  uint32_t capacity;
  uint32_t available;
  uint32_t padding;
  //  statistics
  uint32_t num_prob_clauses;      // number of problem clauses
  uint32_t num_prob_literals;     // sum of the length of these clauses
  uint32_t num_learned_clauses;   // number of learned clauses
  uint32_t num_learned_literals;  // sum of the length of these clauses
} clause_pool_t;


/*
 * Initial and maximal capacity of a pool
 * - initial size = 1Mb
 */
#define DEF_CLAUSE_POOL_CAPACITY 262144
#define MAX_CLAUSE_POOL_CAPACITY (MAX_ARRAY32_SIZE & ~3)


// clause index
typedef uint32_t cidx_t;



/*******************
 *  WATCH VECTORS  *
 ******************/

/*
 * Watch vectors play two roles.
 *
 * 1) During search
 *
 * For a literal l, watch[l] stores index/clauses in
 * which l is a watched literal. The information is stored as a
 * sequence of records, in an integer array.
 *
 * VERSION 1:
 * - if l is watched literal in a clause cidx of length >= 3, then
 *   the record is cidx.
 * - if l occurs in a binary clause { l, l1 } then the record is the
 *   literal l1
 *
 * To tell the difference, we use the lower-order bit of the integer:
 * - [cidx] is stored as is. The two low-order bits of cidx are 00.
 * - [l1] is stored as (l1 << 1)|1  (lower-order bit = 1)
 *
 *
 * VERSION 2:
 * - add a 'blocker' literal: for a clause cidx, we store the pair
 *   [cidx, l2] where l2 is a blocker. It's a literal that occurs in
 *   the clause. If l2 is true, we don't need to visit the clause
 *   to see that it can't propagate anything.
 *
 *
 * 2) During preprocessing
 *
 * Watch[l] stores all the clauses in which l occurs. In this mode,
 * both binary clauses and larger clauses are stored in the clause pool.
 * The vector watch[l] contains then an array of clause indices.
 *
 * The watch structure is a vector:
 * - capacity = full length of the data array
 * - size = number of array elements actually used
 */
typedef struct watch_s {
  uint32_t capacity;
  uint32_t size;
  uint32_t data[0]; // real length = capacity
} watch_t;



/*******************
 *  SAVED CLAUSES  *
 ******************/

/*
 * When variables/clauses are eliminated, we may need to keep a copy of some
 * of the clauses to recover the truth value of eliminated variables.
 * The saved data is a set of clauses of the form C_1 \/ l ... C_k \/ l
 * where l is either pos(x) or neg(x) and x is an eliminated variable.
 *
 * If we have a model M that doesn't give a value to x, we extend the assignment
 * by checking whether C_1, ..., C_k are all true in M. It they are, we set l := false
 * Otherwise, we set l := true (to force C_1 \/ l .... C_k \/ l to all be true in the
 * extended model. For this to work, we must process the variables in reverse order of
 * elimination, so that C_1 ... C_k have a value in M when we process x.
 *
 * The saved clauses are stored in a vector and are organized in blocks.
 * Each block stores k clauses C_1 \/ l ... C_k \/ l as above. The eliminated literal 'l'
 * is the last element of each clause. We then store the length of the block.
 * This looks like this:
 *
 *   -----------------------------------------------------------------------------
 *    previous block | C_1 ... l | C_2 ... l | ... | C_k ... l | n |  next block
 *   -----------------------------------------------------------------------------
 *
 * where n = total number of literals in C1 \/ l .... C_k \/ l.
 */
typedef struct clause_vector_s {
  uint32_t *data;    // array to store the clauses
  uint32_t top;      // end of the last block (0 if there's nothing saved)
  uint32_t capacity; // full size of the data array
} clause_vector_t;

#define DEF_CLAUSE_VECTOR_CAPACITY 10240
#define MAX_CLAUSE_VECTOR_CAPACITY MAX_ARRAY32_SIZE



/**********************
 *  ELIMINATION HEAP  *
 *********************/

/*
 * During preprocessing, we try to eliminate variables by full resolution.
 * We use a heuristic based on the number of positive/negative occurrences
 * of x to order the variables to eliminate. To store the variables in
 * order, we use a binary heap:
 * - data: heap proper as an array of variables
 * - elim_idx: position of variables in the data array
 * - size = number of elements stored in the data array
 * - capacity = full size of the data array
 *
 * For every i in [0 ... size-1], data[i] is a variable
 * - data[0] is always equal to 0 (it's used as a marker)
 * - for i>0 data[i] = a candidate variable for elimination
 *
 * For every variable x,
 * - elim_idx[x] = i iff data[i] = x
 * - elim_idx[x] = -1 if x is not stored in the heap
 */
typedef struct elim_heap_s {
  bvar_t *data;
  int32_t *elim_idx;
  uint32_t size;
  uint32_t capacity;
} elim_heap_t;

#define DEF_ELIM_HEAP_SIZE 1024
#define MAX_ELIM_HEAP_SIZE (UINT32_MAX/sizeof(bvar_t))



/**********************
 *  ASSIGNMENT STACK  *
 *********************/

/*
 * Assignment stack/propagation queue
 * - an array of literals (the literals assigned to true)
 * - two pointers: top of the stack, beginning of the propagation queue
 * - for each decision level, an index into the stack points
 *   to the literal decided at that level (for backtracking)
 */
typedef struct {
  literal_t *lit;
  uint32_t top;
  uint32_t prop_ptr;
  uint32_t *level_index;
  uint32_t nlevels; // size of level_index array
} sol_stack_t;


/*
 * Initial size of level_index
 */
#define DEFAULT_NLEVELS 100



/*******************
 *  CLAUSE STACK   *
 ******************/

/*
 * Experimental data structure to store clauses in a stack,
 * organized by decision levels.
 *
 * Clauses are stored in array data using the same format as clause_pool.
 * A clause is identified by an index i (which is a multiple of four)
 *   data[i] = clause length
 *   data[i+1] = auxiliary data (clause LDB)
 *   data[i+2,... i+n+2] = array of n literals = the clause
 * The first literal (in data[i+2]) is true.
 * The other literals in data[i+3 ... i+n+2] are all false.
 *
 * The stack is organize in levels:
 * - level[i] = index of the first clause learned at decision level i
 * - nlevels = number of levels
 *
 * Rest of the stack:
 * - capacity = full size of array data
 * - top = index in array data where the next clause will be stored
 */
typedef struct {
  uint32_t *data;
  uint32_t top;
  uint32_t capacity; // size of array data
  uint32_t *level;
  uint32_t nlevels; // size of array level
} clause_stack_t;


/*
 * Initial and maximal capacity
 * DEFAULT_NLEVELS is 100.
 */
#define DEF_CLAUSE_STACK_CAPACITY 16384
#define MAX_CLAUSE_STACK_CAPACITY (MAX_ARRAY32_SIZE & ~3)




/******************************
 *  HEAP/VARIABLE ACTIVITIES  *
 *****************************/

/*
 * Heap and variable activities for the variable-selection heuristic
 * - activity[x]: for every variable x between 1 and nvars - 1
 * - index 0 is used as marker:
 *    activity[0] = DBL_MAX (higher than any activity)
 * - heap_index[x]: for every variable x,
 *      heap_index[x] = i if x is in the heap and heap[i] = x
 *   or heap_index[x] = -1 if x is not in the heap
 * - heap: array of nvars variables
 * - heap_last: index of last element in the heap
 *   heap[0] = 0,
 *   for i=1 to heap_last, heap[i] = x for some variable x
 * - size = number of variable (nvars)
 * - vmax = variable index (last variable not in the heap)
 * - act_inc: variable activity increment
 * - inv_act_decay: inverse of variable activity decay (e.g., 1/0.95)
 *
 * The set of variables is split into two segments:
 * - [1 ... vmax-1] = variables that are in the heap or have been in the heap
 * - [vmax ... size-1] = variables that may not have been in the heap
 *
 * To pick a decision variable:
 * - search for the most active unassigned variable in the heap
 * - if the heap is empty or all its variables are already assigned,
 *   search for the first unassigned variables in [vmax ... size-1]
 *
 * Initially: we set vmax to 1 (nothing in the heap yet) so decision
 * variables are picked in increasing order, starting from 1.
 */
typedef struct var_heap_s {
  double *activity;
  int32_t *heap_index;
  bvar_t *heap;
  uint32_t heap_last;
  uint32_t size;
  uint32_t vmax;
  double act_increment;
  double inv_act_decay;
} var_heap_t;



/****************
 *  STATISTICS  *
 ***************/

typedef struct solver_stats_s {
  uint64_t decisions;                // number of decisions
  uint64_t random_decisions;         // number of random decisions
  uint64_t propagations;             // number of boolean propagations
  uint64_t conflicts;                // number of conflicts/backtracking
  uint64_t prob_clauses_deleted;     // number of problem clauses deleted
  uint64_t learned_clauses_deleted;  // number of learned clauses deleted
  uint64_t subsumed_literals;        // removed from learned clause (cf. simplify_learned_clause)

  uint32_t starts;                   // 1 + number of restarts
  uint32_t dives;                    // number of dives
  uint32_t simplify_calls;           // number of calls to simplify_clause_database
  uint32_t reduce_calls;             // number of calls to reduce_learned_clause_set
  uint32_t scc_calls;                // number of calls to try_scc_simplification
  uint32_t subst_calls;              // number of calls to apply_substitution
  uint32_t successful_dive;          // whether we found sat by diving

  // Substitutions
  uint32_t subst_vars;               // number of variables eliminated by substitution

  // Preprocessing statistics
  uint32_t pp_pure_lits;             // number of pure literals removed
  uint32_t pp_unit_lits;             // number of unit literals removed
  uint32_t pp_clauses_deleted;       // number of clauses deleted during preprocessing
  uint32_t pp_subsumptions;          // number of subsumed clauses
  uint32_t pp_strengthenings;        // number of strengthened clauses
  uint32_t pp_unit_strengthenings;   // number of clauses strengthened to unit
  uint32_t pp_cheap_elims;           // cheap variable eliminations
  uint32_t pp_var_elims;             // less cheap variable eliminations
} solver_stats_t;


/**************************
 *  HEURISTIC PARAMETERS  *
 *************************/

typedef struct solver_param_s {
  /*
   * Search/restart/reduce heuristics
   */
  uint32_t seed;               // Seed for the pseudo-random number generator
  uint32_t randomness;         // 0x1000000 * random_factor
  float inv_cla_decay;         // Inverse of clause decay (1/0.999)

  uint32_t stack_threshold;    // Size of learned clause to preserve when in diving mode
  uint32_t keep_lbd;           // Clauses of LBD no more than this are preserved during reduce
  uint32_t reduce_fraction;    // Fraction of learned clauses to delete (scaled by 32)
  uint32_t reduce_interval;    // Number of conflicts between two calls to reduce
  uint32_t reduce_delta;       // Adjustment to reduce_interval
  uint32_t restart_interval;   // Minimal number of conflicts between two restarts

  uint32_t search_period;      // Number of conflicts before we check for progress
  uint32_t search_counter;     // Number of periods before we switch to diving

  uint32_t diving_budget;      // Number of conflicts before giving up diving

  /*
   * Heuristics/parameters for preprocessing
   * (these have no effect if the 'preprocess' flag is false)
   *
   * - subsume_skip: when checking whether a clause cl can subsume something,
   *   we visit clauses that share a variable with cl. It the number of clauses to
   *   visit is larger than subsume_skip  we skip clause cl. The subsumption check would
   *   be too expensive. This parameter is 3000 by default.
   *
   * - var_elim_skip controls which variables we try to eliminate. It's 10 by default.
   *   x is not considered if it has more than var_elim_skip positive and negative occurrences.
   *
   * - res_clause_limit: if eliminating a variable x would create a clause of size
   *   larger than res_clause_limit, we keep x. Default value = 20.
   */
  uint32_t subsume_skip;
  uint32_t var_elim_skip;
  uint32_t res_clause_limit;

  /*
   * Simplify heuristics
   */
  uint32_t simplify_interval;   // Minimal number of conflicts between two calls to simplify
  uint32_t simplify_bin_delta;  // Number of new binary clauses between two SCC computations
} solver_param_t;


/**********************
 *  ANTECEDENT TAGS   *
 *********************/

/*
 * When a variable is assigned, we store a tag to identify the reason
 * for the assignment. There are four cases:
 * - unit clause
 * - decision literal
 * - propagated from a binary clause
 * - propagated from a non-binary clause
 * + another one for variables not assigned
 * + another one for variables propagated from a stacked clause.
 *
 * If preprocessing is enabled, we also use this tag to keep track of
 * eliminated variables:
 * - pure literals
 * - variables eliminated by resolution
 *
 * We also support variable elimination by substitution. If variable x
 * is mapped to a literal l then we set ante_tag[x] = ATAG_SUBST and
 * ante_data[x] = l.
 */
typedef enum antecedent_tag {
  ATAG_NONE,
  ATAG_UNIT,
  ATAG_DECISION,
  ATAG_BINARY,
  ATAG_CLAUSE,
  ATAG_STACKED,

  ATAG_PURE,
  ATAG_ELIM,
  ATAG_SUBST,
} antecedent_tag_t;

#define NUM_ATAGS (ATAG_SUBST+1)

/*
 * Conflict tag:  when a clause is false, we store it for conflict analysis
 * and backtracking. The conflict tag records the type of clauses that's false.
 * There are two cases: binary clause + non-binary clause
 * + another tag for no conflict.
 *
 * For a binary clause conflict, the clause is stored in conflict_buffer.
 * For a non-binary clause, the clause index is stored in conflict_idx.
 */
typedef enum conflict_tag {
  CTAG_NONE,
  CTAG_BINARY,
  CTAG_CLAUSE,
} conflict_tag_t;


/*
 * SOLVER STATUS
 */
typedef enum solver_status {
  STAT_UNKNOWN,
  STAT_SAT,
  STAT_UNSAT,
} solver_status_t;


/******************
 *  FULL SOLVER   *
 *****************/

/*
 * For each variable x, we store
 * - ante_tag[x]  = tag for assigned variables + marks
 * - ante_data[x] = antecedent index
 * - level[x]     = assignment level
 *
 * For each literal l, we keep
 * - watch[l] = watch vector for l
 * - value[l] = assigned value
 *
 * If preprocessing is enabled:
 * - occ[l] = number of clauses that contain l
 */
typedef struct sat_solver_s {
  solver_status_t status;
  uint32_t decision_level;
  uint32_t backtrack_level;
  bool preprocess;             // True if preprocessing is enabled

  uint32_t verbosity;          // Verbosity level: 0 means quiet
  uint32_t reports;            // Counter

  /*
   * Variables and literals
   */
  uint32_t nvars;              // Number of variables
  uint32_t nliterals;          // Number of literals = twice nvars
  uint32_t vsize;              // Size of the variable-indexed arrays (>= nvars)
  uint32_t lsize;              // Size of the watch array (>= nlits)

  uint8_t *value;
  uint8_t *ante_tag;
  uint32_t *ante_data;
  uint32_t *level;
  watch_t **watch;
  uint32_t *occ;              // Occurrence counts

  var_heap_t heap;            // Variable heap
  sol_stack_t stack;          // Assignment/propagation queue


  /*
   * Clause database and related stuff:
   *
   * Default mode:
   * - unit clauses are stored implicitly in the assignment stack
   * - binary clauses are stored implicitly in the watch vectors
   * - all other clauses are in the pool
   *
   * Preprocessing mode:
   * - unit clauses are in the assignment stack
   * - all other clauses are in the pool (including binary clauses).
   */
  bool has_empty_clause;      // Whether the empty clause was added
  uint32_t units;             // Number of unit clauses
  uint32_t binaries;          // Number of binary clauses
  clause_pool_t pool;         // Pool for non-binary/non-unit clauses

  /*
   * Clause stack (experimental)
   */
  clause_stack_t stash;

  /*
   * Conflict data
   */
  conflict_tag_t conflict_tag;
  uint32_t conflict_buffer[2];
  cidx_t conflict_index;

  /*
   * Parameters
   */
  solver_param_t params;

  /*
   * Counters/variables used by the search heuristics
   */
  float cla_inc;               // Clause activity increment

  uint32_t prng;               // State of the pseudo-random number generator

  uint64_t reduce_next;        // Number of conflicts before the next call to reduce
  uint32_t reduce_inc;         // Increment to reduce_threshold
  uint32_t reduce_inc2;        // Increment to reduce_inc

  uint32_t simplify_assigned;  // Number of literals assigned at level0 after the last call to simplify_clause_database
  uint32_t simplify_binaries;  // Number of binary clauses after the last call to simplify_clause_database
  uint32_t simplify_new_bins;  // Number of binary clauses created by simplification
  uint32_t simplify_new_units; // number of unit clauses create by simplification
  uint64_t simplify_next;      // Number of conflicts before the next call to simplify

  /*
   * Exponential moving averages for restarts
   * (based on "Evaluating CDCL Restart Schemes" by Biere & Froehlich, 2015).
   */
  uint64_t slow_ema;
  uint64_t fast_ema;
  uint64_t level_ema;
  uint64_t restart_next;
  uint32_t fast_count;

  /*
   * Experimental: counters for switching to dive mode
   */
  uint32_t progress_units;
  uint32_t progress_binaries;
  uint32_t progress;
  uint64_t check_next;

  /*
   * Experimental: in diving mode: attempt to go as deep as possible
   * in the search tree. We keep track of max search depth
   * and the number of conflicts when it was reached.
   */
  bool diving;
  uint32_t dive_budget;
  uint32_t max_depth;
  uint64_t max_depth_conflicts;
  uint64_t dive_start;


  /*
   * Statistics record
   */
  solver_stats_t stats;

  /*
   * Auxiliary array for clause deletion
   */
  cidx_t *cidx_array;

  /*
   * Buffers and other data structures to build and simplify clauses.
   */
  vector_t buffer;
  vector_t aux;
  gstack_t gstack;
  tag_map_t map;

  /*
   * Saved clauses
   */
  clause_vector_t saved_clauses;

  /*
   * Data structures used during preprocessing:
   * 1) lqueue: queue of pure and unit literals to eliminate
   * 2) elim: heap of candidate variables to eliminate
   * 3) for clause subsumption:
   *    - we visit clauses sequentially
   *    - scan_index = index of the next clause to visit
   *    - cqueue = more clauses that have to be revisited
   *    - every clause in cqueue is marked
   */
  queue_t lqueue;
  elim_heap_t elim;
  queue_t cqueue;
  vector_t cvector;
  uint32_t scan_index;


  /*
   * Data structures to compute SCC in the binary implication graph.
   */
  vector_t vertex_stack;
  gstack_t dfs_stack;
  uint32_t *label;
  uint32_t *visit;

  /*
   * File for data collection (used only when macro DATA is non-zero)
   */
  FILE *data;

} sat_solver_t;


// Default size for the variable array
#define SAT_SOLVER_DEFAULT_VSIZE 1024

// Default buffer size
#define SAT_SOLVER_BUFFER_SIZE 60



/********************
 *  MAIN FUNCTIONS  *
 *******************/

/*
 * Initialization:
 * - sz = initial size of the variable-indexed arrays.
 * - pp = whether to use preprocessing
 *
 * - if sz is zero, the default size is used.
 * - if pp is true, the solver is initialized for preprocessing,
 *   otherwise no preprocessing is used.
 * - the solver is initialized with one variable (the reserved variable 0).
 * - verbosity is 0.
 */
extern void init_nsat_solver(sat_solver_t *solver, uint32_t sz, bool pp);

/*
 * Set the verbosity level
 * - this determines how much stuff is printed (on stderr) during the search.
 * - level == 0 --> print nothing (this is the default)
 * - level >= 1 --> print statistics about preprocessing
 * - level >= 2 --> print statistics at every restart
 */
extern void nsat_set_verbosity(sat_solver_t *solver, uint32_t level);

/*
 * Deletion: free memory
 */
extern void delete_nsat_solver(sat_solver_t *solver);

/*
 * Reset: remove all variables and clauses
 */
extern void reset_nsat_solver(sat_solver_t *solver);

/*
 * Add n fresh variables:
 * - they are indexed from nv, ..., nv + n-1 where nv = number of
 *   variables in solver (on entry to this function).
 */
extern void nsat_solver_add_vars(sat_solver_t *solver, uint32_t n);

/*
 * Allocate a fresh Boolean variable and return its index.
 */
extern bvar_t nsat_solver_new_var(sat_solver_t *solver);




/*********************************
 *  CHANGE HEURISTIC PARAMETERS  *
 ********************************/

/*
 * Variable activity decay: must be between 0 and 1.0
 * - smaller number means faster decay
 */
extern void nsat_set_var_decay_factor(sat_solver_t *solver, double factor);

/*
 * Clause activity decay: must be between 0 and 1.0
 * - smaller means faster decay
 */
extern void nsat_set_clause_decay_factor(sat_solver_t *solver, float factor);

/*
 * Randomness: the parameter is approximately the ratio of random
 * decisions.
 * - randomness = 0: no random decisions
 * - randomness = 1.0: all decisions are random
 */
extern void nsat_set_randomness(sat_solver_t *solver, float randomness);

/*
 * Set the prng seed
 */
extern void nsat_set_random_seed(sat_solver_t *solver, uint32_t seed);

/*
 * Stack clause threshold: learned clauses of LBD greater than threshold are
 * treated as temporary clauses (not stored in the clause database).
 */
extern void nsat_set_stack_threshold(sat_solver_t *solver, uint32_t f);

/*
 * LBD threshold for clause deletion. Clauses of lbd <= keep_lbd are not deleted.
 */
extern void nsat_set_keep_lbd(sat_solver_t *solver, uint32_t threshold);

/*
 * Reduce fraction for clause deletion. f must be between 0 and 32.
 * Each call to reduce_learned_clause_set removes a fraction (f/32) of the clauses
 */
extern void nsat_set_reduce_fraction(sat_solver_t *solver, uint32_t f);

/*
 * Interval between two calls to reduce (number of conflicts)
 */
extern void nsat_set_reduce_interval(sat_solver_t *solver, uint32_t n);

/*
 * Adjustment to the reduce interval (check init_reduce and done_reduce).
 */
extern void nsat_set_reduce_delta(sat_solver_t *solver, uint32_t d);


/*
 * Minimal number of conflicts between two calls to restart
 */
extern void nsat_set_restart_interval(sat_solver_t *solver, uint32_t n);


/*
 * Periodic check for switching to dive
 */
extern void nsat_set_search_period(sat_solver_t *solver, uint32_t n);


/*
 * Counter used in determining when to switch
 */
extern void nsat_set_search_counter(sat_solver_t *solver, uint32_t n);


/*
 * Dive bugdet
 */
extern void nsat_set_dive_budget(sat_solver_t *solver, uint32_t n);


/*
 * PREPROCESSING PARAMETERS
 */

/*
 * Subsumption limit: skip subsumption checks for a clause cls if that
 * would require visiting more than subsume_skip clauses.
 */
extern void nsat_set_subsume_skip(sat_solver_t *solver, uint32_t limit);

/*
 * Var-elimination limit: if x has too many positive and negative occurrences,
 * we don't try to eliminate x.
 */
extern void nsat_set_var_elim_skip(sat_solver_t *solver, uint32_t limit);

/*
 * Resolvent limit: if eliminating x would create a clause larger than
 * res_clause_limit, we keep x.
 */
extern void nsat_set_res_clause_limit(sat_solver_t *solver, uint32_t limit);


/*
 * SIMPLIFY PARAMETERS
 */

/*
 * Minimal number of conflicts between two calls to simplify
 */
extern void nsat_set_simplify_interval(sat_solver_t *solver, uint32_t n);

/*
 * Number of new binary clauses before two SCC computations
 */
extern void nsat_set_simplify_bin_delta(sat_solver_t *solver, uint32_t d);


/*********************
 *  CLAUSE ADDITION  *
 ********************/

/*
 * A clause is an array of literals (integers between 0 and nlits - 1)
 * - a clause is simplified if it satisfies the following conditions:
 *   1) it doesn't contain assigned literals (including the reserved
 *      literals 0 and 1)
 *   2) it doesn't include duplicates or complementary literals
 *
 * This function simplifies the clause then adds it
 * - n = number of literals
 * - l = array of n literals
 * - the array is modified
 */
extern void nsat_solver_simplify_and_add_clause(sat_solver_t *solver, uint32_t n, literal_t *l);


/*************
 *  SOLVING  *
 ************/

/*
 * Check satisfiability of the set of clauses
 * - result = either STAT_SAT or STAT_UNSAT
 */
extern solver_status_t nsat_solve(sat_solver_t *solver);


/*
 * Read the status
 */
static inline solver_status_t nsat_status(sat_solver_t *solver) {
  return solver->status;
}



/**************************
 *  VARIABLE ASSIGNMENTS  *
 *************************/

static inline bval_t lit_value(const sat_solver_t *solver, literal_t l) {
  assert(l < solver->nliterals);
  return solver->value[l];
}

static inline bval_t var_value(const sat_solver_t *solver, bvar_t x) {
  assert(x < solver->nvars);
  return solver->value[pos(x)];
}

static inline bool lit_is_unassigned(const sat_solver_t *solver, literal_t l) {
  return is_unassigned_val(lit_value(solver, l));
}

static inline bool var_is_unassigned(const sat_solver_t *solver, bvar_t x) {
  return is_unassigned_val(var_value(solver, x));
}

static inline bool var_is_assigned(const sat_solver_t *solver, bvar_t x) {
  return ! var_is_unassigned(solver, x);
}

static inline bool lit_is_assigned(const sat_solver_t *solver, literal_t l) {
  return ! lit_is_unassigned(solver, l);
}

static inline bool lit_prefers_true(const sat_solver_t *solver, literal_t l) {
  return true_preferred(lit_value(solver, l));
}

static inline bool lit_is_true(const sat_solver_t *solver, literal_t l) {
  return lit_value(solver, l) == BVAL_TRUE;
}

static inline bool lit_is_false(const sat_solver_t *solver, literal_t l) {
  return lit_value(solver, l) == BVAL_FALSE;
}


static inline bool var_prefers_true(const sat_solver_t *solver, bvar_t x) {
  return true_preferred(var_value(solver, x));
}

static inline bool var_is_true(const sat_solver_t *solver, bvar_t x) {
  return var_value(solver, x) == BVAL_TRUE;
}

static inline bool var_is_false(const sat_solver_t *solver, bvar_t x) {
  return var_value(solver, x) == BVAL_FALSE;
}



/************
 *  MODELS  *
 ***********/

/*
 * Return the model: copy all variable value into val
 * - val's size must be at least solver->nvars
 * - val[0] is always true
 */
extern void nsat_get_allvars_assignment(const sat_solver_t *solver, bval_t *val);

/*
 * Copy all true literals in array a:
 * - a must have size >= solver->nvars.
 * return the number of literals added to a.
 */
extern uint32_t nsat_get_true_literals(const sat_solver_t *solver, literal_t *a);


/******************************
 * PRINT INTERNAL STRUCTURES  *
 *****************************/

extern void show_state(FILE *f, const sat_solver_t *solver);


/*******************************
 * STATISTICS/DATA COLLECTION  *
 ******************************/

/*
 * If the solver is compiled with DATA enabled,
 * then data is collected in a file after every conflict.
 * - this function opens the data file
 * - name = name of the file to use
 * - if the file can't be created, no error is produced
 *   (and no data will be collected).
 *
 * If DATA is disabled, the function does nothing.
 */
extern void nsat_open_datafile(sat_solver_t *solver, const char *name);



#endif /* __NEW_SAT_SOLVER_H */
