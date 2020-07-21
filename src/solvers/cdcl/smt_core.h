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
 * DPLL(T) SOLVER
 *
 * An smt_core structure is parameterized by a theory-solver
 * object. Operations that the theory solver must implement are
 * accessed via function pointers.
 *
 * Atoms, explanations, and theory solver are treated abstractly by the smt_core.
 * They are represented by generic (void *) pointers. The two lower-order bits
 * of an explanation pointer must be 00 (aligned to a multiple of 4bytes).
 *
 * The core has support for
 * - creation of boolean variables
 * - attaching atoms to boolean variables
 * - addition of clauses
 * - push/pop/reset operations
 * - boolean and theory propagation
 * - assertion of implied literals and conflicts
 * - conflict resolution and construction of learned clauses
 * - optional deletion of newly created atoms on backtracking (to support
 *   solver that create many atoms on the fly).
 * - restart
 * - reduction of learned clause database
 *
 * Variables and clauses can be added on the fly, during the search.
 *
 * History: created January 10, 2008.
 * Based on an earlier version (dpll.h and dpll.c) that was not sufficient.
 */

#ifndef __SMT_CORE_H
#define __SMT_CORE_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#include "io/tracer.h"
#include "solvers/cdcl/smt_core_base_types.h"
#include "solvers/cdcl/gates_hash_table.h"
#include "utils/bitvectors.h"
#include "utils/int_vectors.h"

#include "yices_types.h"


// EXPERIMENTAL
#include "scratch/booleq_table.h"


/***********
 * CLAUSES *
 **********/

/*
 * Clauses structure
 * - two pointers to form lists of clauses for the watched literals
 * - a clause is an array of literals terminated by an end marker
 *   (a negative number).
 * - the first two literals stored in cl[0] and cl[1]
 *   are the watched literals.
 * Learned clauses have the same components as a clause
 * and an activity, i.e., a float used by the clause-deletion
 * heuristic. (Because of alignment and padding, this wastes 32bits
 * on a 64bit machine....)
 *
 * Linked lists:
 * - a link lnk is a pointer to a clause cl
 *   the low-order bits of lnk encode whether the next link is
 *   in cl->link[0] or cl->link[1]
 * - this is compatible with the tagged pointers used as antecedents.
 *
 * SPECIAL CODING: to distinguish between learned clauses and problem
 * clauses, the end marker is different.
 * - for problem clauses, end_marker = -1
 * - for learned clauses, end_marker = -2
 *
 * These two end_markers always have an UNDEF_VALYE:
 * - value[-1] = VAL_UNDEF_FALSE
 *   value[-2] = VAL_UNDEF_FALSE
 *
 * CLAUSE DELETION AND SIMPLIFICATION:
 * - to mark a clause for deletion or to removed it from the watched lists,
 *   both cl[0] and cl[1] are replaced by their opposite (turned into negative numbers).
 */

enum {
  end_clause = -1,  // end of problem clause
  end_learned = -2, // end of learned clause
};

typedef struct clause_s clause_t;

typedef uintptr_t link_t;

struct clause_s {
  link_t link[2];
  literal_t cl[0];
};

typedef struct learned_clause_s {
  float activity;
  clause_t clause;
} learned_clause_t;


/*
 * Tagging/untagging of link pointers
 */
#define LINK_TAG ((uintptr_t) 0x1)
#define NULL_LINK ((link_t) 0)

static inline link_t mk_link(clause_t *c, uint32_t i) {
  assert((i & ~LINK_TAG) == 0 && (((uintptr_t) c) & LINK_TAG) == 0);
  return (link_t)(((uintptr_t) c) | ((uintptr_t) i));
}

static inline clause_t *clause_of(link_t lnk) {
  return (clause_t *)(lnk & ~LINK_TAG);
}

static inline uint32_t idx_of(link_t lnk) {
  return (uint32_t)(lnk & LINK_TAG);
}

static inline link_t next_of(link_t lnk) {
  return clause_of(lnk)->link[idx_of(lnk)];
}


/*
 * return a new link lnk0 such that
 * - clause_of(lnk0) = c
 * - idx_of(lnk0) = i
 * - next_of(lnk0) = lnk
 */
static inline link_t cons(uint32_t i, clause_t *c, link_t lnk) {
  assert(i <= 1);
  c->link[i] = lnk;
  return mk_link(c, i);
}

/*
 * If lnk points to a clause cl, then return
 * a pointer to either cl->link[0] or cl->link[1], depending on
 * the lower order bit of lnk.
 */
static inline link_t *cdr_ptr(link_t lnk) {
  return clause_of(lnk)->link + idx_of(lnk);
}





/*********************************
 *  CLAUSE AND LITERAL VECTORS   *
 ********************************/

/*
 * Vectors are arrays preceded by a hidden header
 * - e.g., a literal vector v is a pointer to literals
 * - the elements in the vectors are v[0] ... v[n-1]
 * - the header specifies the capacity and current size of v
 */
typedef struct clause_vector_s {
  uint32_t capacity;
  uint32_t size;
  clause_t *data[0];
} clause_vector_t;

typedef struct literal_vector_s {
  uint32_t capacity;
  uint32_t size;
  literal_t data[0];
} literal_vector_t;


/*
 * Access to header of clause vector v
 */
static inline clause_vector_t *cv_header(clause_t **v) {
  return (clause_vector_t *)(((char *)v) - offsetof(clause_vector_t, data));
}

static inline uint32_t get_cv_size(clause_t **v) {
  return cv_header(v)->size;
}

static inline void set_cv_size(clause_t **v, uint32_t sz) {
  cv_header(v)->size = sz;
}

static inline uint32_t get_cv_capacity(clause_t **v) {
  return cv_header(v)->capacity;
}


/*
 * Header, size and capacity of a literal vector v
 */
static inline literal_vector_t *lv_header(literal_t *v) {
  return (literal_vector_t *)(((char *) v) - offsetof(literal_vector_t, data));
}

static inline uint32_t get_lv_size(literal_t *v) {
  return lv_header(v)->size;
}

static inline void set_lv_size(literal_t *v, uint32_t sz) {
  lv_header(v)->size = sz;
}

static inline uint32_t get_lv_capacity(literal_t *v) {
  return lv_header(v)->capacity;
}



/*
 * Default sizes and max sizes of vectors
 */
#define DEF_CLAUSE_VECTOR_SIZE 100
#define MAX_CLAUSE_VECTOR_SIZE (((uint32_t)(UINT32_MAX-sizeof(clause_vector_t)))/8)

#define DEF_LITERAL_VECTOR_SIZE 10
#define DEF_LITERAL_BUFFER_SIZE 100
#define MAX_LITERAL_VECTOR_SIZE (((uint32_t)(UINT32_MAX-sizeof(literal_vector_t)))/4)



/**********************************
 *  ASSIGNMENT/PROPAGATION QUEUE  *
 *********************************/

/*
 * Assignment stack/propagation queue
 * - an array of literals (the literals assigned to true)
 * - pointers: top of the stack
 * - pointers for boolean and theory propagation
 *   - prop_ptr: beginning of the boolean propagation queue
 *   - theory_ptr: beginning of the theory propagation queue
 * - literals in stack->lit[prop_ptr ... top-1] form the boolean propagation queue
 * - literals in stack->lit[theory_ptr ... top-1] form the theory  propagation queue
 * - for each decision level, an index into the stack points
 *   to the literal decided or assigned at that level (for backtracking)
 * - for level 0, level_index[0] = 0 = index of the first literal assigned
 */
typedef struct {
  literal_t *lit;
  uint32_t top;
  uint32_t prop_ptr;
  uint32_t theory_ptr;
  uint32_t *level_index;
  uint32_t nlevels; // size of level_index array
} prop_stack_t;


/*
 * Initial size of level_index
 */
#define DEFAULT_NLEVELS 100




/******************
 *  ANTECEDENTS   *
 *****************/

/*
 * Antecedent = reason for an implied literal.
 * It's either a clause or a literal or a generic explanation.
 * Antecedents are represented as tagged pointers with tag in the
 * two low-order bits
 * - tag = 00: clause with implied literal as cl[0]
 * - tag = 01: clause with implied literal as cl[1]
 * - tag = 10: literal
 * - tag = 11: generic explanation from a theory solver
 */
typedef uintptr_t antecedent_t;

enum {
  clause0_tag = 0,
  clause1_tag = 1,
  literal_tag = 2,
  generic_tag = 3,
};

static inline uint32_t antecedent_tag(antecedent_t a) {
  return a & 0x3;
}

static inline literal_t literal_antecedent(antecedent_t a) {
  return (literal_t) (((int32_t) a) >>2);
}

static inline clause_t *clause_antecedent(antecedent_t a) {
  return (clause_t *) (a & ~((uintptr_t) 0x3));
}

// clause index: 0 or 1, low order bit of a
static inline uint32_t clause_index(antecedent_t a) {
  return (uint32_t) (a & 0x1);
}

static inline void *generic_antecedent(antecedent_t a) {
  return (void *) (a & ~((uintptr_t) 0x3));
}

static inline antecedent_t mk_literal_antecedent(literal_t l) {
  return (((uintptr_t) l) << 2) | literal_tag;
}

static inline antecedent_t mk_clause0_antecedent(clause_t *cl) {
  assert((((uintptr_t) cl) & 0x3) == 0);
  return ((uintptr_t) cl) | clause0_tag;
}

static inline antecedent_t mk_clause1_antecedent(clause_t *cl) {
  assert((((uintptr_t) cl) & 0x3) == 0);
  return ((uintptr_t) cl) | clause1_tag;
}

static inline antecedent_t mk_clause_antecedent(clause_t *cl, int32_t idx) {
  assert((((uintptr_t) cl) & 0x3) == 0);
  return ((uintptr_t) cl) | (idx & 1);
}

static inline antecedent_t mk_generic_antecedent(void *g) {
  assert((((uintptr_t) g) & 0x3) == 0);
  return ((uintptr_t) g) | generic_tag;
}


/*
 * Macros to pack/unpack an integer into a void* pointer
 * to be used as a generic explanation.
 * - we can't use the default tag_i32/untag_i32 because we must
 *   keep the two lower bits 00
 */
static inline void *mk_i32_expl(int32_t x) {
  return (void *) (((uintptr_t) ((uint32_t) x))<<2);
}

static inline int32_t i32_of_expl(void *g) {
  return (int32_t) (((uintptr_t) g) >> 2);
}



/*******************
 *  VARIABLE HEAP  *
 ******************/

/*
 * Heap: for activity-based variable selection heuristic
 * - activity[x]: for every variable x between 0 and nvars - 1
 * - indices -1 and -2 are used as sentinels:
 *   activity[-1] = DBL_MAX (higher than any activity)
 *   activity[-2] = -1.0 (lower than any variable activity)
 * - heap_index[x]: for every variable x,
 *      heap_index[x] = i if x is in the heap and heap[i] = x
 *   or heap_index[x] = -1 if x is not in the heap
 * - heap: array of nvars + 1 variables
 * - heap_last: index of last element in the heap
 *   heap[0] = -1,
 *   for i=1 to heap_last, heap[i] = x for some variable x
 * - act_inc: variable activity increment
 * - inv_act_decay: inverse of variable activity decay (e.g., 1/0.95)
 */
typedef struct var_heap_s {
  uint32_t size;
  double *activity;
  bvar_t *heap;
  int32_t *heap_index;
  uint32_t heap_last;
  double act_increment;
  double inv_act_decay;
} var_heap_t;




/*****************
 *  TRAIL STACK  *
 ****************/

/*
 * Push/pop stack:
 * - for each base_level: we keep the number of variables and unit-clauses
 * + the size of vectors binary_clauses and problem_clauses on entry to that level,
 * + the propagation pointers at that point.
 * - we store prop_ptr to support sequences such as
 *     assert unit clause l1;
 *     push;
 *     assert unit clause l2;
 *     search;
 *     pop;
 *     assert more clauses;
 *     search
 * - on entry to the first search, no boolean propagation has been done yet, prop_ptr = 0
 * - after pop, we need to restore prop_ptr to 0, otherwise anything implied by
 *   the unit clause l1 may be missed
 */
typedef struct trail_s {
  uint32_t nvars;
  uint32_t nunits;
  uint32_t nbins;
  uint32_t nclauses;
  uint32_t prop_ptr;
  uint32_t theory_ptr;
} trail_t;

typedef struct trail_stack_s {
  uint32_t size;
  uint32_t top;
  trail_t *data;
} trail_stack_t;

#define DEFAULT_DPLL_TRAIL_SIZE 20
#define MAX_DPLL_TRAIL_SIZE (UINT32_MAX/sizeof(trail_t))





/****************
 *  ATOM TABLE  *
 ***************/

/*
 * The atom table maps boolean variables to atoms
 *
 * For every boolean variable v:
 * - has_atom[v]: one bit = 1 if v has an associated atom, 0 otherwise
 * - atom[v] = pointer to the atom attached to v (not initialized if has_atom[v] == 0)
 * - size = size of array atom = number of bits in has_atom vector
 *
 * Using the extra bitvector has_atom improves performance
 * if there are a lot of variables but few atoms.
 *
 * Initially, size is 0 and nothing is allocated.
 * The table is extended if needed when attach_atom is called.
 */
typedef struct atom_table_s {
  byte_t *has_atom;
  void **atom;
  uint32_t size;
  uint32_t natoms; // for statistics
} atom_table_t;


#define MAX_ATOM_TABLE_SIZE (UINT32_MAX/8)



/********************
 *  THEORY SOLVER   *
 *******************/

/*
 * A theory solver must implement the following functions
 *
 * 1) void start_internalization(void *solver)
 *    - this is called to signal the solver that new assertions will
 *      be added at the base level
 *    - assert_atom/propagate may be called after this and before
 *      start_search to perform base-level simplifications.
 *
 * 2) void start_search(void *solver)
 *    - this is called when the search starts to enable solver to perform
 *      initializations and simplifications. If solver detects an inconsistency
 *      at this point, it must record it using record_theory_conflict (possibly
 *      with an empty conflict).
 *
 * 3) bool assert_atom(void *solver, void *atom, literal_t l)
 *    - this is called when literal l is assigned and var_of(l) has an atom attached.
 *      if l has positive sign, then atom is true
 *      if l has negative sign, then atom is false
 *    - the function must return false if a conflict is detected and
 *      record the conflict (as a conjunction of false literals) by
 *      calling record_theory_conflict
 *    - it must return true if no conflict is detected
 *
 * 4) bool propagate(void *solver)
 *    - this is called at the end of each propagation round to check whether
 *      all atoms asserted so far are consistent.
 *    - the function must return true if no conflict is detected
 *    - it must return false if a conflict is detected and record that conflict
 *
 * 5) fcheck_code_t final_check(void *solver)
 *    - this is called when smt_final_check is invoked (when all boolean
 *      variables are assigned)
 *    - final_check must return one of the following codes:
 *       FCHECK_CONTINUE: if more processing is required
 *       FCHECK_SAT: if the solver agrees that the problem is SAT
 *       FCHECK_UNKNOWN: if the solver is incomplete and cannot determine
 *         whether the problem is SAT
 *    - if the solver returns FCHECK_CONTINUE, it must have done one of
 *      the following things:
 *      - record a conflict (by calling record_theory_conflict)
 *      - create lemmas or atoms in the core
 *    - if the theory solver returns FCHECK_SAT or FCHECK_UNKNOWN, the search
 *      stops and the solver smt-core status is set to SAT or UNKNOWN.
 *
 * 6) void expand_explanation(void *solver, literal_t l, void *expl, ivector_t *v)
 *    - this is called during conflict resolution to deal with literals propagated
 *      by the theory solver.
 *    - solver can propagate literals by calling propagate_literal(core, l, expl)
 *      where l is a literal, expl is an abstract explanation object (void *)
 *    - if l is involved in conflict resolution later on, then expl must be expanded
 *      into a conjunction of literals l_1 ... l_n such that
 *          (l_1 and .... and l_n) implies l
 *      holds in the theory.
 *    - function expand_explanation(solver, l, expl, v) must perform the expansion
 *      l is an implied literal, with expl as generic antecedent.
 *      v is a vector to store the result
 *      the literals l1 ... l_n must be appended to vector v (without resetting v)
 *
 * 7) void increase_decision_level(void *solver)
 *    - this is called whenever a new decision level is entered, i.e., within
 *      any call to decide_literal(core, l)
 *    - the theory solver must keep track of this so that it can backtrack to the
 *      right point later on
 *
 * 8) void backtrack(void *solver, uint32_t back_level)
 *    - this is called whenever the core backtracks to back_level. The theory
 *      solver must undo all assertions made at decision levels > back_level.
 *
 * 9) literal_t select_polarity(void *solver, void *atom, literal_t l)
 *    - optional support for a solver-specific splitting heuristic:
 *    - l is a decision literal attached to a solver's atom.
 *    - the function must decide between setting l true or false
 *    - it must return either l  (set l := true) or (not l)  (set l := false)
 *
 * 10) void delete_atom(void *solver, void *atom)
 *    - this is called to inform solver that the core has removed a variable v
 *      with atom attached from its set of variables. This is intended to
 *      support a minimal form of garbage collection (stack based).
 *    - removal of variables occurs if a checkpoint has been set at a decision level k,
 *      and the core backtracks to a level <= k.
 *
 * 11) void end_atom_deletion(void *solver)
 *    - this is called when the core has finished deleting a group of atoms, to
 *      enable solver to take appropriate cleanup actions.
 *
 * 12) void push(void *solver)
 *     void pop(void *solver)
 *     void reset(void *solver)
 *
 * 13) void clear(void *solver)
 *   - new function added June 12, 2014. Whenever smt_clear is called
 *     the smt_core propagates it to the theory solver by calling this function.
 *     Smt_clear is called in a state where solver->status is SAT or UNKNOWN,
 *     the theory solver must restore its internal state to what it was on entry
 *     to the previous call to final_check (this should be used by the Egraph
 *     to remove all temporary equalities introduced during model reconciliation).
 *
 *
 * Functions deleted_atom, end_deletion, push, pop, and reset are
 * optional. The corresponding function pointer in theory_solver_t
 * object may be set to NULL. This will work provided the features
 * that require them are never used (i.e., "fire-and-forget" mode of
 * operation, and no calls to checkpoint).
 *
 * The theory solver can propagate literal assignments to the core, and
 * add clauses, atoms, and literals on the fly.
 * - literal propagation is performed by calling propagate_literal(core, ...)
 *   this function can be called only from
 *      th->start_search
 *      th->propagate
 * - on-the-fly literals, atoms, and lemmas can be created from within
 *      th->start_search
 *      th->propagate
 *      th->backtrack
 * - it's not safe to call propagate_literal or to add clauses or literals
 *   within th->assert_atom
 */

// Codes for final_check
typedef enum fcheck_code {
  FCHECK_CONTINUE,
  FCHECK_SAT,
  FCHECK_UNKNOWN,
} fcheck_code_t;


// Signatures for all these functions
typedef void (*start_intern_fun_t)(void *solver);
typedef void (*start_fun_t)(void *solver);
typedef bool (*assert_fun_t)(void *solver, void *atom, literal_t l);
typedef bool (*propagate_fun_t)(void *solver);
typedef fcheck_code_t (*final_check_fun_t)(void *solver);
typedef void (*expand_expl_fun_t)(void *solver, literal_t l, void *expl, ivector_t *v);
typedef void (*increase_level_fun_t)(void *solver);
typedef void (*backtrack_fun_t)(void *solver, uint32_t back_level);
typedef literal_t (*select_pol_fun_t)(void *solver, void *atom, literal_t l);
typedef void (*del_atom_fun_t)(void *solver, void *atom);
typedef void (*end_del_fun_t)(void *solver);
typedef void (*push_fun_t)(void *solver);
typedef void (*pop_fun_t)(void *solver);
typedef void (*reset_fun_t)(void *solver);
typedef void (*clear_fun_t)(void *solver);


/*
 * Solver descriptor: 2008/02/11: we now split it into
 * - a control interface
 * - an SMT-specific interface
 *
 * The control interface is generic and is also used for communication
 * form the egraph to other theory solvers.
 *
 * The SMT-specific interface needs to be implemented only by solvers
 * that can interface directly with the core. It includes the solver
 * operations that have to do with atoms and explanations.
 */
typedef struct th_ctrl_interface_s {
  start_intern_fun_t   start_internalization;
  start_fun_t          start_search;
  propagate_fun_t      propagate;
  final_check_fun_t    final_check;
  increase_level_fun_t increase_decision_level;
  backtrack_fun_t      backtrack;
  push_fun_t           push;
  pop_fun_t            pop;
  reset_fun_t          reset;
  clear_fun_t          clear;
} th_ctrl_interface_t;

typedef struct th_smt_interface_s {
  assert_fun_t         assert_atom;
  expand_expl_fun_t    expand_explanation;
  select_pol_fun_t     select_polarity;
  del_atom_fun_t       delete_atom;
  end_del_fun_t        end_atom_deletion;
} th_smt_interface_t;




/*****************
 *  LEMMA QUEUE  *
 ****************/

/*
 * By lemmas we mean clauses that are created on the fly by the theory solver.
 * These new clauses may cause a conflict or require backtracking so they have
 * to be processed and added carefully. To do this, we do not immediately add
 * lemmas to the clause database but we copy them into an auxiliary queue, for
 * processing when the theory solver returns.
 *
 * Each block in the queue is an array of literals. The content of this array
 * is a set of lemmas separated by end markers (null_literal).
 * - for a block b:
 *   b->data is an array of b->size literals
 *   the lemmas are stored in b->data[0 ... n-1] where n = b->ptr
 *
 * The queue itself is an array of blocks divided in three segments:
 * - for 0 <= i < free_block: blocks currently in use (i.e., that contain lemmas)
 *   for 0 <= i < free_block-1, block[i] is full
 *   if free_block > 0 then i = free_block-1 = index of the current block
 *            where new lemmas are copied,  if space is available
 * - for free_block <= i < nblocks: allocated but unused blocks (all are empty).
 * - for nblocks <= i < capacity: not allocated (block[i] is garbage/not a valid pointer).
 */
typedef struct lemma_block_s {
  uint32_t size;     // size of data array
  uint32_t ptr;      // index of the first free element in data
  literal_t data[0];
} lemma_block_t;

typedef struct lemma_queue_s {
  uint32_t capacity;   // size of block array
  uint32_t nblocks;    // number of non-null blocks
  uint32_t free_block;  // start of the free block segment
  lemma_block_t **block;
} lemma_queue_t;


/*
 * Default and max size of a block
 */
#define DEF_LEMMA_BLOCK_SIZE 1000
#define MAX_LEMMA_BLOCK_SIZE (UINT32_MAX/4)

/*
 * Max number of blocks in the queue
 */
#define MAX_LEMMA_BLOCKS (UINT32_MAX/8)

/*
 * Number of blocks for the first allocation
 */
#define DEF_LEMMA_BLOCKS 4

/*
 * Max number of empty blocks kept in the queue
 * after it's reset
 */
#define LEMMA_BLOCKS_TO_KEEP 4


/*****************
 *  CHECKPOINTS  *
 ****************/

/*
 * THIS IS EXPERIMENTAL AND UNTESTED
 *
 * We use a stack-based mechanism for deleting irrelevant atoms,
 * variables. and clauses constructed during the search. This is done
 * via a stack of checkpoints. Each checkpoint records a decision
 * level and the number of boolean variables on entry to that
 * level. The garbage collection mechanism attempts to delete any new
 * variables, atoms, and clauses created at levels > d when the solver
 * backtracks to a lower decision level. Nothing is deleted if one or
 * more atoms created at levels > d is now assigned at a level <= d,
 * which may happen during conflict resolution. In such a case, the
 * checkpoint is kept and deletion will be tried again later.
 *
 * This can be used as follows:
 * - set a checkpoint before calling decide (current decision_level = d,
 *   current number of variables  = n)
 * - variables, atoms, and clauses can be created on-the-fly
 * - when the solver backtracks to decision_level <= d, it removes all
 *   boolean variables created since the checkpoint was set. This restores
 *   the solver to n variables.
 * - any clause that contain one of the deleted variables is also deleted
 * - if a deleted variable is attached to an atom, then the theory solver
 *   is notified via the deleted_atom function
 */

typedef struct checkpoint_s {
  uint32_t dlevel;
  uint32_t nvars;
} checkpoint_t;

typedef struct checkpoint_stack_s {
  uint32_t size;
  uint32_t top;
  checkpoint_t *data;
} checkpoint_stack_t;


#define DEF_CHECKPOINT_STACK_SIZE 10
#define MAX_CHECKPOINT_STACK_SIZE (UINT32_MAX/sizeof(checkpoint_t))




/***********************
 *  STATISTICS RECORD  *
 **********************/

/*
 * Search statistics
 */
typedef struct dpll_stats_s {
  uint32_t restarts;         // number of restarts
  uint32_t simplify_calls;   // number of calls to simplify_clause_database
  uint32_t reduce_calls;     // number of calls to reduce_learned_clause_set
  uint32_t remove_calls;     // number of calls to remove_irrelevant_learned_clauses

  uint64_t decisions;        // number of decisions
  uint64_t random_decisions; // number of random decisions
  uint64_t propagations;     // number of boolean propagations
  uint64_t conflicts;        // number of conflicts/backtrackings

  uint32_t th_props;         // number of theory propagation
  uint32_t th_prop_lemmas;   // number of propagation/explanation turned into clauses
  uint32_t th_conflicts;     // number of calls to record_conflict
  uint32_t th_conflict_lemmas;  // number of theory conflicts turned into clauses

  uint64_t prob_literals;     // number of literals in problem clauses
  uint64_t learned_literals;  // number of literals in learned clauses

  uint64_t prob_clauses_deleted;     // number of problem clauses deleted
  uint64_t learned_clauses_deleted;  // number of learned clauses deleted
  uint64_t bin_clauses_deleted;      // number of binary clauses deleted

  uint64_t literals_before_simpl;
  uint64_t subsumed_literals;
} dpll_stats_t;



/*********************
 *  SMT SOLVER CORE  *
 ********************/

/*
 * Status: the codes are now defined in yices_types.h
 * - idle is the initial status
 * - addition of clauses may cause status to become unsat
 *   otherwise it remains idle until search starts.
 * - status is switched to searching when search starts
 * - the search can be interrupted, or it completes with
 *   status = SAT or UNSAT or UNKNOWN (unknown may be returned
 *   if the solver is incomplete and does not find an inconsistency)
 * - if status is INTERRUPTED, SAT, or UNKNOWN, then push or clause
 *   addition returns status to idle.
 * - if status is UNSAT, reset or pop must be called before any
 *   other operation. This also restores the state to idle.
 */
#if 0
// this type is now imported from yices_types.h
typedef enum smt_status {
  STATUS_IDLE,
  STATUS_SEARCHING,
  STATUS_UNKNOWN,
  STATUS_SAT,
  STATUS_UNSAT,
  STATUS_INTERRUPTED,
  STATUS_ERROR, // not used by the context operations/only by yices_api
} smt_status_t;
#endif

#define NUM_SMT_STATUSES (STATUS_ERROR+1)

/*
 * Optional features: stored as bits in the solver option_flag
 * - clean_interrupt: if this bit is set, the current state is saved
 *   on a call to start_search. This allows the solver to return
 *   to a clean state if stop_search() is called.
 * - push_pop: if this bit is set, push and pop are supported, otherwise
 *   they are not.
 * These options are set when the solver is created by giving a mode
 * - INTERACTIVE enables both clean_interrupt and push_pop
 * - PUHSPOP enables push_pop but disables clean_interrupt
 * - BASIC disables clean_interrupt and push_pop
 *
 * Disabling push_pop and clean_interrupt results in more thorough clause
 * simplification at the base_level, by ensuring base_level is always 0.
 * This should improve performance.
 */
typedef enum smt_mode {
  SMT_MODE_BASIC,
  SMT_MODE_PUSHPOP,
  SMT_MODE_INTERACTIVE,
} smt_mode_t;

// bit masks
#define CLEAN_INTERRUPT_MASK (0x1)
#define PUSH_POP_MASK        (0x2)


/*
 * The clause database is divided into:
 *  - a vector of problem clauses
 *  - a vector of learned clauses
 * unit and binary clauses are stored implicitly:
 * - unit clauses are just literals in the assignment stack
 * - binary clauses are stored in the binary watch vectors
 *
 * To support push/pop, we keep a copy of all binary clauses added at base_level>0.
 *
 * Propagation structures: for every literal l
 * - bin[l] = literal vector for binary clauses
 * - watch[l] = list of clauses where l is a watched literal
 *   (i.e., clauses where l occurs in position 0 or 1)
 * - optional: end_watch[l] = pointer to the last element in the watch list of l
 *   end_watch is used if USE_END_WATCH is set a compilation time
 *
 * For every variable x between 0 and nb_vars - 1
 * - antecedent[x]: antecedent type and value
 * - level[x]: decision level (only meaningful if x is assigned)
 * - mark[x]: 1 bit used in UIP computation
 * - value[x] = current assignment
 *   value ranges from -1 to nbvars - 1 so that value[x] exists when x = null_bvar = -1
 *   value[-1] is always set to VAL_UNDEF_FALSE
 *
 * Assignment stack
 *
 * Variable heap
 *
 * Conflict data:
 * - inconsistent is set to true when a conflict is detected
 * - there are three types of conflicts:
 *   - a binary clause { l1, l2 } is false in the current assignment
 *   - a non-binary clause cl = { l1, ..., l_n } is false
 *   - the theory solver reports a conflict a = { l1, ..., l_n}
 * - in all three cases, conflict points to an array of false literals,
 *   terminated by either end_clause/null_literal or end_learned.
 * - false_clause and theory_conflict are set to indicate the conflict type.
 * - for a binary clause:
 *      l1, l2, end_clause are copied into the auxiliary array conflict_buffer
 *      conflict points to conflict_buffer
 *      theory_conflict is false
 *      false_clause is NULL
 * - for a non-binary clause conflict cl
 *      conflict points to cl->cl
 *      theory_conflict is false
 *      false_clause is set to cl
 * - for a theory conflict a:
 *      conflict is set to a
 *      theory_conflict is true
 *      false_clause is NULL
 *
 * Theory-clause caching heuristics:
 * - optionally, small theory conflicts and theory explanations can be turned
 *   into learned clauses (as a side effect of conflict resolution).
 * - this feature is enabled by setting the flag theory_cache to true
 * - if th_cache is true, th_cache_cl_size specifies which
 *   conflicts/explanations are considered (i.e., if they contain at most
 *   th_cache_cl_size literals, they are turned into clauses).
 *
 * Solving with assumptions:
 * - we can optionally solve the problem under assumptions
 * - the assumptions literals l_1 .... l_n
 * - we store them in an assumptions array
 * - we want to force the search tree to explore only the branches
 *   where l_1  ... l_n are all true
 * - to do this, we force the n first decisions to be
 *   l_1 = true,   ..., l_n = true.
 * - there's a conflict when we can't make such a decision
 *   (i.e., l_i is forced to false by previous assumptions).
 *
 * We can then build an unsat core by keeping track of this l_i.
 * We store it in core->bad_assumption. If there's no conflict,
 * code->bad_assumption is null_literal.
 */
typedef struct smt_core_s {
  /* Theory solver */
  void *th_solver;                 // pointer to the theory solver
  th_ctrl_interface_t th_ctrl;     // control functions
  th_smt_interface_t th_smt;       // SMT-specific operations
  bool bool_only;                  // true means no theory propagation required

  /* Status */
  int32_t status;

  /* Option flags */
  uint32_t option_flag;

  /* Problem size */
  uint32_t nvars;             // Number of variables
  uint32_t nlits;             // Number of literals = twice the number of variables
  uint32_t vsize;             // Size of the variable arrays (>= nb_vars)
  uint32_t lsize;             // Size of the literal arrays (>= nb_lits)

  uint32_t nb_clauses;        // Number of clauses with at least 3 literals (problem + learned clauses)
  uint32_t nb_prob_clauses;   // Number of (non-hidden) problem clauses
  uint32_t nb_bin_clauses;    // Number of binary clauses
  uint32_t nb_unit_clauses;   // Number of unit clauses

  /* Counters for simplify DB */
  uint32_t simplify_bottom;     // stack top pointer after last simplify_clause_database
  uint64_t simplify_props;      // value of propagation counter at that point
  uint64_t simplify_threshold;  // number of propagations before simplify is enabled again

  uint64_t aux_literals;       // temporary counter used by simplify_clause
  uint32_t aux_clauses;        // temporary counter used by simplify_clause

  /* Current decision level */
  uint32_t decision_level;
  uint32_t base_level;         // Incremented on push/decremented on pop

  /* Activity increments and decays for learned clauses */
  float cla_inc;             // Clause activity increment
  float inv_cla_decay;       // Inverse of clause decay (e.g., 1/0.999)

  /* Randomness parameter */
  uint32_t prng;             // state of the pseudo random number generator
  uint32_t scaled_random;    // 0x1000000 * random_factor

  /* Theory cache parameters */
  bool th_cache_enabled;      // true means caching enabled
  uint32_t th_cache_cl_size;  // max. size of cached clauses

  /* Conflict data */
  bool inconsistent;
  bool theory_conflict;
  literal_t conflict_buffer[4];
  literal_t *conflict;
  clause_t *false_clause;
  uint32_t th_conflict_size;  // number of literals in theory conflicts

  /* Assumptions */
  bool has_assumptions;
  uint32_t num_assumptions;
  uint32_t assumption_index;
  const literal_t *assumptions;
  literal_t bad_assumption;

  /* Auxiliary buffers for conflict resolution */
  ivector_t buffer;
  ivector_t buffer2;

  /* Buffer for expanding theory explanations */
  ivector_t explanation;

  /* Clause database */
  clause_t **problem_clauses;
  clause_t **learned_clauses;

  ivector_t binary_clauses;  // Keeps a copy of binary clauses added at base_levels>0

  /* Variable-indexed arrays (of size vsize) */
  uint8_t *value;
  antecedent_t *antecedent;
  uint32_t *level;
  byte_t *mark;        // bitvector: for conflict resolution

  /* Literal-indexed arrays (of size lsize) */
  literal_t **bin;   // array of literal vectors
  link_t *watch;     // array of watch lists

  /* Stack/propagation queue */
  prop_stack_t stack;

  /* Heap */
  var_heap_t heap;

  /* Lemma queue */
  lemma_queue_t lemmas;

  /* Statistics */
  dpll_stats_t stats;

  /* Atom table */
  atom_table_t atoms;

  /* Table of logical gates */
  gate_table_t gates;

  /* Push/pop stack */
  trail_stack_t trail_stack;

  /* Checkpoints */
  checkpoint_stack_t checkpoints;
  bool cp_flag;  // set true when backtracking. false when checkpoints are added

  /* EXPERIMENTAL (default to NULL) */
  booleq_table_t *etable;

  /* Tracer object (default to NULL) */
  tracer_t *trace;

  bool interrupt_push;
} smt_core_t;


/*
 * Initial size of buffer, buffer2, and explanation vectors
 */
#define DEF_LBUFFER_SIZE 40


/*
 * Default values for the clause/variable activity increment
 * - before smt_process returns, all activities are multiplied
 *   by the decay factor
 * - when a variable or clause activity increases above the
 *   activity threshold, then all activities are rescaled to
 *   prevent overflow
 */
#define VAR_DECAY_FACTOR               0.95
#define VAR_ACTIVITY_THRESHOLD         (1e100)
#define INV_VAR_ACTIVITY_THRESHOLD     (1e-100)
#define INIT_VAR_ACTIVITY_INCREMENT    1.0

#define CLAUSE_DECAY_FACTOR            (0.999F)
#define CLAUSE_ACTIVITY_THRESHOLD      (1e20F)
#define INV_CLAUSE_ACTIVITY_THRESHOLD  (1e-20F)
#define INIT_CLAUSE_ACTIVITY_INCREMENT (1.0F)


/*
 * Parameters for removing irrelevant learned clauses
 * (zchaff-style).
 */
#define TAIL_RATIO 16
#define HEAD_ACTIVITY 500
#define TAIL_ACTIVITY 10
#define HEAD_RELEVANCE 6
#define TAIL_RELEVANCE 45


/*
 * Default random_factor = 2% of decisions are random (more or less)
 * - the heuristic generates a random 24 bit integer
 * - if that number is <= random_factor * 2^24, then a random variable
 *   is chosen
 * - so we store random_factor * 2^24 = random_factor * 0x1000000 in
 *   the scaled_random field of an smt_core
 */
#define VAR_RANDOM_FACTOR 0.02F

// mask to extract 24 bits out of an unsigned 32bit integer
#define VAR_RANDOM_MASK  ((uint32_t)0xFFFFFF)
#define VAR_RANDOM_SCALE (VAR_RANDOM_MASK+1)




/************************
 *  GENERIC OPERATIONS  *
 ***********************/

/*
 * Initialize an smt solver
 * - n = initial vsize = size of the variable-indexed arrays
 * - th = theory solver
 * - ctrl = descriptor of control functions for th
 * - smt = descriptor of the SMT functions for th
 * - mode = to select optional features
 * This creates the predefined "constant" variable and the true/false literals
 *
 * The clause and variable activity increments, and the randomness
 * parameters are set to their default values
 */
extern void init_smt_core(smt_core_t *s, uint32_t n, void *th,
                          th_ctrl_interface_t *ctrl, th_smt_interface_t *smt,
                          smt_mode_t mode);


/*
 * Set the bool_only flag (this an optimization for pure bitvector problems)
 * - if this flag is set, there's no theory propagation
 */
static inline void smt_core_set_bool_only(smt_core_t *s) {
  s->bool_only = true;
}

/*
 * Replace the theory solver and interface descriptors
 * - this can used provided no atom/clause has been added yet
 */
extern void smt_core_reset_thsolver(smt_core_t *s, void *th, th_ctrl_interface_t *ctrl,
				    th_smt_interface_t *smt);


/*
 * Delete: free all allocated memory
 */
extern void delete_smt_core(smt_core_t *s);


/*
 * Reset: remove all variables, atoms, and clauses
 * - also calls reset on the attached theory solver
 */
extern void reset_smt_core(smt_core_t *s);


/*
 * Attach a tracer object:
 * - s->trace must be NULL
 */
extern void smt_core_set_trace(smt_core_t *s, tracer_t *tracer);


/*
 * EXPERIMENTAL: create the etable
 */
extern void smt_core_make_etable(smt_core_t *s);


/*
 * EXPERIMENTAL: record l = (xor a b)
 * - call smt_core_make_etable first
 */
extern void smt_core_record_xor_def(smt_core_t *s, literal_t l, literal_t a, literal_t b);



/*
 * Start a new base level
 * - keep track of the current set of variables, atoms, and clauses
 * - subsequent call to smt_pop restore s to that state
 * Push must not be called if a search is under way or if s has status UNSAT or INTERRUPTED
 * or if push_pop is disabled.
 *
 * If s->status is UNKNOWN or SAT, then the current boolean assignment is cleared
 * and s->status is reset to IDLE.
 */
extern void smt_push(smt_core_t *s);


/*
 * Restore to the saved state on top of the trail_stack
 * - remove all learned_clauses
 * - remove all clauses, variable, and atoms created at the current base_level
 * - reset status to IDLE
 * - must not be called if the trail_stack is empty (no push) or if
 *   status is SEARCHING or INTERRUPTED
 */
extern void smt_pop(smt_core_t *s);


/*
 * Set the activity increment parameters
 * - decay_factor must be a floating point number between 0 and 1.0
 */
extern void set_var_decay_factor(smt_core_t *s, double factor);
extern void set_clause_decay_factor(smt_core_t *s, float factor);

/*
 * Set the randomness parameter used by the default variable
 * selection heuristic: random_factor must be a floating point
 * number between 0 and 1.0.
 */
extern void set_randomness(smt_core_t *s, float random_factor);


/*
 * Set the pseudo random number generator seed
 */
extern void set_random_seed(smt_core_t *s, uint32_t seed);


/*
 * Activate theory-clause caching
 * - cl_size = max size of clauses to be cached
 */
static inline void enable_theory_cache(smt_core_t *s, uint32_t cl_size) {
  s->th_cache_enabled = true;
  s->th_cache_cl_size = cl_size;
}

/*
 * Disable theory-clause caching
 */
static inline void disable_theory_cache(smt_core_t *s) {
  s->th_cache_enabled = false;
}


/*
 * Read the current decision level
 */
static inline uint32_t smt_decision_level(smt_core_t *s) {
  return s->decision_level;
}

/*
 * Read the current base level
 */
static inline uint32_t smt_base_level(smt_core_t *s) {
  return s->base_level;
}

/*
 * Read the status
 */
static inline smt_status_t smt_status(smt_core_t *s) {
  return s->status;
}

/*
 * Read the heuristic parameters
 */
static inline double var_decay_factor(smt_core_t *s) {
  return 1/s->heap.inv_act_decay;
}

static inline double clause_decay_factor(smt_core_t *s) {
  return 1/s->inv_cla_decay;
}

static inline double randomness_factor(smt_core_t *s) {
  return ((double) s->scaled_random)/ VAR_RANDOM_SCALE;
}



/*
 * Read the search statistics
 */
static inline uint32_t num_restarts(smt_core_t *s) {
  return s->stats.restarts;
}

static inline uint32_t num_simplify_calls(smt_core_t *s) {
  return s->stats.simplify_calls;
}

static inline uint32_t num_reduce_calls(smt_core_t *s) {
  return s->stats.reduce_calls;
}

static inline uint32_t num_remove_calls(smt_core_t *s) {
  return s->stats.remove_calls;
}

static inline uint64_t num_decisions(smt_core_t *s) {
  return s->stats.decisions;
}

static inline uint64_t num_random_decisions(smt_core_t *s) {
  return s->stats.random_decisions;
}

static inline uint64_t num_propagations(smt_core_t *s) {
  return s->stats.propagations;
}

static inline uint64_t num_conflicts(smt_core_t *s) {
  return s->stats.conflicts;
}

static inline uint32_t num_theory_conflicts(smt_core_t *s) {
  return s->stats.th_conflicts;
}

static inline uint32_t num_theory_propagations(smt_core_t *s) {
  return s->stats.th_props;
}


/*
 * Read the size statistics
 */
static inline uint32_t num_vars(smt_core_t *s) {
  return s->nvars;
}

static inline uint32_t num_atoms(smt_core_t *s) {
  return s->atoms.natoms;
}

static inline uint32_t num_literals(smt_core_t *s) {
  return s->nlits;
}

static inline uint32_t num_prob_clauses(smt_core_t *s) {
  return get_cv_size(s->problem_clauses);
}

static inline uint64_t num_prob_literals(smt_core_t *s) {
  return s->stats.prob_literals;
}

// this is either 0 or 1
static inline uint32_t num_empty_clauses(smt_core_t *s) {
  return s->inconsistent;
}

static inline uint32_t num_unit_clauses(smt_core_t *s) {
  return s->nb_unit_clauses;
}

static inline uint32_t num_binary_clauses(smt_core_t *s) {
  return s->nb_bin_clauses;
}

static inline uint32_t num_learned_clauses(smt_core_t *s) {
  return get_cv_size(s->learned_clauses);
}

static inline uint64_t num_learned_literals(smt_core_t *s) {
  return s->stats.learned_literals;
}

// all clauses
static inline uint32_t num_clauses(smt_core_t *s) {
  return num_empty_clauses(s) + num_unit_clauses(s) + num_binary_clauses(s) +
    num_prob_clauses(s) + num_learned_clauses(s);
}

// average size of the learned clauses
extern double avg_learned_clause_size(smt_core_t *core);




/************************************
 *  VARIABLES, LITERALS, AND ATOMS  *
 ***********************************/

/*
 * Create a fresh variable and return its index
 * - the index is x = s->nvars
 *
 * Initialization:
 * - antecedent[x] = NULL
 * - level[x] not initialized
 * - mark[x] = 0
 * - polarity[x] = 0 (negative polarity preferred)
 * - activity[x] = 0 (in heap)
 *
 * For l=pos_lit(x) or neg_lit(x):
 * - value[l] = VAL_UNDEF
 * - bin[l] = NULL
 * - watch[l] = NULL
 */
extern bvar_t create_boolean_variable(smt_core_t *s);

/*
 * Add n fresh boolean variables: the new indices are allocated starting
 * from s->nvars (i.e., if s->nvars == v before the call, the
 * new variables have indices v, v+1, ... v+n-1).
 */
extern void add_boolean_variables(smt_core_t *s, uint32_t n);

/*
 * Attach atom a to boolean variable x
 * - x must not have an atom attached already
 */
extern void attach_atom_to_bvar(smt_core_t *s, bvar_t x, void *atom);

/*
 * Remove atom attached to x (no effect if x doesn't have an atom)
 */
extern void remove_bvar_atom(smt_core_t *s, bvar_t x);


/*
 * Check whether x has an atom attached
 */
extern bool bvar_has_atom(smt_core_t *s, bvar_t x);


/*
 * Get the atom attached to x (NULL if x has no atom attached)
 */
extern void *bvar_atom(smt_core_t *s, bvar_t x);


/*
 * Faster than bvar_atom, but requires bvar_has_atom(s, x) to be true
 */
static inline void *get_bvar_atom(smt_core_t *s, bvar_t x) {
  assert(bvar_has_atom(s, x));
  return s->atoms.atom[x];
}


/*
 * Antecedent of x
 */
static inline antecedent_t get_bvar_antecedent(smt_core_t *s, bvar_t x) {
  assert(0 <= x && x < s->nvars);
  return s->antecedent[x];
}


/*
 * Set the initial activity of variable x.
 * This determines the initial variable ordering in the decision heuristics.
 * By default, all variables have the same initial activity, namely, 0.0
 */
extern void set_bvar_activity(smt_core_t *s, bvar_t x, double a);

/*
 * Read variable current activity
 */
static inline double get_bvar_activity(smt_core_t *s, bvar_t x) {
  assert(0 <= x && x < s->nvars);
  return s->heap.activity[x];
}



/*************************
 *  MODEL CONSTRUCTION   *
 ************************/

/*
 * Check whether variable x is assigned
 */
static inline bool bvar_is_assigned(const smt_core_t *s, bvar_t x) {
  assert(0 <= x && x < s->nvars);
  return bval_is_def(s->value[x]);
}

static inline bool bvar_is_unassigned(const smt_core_t *s, bvar_t x) {
  assert(0 <= x && x < s->nvars);
  return bval_is_undef(s->value[x]);
}

/*
 * Same thing for literal l
 */
static inline bool literal_is_assigned(const smt_core_t *s, literal_t l) {
  return bvar_is_assigned(s, var_of(l));
}

static inline bool literal_is_unassigned(const smt_core_t *s, literal_t l) {
  return bvar_is_unassigned(s, var_of(l));
}


/*
 * Read the value assigned to variable x at the current decision level.
 * This can be used to build a model if s->status is SAT (or UNKNOWN).
 */
static inline bval_t bvar_value(const smt_core_t *s, bvar_t x) {
  assert(0 <= x &&  x < s->nvars);
  return s->value[x];
}


/*
 * Read the value assigned to a variable x at the base level
 * - if x is not assigned at the base level, this returns the
 *   preferred value (either VAL_UNDEF_FALSE or VAL_UNDEF_TRUE)
 */
static inline bval_t bvar_base_value(const smt_core_t *s, bvar_t x) {
  bval_t v;
  assert(0 <= x && x < s->nvars);
  v = s->value[x];
  if (s->level[x] > s->base_level) {
    v &= 1; // clear bit 1, keep bit 0
    assert(bval_is_undef(v));
  }
  return v;
}

/*
 * Get the polarity bit of x = low-order bit of value[x]
 * - if x is assigned, polarity = current value (0 means true, 1 means false)
 * - if x is unassigned, polarity = preferred value
 */
static inline uint32_t bvar_polarity(const smt_core_t *s, bvar_t x) {
  assert(0 <= x && x < s->nvars);
  return (uint32_t) (s->value[x] & 1);
}


/*
 * Read the value assigned to literal l at the current decision level
 * - let x var_of(l) then
 * - if sign_of(l) = 0, val(l) = val(x)
 *   if sign_of(l) = 1, val(l) = opposite of val(x)
 * - returns VAL_UNDEF_TRUE or VAL_UNDEF_FALSE if no value is assigned.
 */
static inline bval_t literal_value(const smt_core_t *s, literal_t l) {
  assert(0 <= l && l < (int32_t) s->nlits);
  return s->value[var_of(l)] ^ sign_of_lit(l);
}

/*
 * Read the value assigned to a literal l at the base level
 * - returns VAL_UNDEF_FALSE or VAL_UNDEF_TRUE if l is not assigned at that level
 */
static inline bval_t literal_base_value(const smt_core_t *s, literal_t l) {
  assert(0 <= l && l < s->nlits);
  return bvar_base_value(s, var_of(l)) ^ sign_of_lit(l);
}


/*
 * Get all true literals in the current assignment: copy them into vector v
 * - they are stored in chronological order
 * - the constant "true_literal" is not put in v
 */
extern void collect_true_literals(smt_core_t *s, ivector_t *v);


/*
 * Get the decision literals in the current assignment: copy them into vector v
 */
extern void collect_decision_literals(smt_core_t *s, ivector_t *v);


/*
 * Import a model from an external solver
 * - this sets the value of a boolean variable b
 */
extern void set_bvar_value(smt_core_t *s, bvar_t x, bval_t val);

/*
 * Set the core status
 */
static inline void set_smt_status(smt_core_t *s, smt_status_t status) {
  s->status = status;
}

/*
 * Check whether the core is trivially SAT
 * - i.e., check whether there are no problem clauses
 */
extern bool smt_trivially_sat(smt_core_t *s);

/*
 * Search for a satisfiable assignment.
 * - stop on the first conflict and return false
 * - return true if all Boolean variables are assigned.
 * Restrictions:
 * - s->status must be SEARCHING
 * - s must be purely Boolean.
 */
extern bool smt_easy_sat(smt_core_t *s);


/*********************
 *  CLAUSE ADDITION  *
 ********************/

/*
 * Clauses are simplified before being added:
 * - literals false at the base level are removed
 * - duplicate literals are removed
 * - a clause trivially true (either because it contains complementary
 *   literals or a literal true at the base level) is ignored.
 *
 * The general form is add_clause(s, n, a) where a is an array of n literals.
 *
 * Special forms are provided for unit, binary, and ternary clauses (also
 * for the empty clause).
 *
 * Clauses can be added before the search, when s->status is STATUS_IDLE
 * or on-the-fly, when s->status is STATUS_SEARCHING.
 *
 * If s->status is SEARCHING and s->decision_level > s->base_level,
 * then the clause is a not added immediately, it's copied into the
 * lemma queue.
 */
extern void add_empty_clause(smt_core_t *s);
extern void add_unit_clause(smt_core_t *s, literal_t l);
extern void add_binary_clause(smt_core_t *s, literal_t l1, literal_t l2);
extern void add_ternary_clause(smt_core_t *s, literal_t l1, literal_t l2, literal_t l3);

extern void add_clause(smt_core_t *s, uint32_t n, literal_t *a);


/*********************************
 *  QUANTIFIER INSTANCE CLAUSES  *
 ********************************/

/*
 * Add all queued quant lemmas to the database.
 * - this may cause backtracking
 * - a conflict clause may be recorded
 * If so, conflict resolution must be called outside this function
 * Literal en is the enable associated with the quantifier instance
 */
extern void add_all_quant_lemmas(smt_core_t *s, literal_t en, ivector_t *units);

/*
 * Record the empty clause as a conflict
 * - if resolve conflict is called after this, it will do the
 * right thing (namely, see that the conflict can't be resolved).
 */
extern void record_empty_conflict(smt_core_t *s);



/******************************
 *  ACCESS TO THE GATE TABLE  *
 *****************************/

static inline gate_table_t *get_gate_table(smt_core_t *s) {
  return &s->gates;
}


/***********************
 *  SEARCH PROCEDURES  *
 **********************/

/*
 * Start a new round of assertions
 * - this is called before base_propagate or any other function
 *   creating atoms, clauses, etc.
 * - this propagates to the theory solver.
 * - the current status must be IDLE and it remains IDLE.
 */
extern void internalization_start(smt_core_t *s);


/*
 * Propagation at the base-level:
 * - the current status must be IDLE
 * - this performs one round of propagation
 * Return true if no conflict is detected, false otherwise.
 * The status is updated to UNSAT if there's a conflict.
 * It remains IDLE otherwise.
 *
 * Warning: this is called before start_search.
 */
extern bool base_propagate(smt_core_t *s);


/*
 * Prepare for the search
 * - a = optional array of assumptions
 * - n = number of assumptions
 * - a[0 ... n-1] must all be valid literals in the core
 *
 * Effect:
 * - initialize variable heap
 * - store a pointer to the assumption array
 * - set status to SEARCHING
 * - reset the search statistics counters
 * - if clean_interrupt is enabled, save the current state to
 *   enable cleanup after interrupt (this uses push)
 * The current status must be IDLE.
 */
extern void start_search(smt_core_t *s, uint32_t n, const literal_t *a);


/*
 * Stop the search:
 * - if s->status is SEARCHING, this sets status to INTERRUPTED
 *   otherwise, this has no effect.
 * - this can be called from a signal handler to interrupt the solver
 * - if clean_interrupt is enabled,  the state at start_search can be restored by
 *   calling smt_cleanup
 */
extern void stop_search(smt_core_t *s);


/*
 * Perform a (branching) decision: assign l to true
 * - s->status must be SEARCHING
 * - l must be an unassigned literal
 * - the decision level is incremented and l is pushed on the
 *   propagation stack with empty antecedent.
 */
extern void decide_literal(smt_core_t *s, literal_t l);


/*
 * Assign literal l to true with the given antecedent
 * - s->mark[v] is set if decision level = base level
 */
extern void implied_literal(smt_core_t *s, literal_t l, antecedent_t a);


/*
 * Cause a restart: backtrack to the base_level
 * - s->status must be SEARCHING
 */
extern void smt_restart(smt_core_t *s);


/*
 * Variant of restart: attempt to reuse the assignment trail
 * - find the unassigned variable x of highest activity
 * - keep all current decisions that have a higher activity than x
 */
extern void smt_partial_restart(smt_core_t *s);


/*
 * Another variant of restart: attempt to reuse the assignment trail
 * - find the unassigned variable x of highest activity
 * - keep all current decision levels that have at least one
 *   variable with a higher activity than x
 */
extern void smt_partial_restart_var(smt_core_t *s);


/*
 * Reduce the clause database by removing half the learned clauses
 * (the ones with lowest activities)
 */
extern void reduce_clause_database(smt_core_t *s);


/*
 * Reduce the clause database by remove large clauses with low activity
 * (complicated Zchaff/Berkmin-style heuristic)
 */
extern void remove_irrelevant_learned_clauses(smt_core_t *s);


/*
 * Set a checkpoint: this records the current decision_level and
 * number of variables.
 * - if the solver backtracks to this or a smaller decision level,
 *   then all variables (and atoms) created after this checkpoints
 *   are removed (well not quite!)
 * - any clause that contains a removed variable is also deleted
 */
extern void smt_checkpoint(smt_core_t *s);


/*
 * Main solving function: process until a stable state is reached
 * - a state with status UNSAT or INTERRUPTED is stable
 * - a state with status SEARCHING is stable if there's nothing
 *   to propagate and no lemmas to process, and if there's no conflict
 * - from a stable state with status SEARCHING,
 *       one can add lemmas and call process again
 *    or select a decision literal and call process again
 *    or close the state (mark it as SAT or UNKNOWN)
 *
 * smt_process executes the following code:
 *
 * repeat
 *   if there's a conflict
 *     try to resolve the conflict
 *     if we can't resolve it
 *       change status to UNSAT and exit
 *     else
 *       decay variable and clause activities
 *     endif
 *   elsif checkpoint-based garbage collection is possible
 *     do the garbage collection
 *   elsif lemmas are present then
 *     integrate them to the clause database
 *   else
 *     perform boolean and theory propagation
 *     if propagation finds no conflict and doesn't add lemmas
 *       if decision_level == base_level
 *         simplify the clause database
 *       endif
 *       exit the loop
 *     endif
 *   endif
 * end repeat
 *
 */
extern void smt_process(smt_core_t *s);


/*
 * Variant of smt_process with a conflict bound.
 *
 * After a conflict is resolved, this function checks whether the
 * total number of conflicts so far exceeds max_conflicts. If so
 * it exits.
 *
 * The returned value indicates whether this function exited in
 * a stable state or on an early exit:
 * - true means state state reached
 * - false means max_conflicts reached.
 *
 * If this function returns false, the caller can't assume that
 * it is safe to make a decision.
 */
extern bool smt_bounded_process(smt_core_t *s, uint64_t max_conflicts);


/*
 * Check for delayed theory solving:
 * - call the final_check function of the theory solver
 * - if the theory solver creates new variables or lemmas or report a conflict
 *   then smt_process is called
 * - otherwise the core status is updated to SAT or UNKNOWN and the search
 *   is done.
 */
extern void smt_final_check(smt_core_t *s);



/*
 * Propagation function for the theory solver
 * - assign l to true with the given explanation as antecedent.
 * - l must not be assigned already.
 */
extern void propagate_literal(smt_core_t *s, literal_t l, void *expl);


/*
 * For the theory solver: record a conflict (a disjunction of literals is false)
 * - a must be an array of literals terminated by end_clause (which is
 *   the same as null_literal).
 * - all literals in a must be false at the current decision level
 *
 * Warning: no copy is made. Array a should not be modified by the theory solver,
 * until the conflict is resolved.
 */
extern void record_theory_conflict(smt_core_t *s, literal_t *a);

/*
 * Variants of record_theory_conflict
 */
extern void record_empty_theory_conflict(smt_core_t *s);
extern void record_unit_theory_conflict(smt_core_t *s, literal_t l);
extern void record_binary_theory_conflict(smt_core_t *s, literal_t l1, literal_t l2);
extern void record_ternary_theory_conflict(smt_core_t *s, literal_t l1, literal_t l2, literal_t l3);


/*
 * Close the search: mark s as either SAT or UNKNOWN
 */
static inline void end_search_sat(smt_core_t *s) {
  assert(s->status == STATUS_SEARCHING || s->status == STATUS_INTERRUPTED);
  s->status = STATUS_SAT;
}

static inline void end_search_unknown(smt_core_t *s) {
  assert(s->status == STATUS_SEARCHING || s->status == STATUS_INTERRUPTED);
  s->status = STATUS_UNKNOWN;
}


/*
 * If the search was interrupted, this function
 * restores s to what it was at the start of the search.
 * - remove all learned clauses and all the lemmas, variables, and atoms created
 *   during the search.
 * - reset s->status to IDLE
 * - this must not be called if clean_interrupt is disabled.
 */
extern void smt_cleanup(smt_core_t *s);


/*
 * Clear assignment and enable addition of new clauses after a search.
 * - this can be called if s->status is UNKNOWN or SAT
 * - s->status is reset to STATUS_IDLE and the current boolean
 *   assignment is cleared (i.e., we backtrack to the current base_level)
 */
extern void smt_clear(smt_core_t *s);


/*
 * Cleanup after the search returned unsat
 * - s->status must be UNSAT.
 * - if there are assumptions, this removes them and reset s->status
 *   to STATUS_IDLE
 * - if clean_interrupt is enabled, this also restores s to its state
 *   before the search: learned clauses are deleted, lemmas, variables
 *   and atoms created during the search are deleted.
 * - if clean_interrupt is disabled and there are no assumptions,
 *   this does nothing.
 *
 * On exit, s->status is either STATUS_UNSAT (if no assumptions
 * were removed) or STATUS_IDLE (if assumptions were removed).
 */
extern void smt_clear_unsat(smt_core_t *s);



/*********************************
 *  ASSUMPTIONS AND UNSAT CORES  *
 ********************************/

/*
 * Get the next assumption for the current decision_level
 * - s->status mut be SEARCHING
 * - this scans the assumption array to search for an assumption
 *   that is not already true.
 * - returns an assumption l or null_literal if all assumptions
 *   are true (or if there are no assumptions)
 */
extern literal_t get_next_assumption(smt_core_t *s);


/*
 * Store l as a bad assumption:
 * - l must be false in s
 * - copy l in s->bad_assumption
 * - mark the context as unsat
 */
extern void save_conflicting_assumption(smt_core_t *s, literal_t l);


/*
 * Compute an unsat core:
 * - the core is stored as a list of literals in vector v:
 *   (i.e., the conjunction of these literals is unsat in the current context)
 * - s->status must be UNSAT
 * - if there are no bad_assumption, an empty core is returned
 * - otherwise the core is build by resolving the bad_assumption's antecedents
 */
extern void build_unsat_core(smt_core_t *s, ivector_t *v);



/**************************************
 *  SUPPORT FOR BRANCHING HEURISTICS  *
 *************************************/

/*
 * The default heuristic is based on variable activities +
 * randomization + the preferred polarity vector (picosat-style).
 *
 * The select...bvar functions can be used to implement other
 * heuristics.
 */

/*
 * Select an unassigned literal using the default decision heuristic:
 * - mix of activity based + randomization heuristic
 * - use the preferred polarity vector to decide between true/false
 * return null_literal if all variables are assigned.
 */
extern literal_t select_unassigned_literal(smt_core_t *s);


/*
 * Select the unassigned variable of highest activity
 * - return null_bvar if all variables are assigned
 */
extern bvar_t select_most_active_bvar(smt_core_t *s);

/*
 * Randomly pick an unassigned variable (with uniform probability)
 * - return null_bvar if all variables are assigned.
 */
extern bvar_t select_random_bvar(smt_core_t *s);

/*
 * Check whether all variables are assigned
 */
static inline bool all_variables_assigned(smt_core_t *s) {
  assert(s->stack.top <= s->nvars);
  return s->nvars == s->stack.top;
}

/*
 * Check whether all problem clauses (binary clauses + clauses with at
 * least three literals) are true in the current assignment.
 */
extern bool all_clauses_true(smt_core_t *s);


/****************************
 * UNCONSTRAINED VARIABLES  *
 ***************************/

/*
 * Record to store the set of unconstrained variables:
 * - nvars = total number of variables
 * - free = array of booleans
 * - free[x] true means that x is unconstrained (i.e., does not occur
 *   in any clause)
 */
typedef struct free_bool_vars_s {
  uint8_t *free;
  uint32_t nvars;
} free_bool_vars_t;

/*
 * Initialized fv structure:
 * - n = number of variables
 */
extern void init_free_bool_vars(free_bool_vars_t *fv, uint32_t n);

/*
 * Delete fv
 */
extern void delete_free_bool_vars(free_bool_vars_t *fv);

/*
 * Collect all the free variables in a solver s
 * - store them in fv
 * - fv must be initialized and large enough to store
 *   all the variables of s
 */
extern void collect_free_bool_vars(free_bool_vars_t *fv, const smt_core_t *s);


#endif /* __SMT_CORE_H */
