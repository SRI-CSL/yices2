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
 * BIT-VECTOR SOLVER (BASELINE)
 */

#include <assert.h>

#include "solvers/bv/bv64_intervals.h"
#include "solvers/bv/bvsolver.h"
#include "terms/bv64_constants.h"
#include "utils/hash_functions.h"
#include "utils/index_vectors.h"
#include "utils/int_partitions.h"
#include "utils/int_powers.h"
#include "utils/memalloc.h"
#include "utils/refcount_int_arrays.h"


#define TRACE 0

#define DUMP 0

#if TRACE || DUMP

#include <stdio.h>
#include <inttypes.h>

#include "api/yices_globals.h"
#include "io/term_printer.h"
#include "solvers/bv/bvsolver_printer.h"
#include "solvers/cdcl/gates_printer.h"
#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/egraph/egraph_printer.h"


static void print_solver_state(FILE *f, bv_solver_t *solver) {  
  fprintf(f, "\n--- Terms ---\n");
  print_term_table(f, __yices_globals.terms);
  fprintf(f, "\n--- Bitvector Partition ---\n");
  print_bv_solver_partition(f, solver);
  fprintf(f, "\n--- Bitvector Variables ---\n");
  print_bv_solver_vars(f, solver);
  fprintf(f, "\n--- Bitvector Atoms ---\n");
  print_bv_solver_atoms(f, solver);
  fprintf(f, "\ntotal: %"PRIu32" atoms\n", solver->atbl.natoms);
  fprintf(f, "\n--- Bitvector Bounds ---\n");
  print_bv_solver_bounds(f, solver);
  fprintf(f, "\n--- DAG ---\n");
  print_bv_solver_dag(f, solver);
  if (solver->blaster != NULL) {
    fprintf(f, "\n--- Gates ---\n");
    print_gate_table(f, solver->blaster->htbl);
  }
  fprintf(f, "\n--- Clauses ---\n");
  print_clauses(f, solver->core);
  fprintf(f, "\n");
}


#endif


#if DUMP

static void bv_solver_dump_state(bv_solver_t *solver, const char *filename);

#endif



/*****************
 *  BOUND QUEUE  *
 ****************/

/*
 * Initialize the queue: initial size = 0
 */
static void init_bv_bound_queue(bv_bound_queue_t *queue) {
  queue->data = NULL;
  queue->top = 0;
  queue->size = 0;
  queue->bound = NULL;
  queue->bsize = 0;
}


/*
 * Allocate the data array of make it 50% larger
 */
static void bv_bound_queue_extend(bv_bound_queue_t *queue) {
  uint32_t n;

  n = queue->size;
  if (n == 0) {
    n = DEF_BV_BOUND_QUEUE_SIZE;
    assert(n <= MAX_BV_BOUND_QUEUE_SIZE);
    queue->data = (bv_bound_t *) safe_malloc(n * sizeof(bv_bound_t));
    queue->size = n;

  } else {
    n += (n >> 1); // 50% larger
    assert(n > queue->size);
    if (n > MAX_BV_BOUND_QUEUE_SIZE) {
      out_of_memory();
    }
    queue->data = (bv_bound_t *) safe_realloc(queue->data, n * sizeof(bv_bound_t));
    queue->size = n;
  }
}


/*
 * Make the bound array large enough to store bound[x]
 * - x must be a variable index (between 0 and MAX_BV_BOUND_NUM_LISTS)
 * - this should be called when x >= queue->bsize
 */
static void bv_bound_queue_resize(bv_bound_queue_t *queue, thvar_t x) {
  uint32_t i, n;
  int32_t *tmp;

  assert(x >= queue->bsize);

  n = queue->bsize;
  if (n == 0) {
    n = DEF_BV_BOUND_NUM_LISTS;
  } else {
    n += (n >> 1);
    assert(n > queue->bsize);
  }

  if (n <= (uint32_t) x) {
    n = x + 1;
  }

  if (n > MAX_BV_BOUND_NUM_LISTS) {
    out_of_memory();
  }

  tmp = (int32_t *) safe_realloc(queue->bound, n * sizeof(int32_t));
  for (i=queue->bsize; i<n; i++) {
    tmp[i] = -1;
  }

  queue->bound = tmp;
  queue->bsize = n;
}


/*
 * Add a bound for variable x:
 * - id = the atom index
 */
static void bv_bound_queue_push(bv_bound_queue_t *queue, thvar_t x, int32_t id) {
  int32_t k, i;

  if (x >= queue->bsize) {
    bv_bound_queue_resize(queue, x);
    assert(x < queue->bsize);
  }

  k = queue->bound[x];
  assert(-1 <= k && k < (int32_t) queue->top);

  i = queue->top;
  if (i == queue->size) {
    bv_bound_queue_extend(queue);
  }
  assert(i < queue->size);

  queue->data[i].atom_id = id;
  queue->data[i].pre = k;
  queue->bound[x] = i;

  queue->top = i+1;
}



/*
 * Get the index of the first bound on x
 * - return -1 if there's no bound on x
 */
static inline int32_t bv_bound_for_var(bv_bound_queue_t *queue, thvar_t x) {
  int32_t k;

  k = -1;
  if (x < queue->bsize) {
    k = queue->bound[x];
    assert(-1 <= k && k < (int32_t) queue->top);
  }

  return k;
}



/*
 * Delete the queue
 */
static void delete_bv_bound_queue(bv_bound_queue_t *queue) {
  safe_free(queue->data);
  safe_free(queue->bound);
  queue->data = NULL;
  queue->bound = NULL;
}


/*
 * Empty the queue
 */
static void reset_bv_bound_queue(bv_bound_queue_t *queue) {
  uint32_t i, n;

  n = queue->bsize;
  for (i=0; i<n; i++) {
    queue->bound[i] = -1;
  }
  queue->top = 0;
}



/**********************************
 *  INTERVAL-COMPUTATION BUFFERS  *
 *********************************/

/*
 * Initialize the stack
 */
static void init_bv_interval_stack(bv_interval_stack_t *stack) {
  stack->data = NULL;
  stack->buffers = NULL;
  stack->size = 0;
  stack->top = 0;
}


/*
 * Delete: free all memory
 */
static void delete_bv_interval_stack(bv_interval_stack_t *stack) {
  uint32_t i, n;

  n = stack->size;
  if (n != 0) {
    assert(stack->data != NULL && stack->buffers != NULL);
    delete_bv_aux_buffers(stack->buffers);
    for (i=0; i<n; i++) {
      delete_bv_interval(stack->data + i);
    }
    safe_free(stack->buffers);
    safe_free(stack->data);

    stack->buffers = NULL;
    stack->data = NULL;
    stack->top = 0;
    stack->size = 0;
  }
}



/*
 * Reset: same as delete
 */
static inline void reset_bv_interval_stack(bv_interval_stack_t *stack) {
  delete_bv_interval_stack(stack);
}


/*
 * Allocate the stack (if not allocated already)
 * - use the default size
 */
static void alloc_bv_interval_stack(bv_interval_stack_t *stack) {
  uint32_t i, n;
  bv_interval_t *d;
  bv_aux_buffers_t *b;

  n = stack->size;
  if (n == 0) {
    n = DEF_BV_INTV_STACK_SIZE;
    assert(n <= MAX_BV_INTV_STACK_SIZE);
    d = (bv_interval_t *) safe_malloc(n * sizeof(bv_interval_t));
    for (i=0; i<n; i++) {
      init_bv_interval(d + i);
    }

    b = (bv_aux_buffers_t *) safe_malloc(sizeof(bv_aux_buffers_t));
    init_bv_aux_buffers(b);

    stack->data = d;
    stack->buffers = b;
    stack->size = n;
  }
}



/*
 * Get an interval object
 * - this uses a FIFO allocation model
 * - return NULL if the stack is full (fails)
 */
static bv_interval_t *get_bv_interval(bv_interval_stack_t *stack) {
  bv_interval_t *d;
  uint32_t i;

  d = NULL;
  i = stack->top;
  if (i < stack->size) {
    d = stack->data + i;
    stack->top = i+1;
  }
  return d;
}


/*
 * Free the last allocated interval object (i.e., decrement top)
 */
static inline void release_bv_interval(bv_interval_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}


/*
 * Free all the allocated intervals
 */
static inline void release_all_bv_intervals(bv_interval_stack_t *stack) {
  stack->top = 0;
}

/*
 * Get the auxiliary buffer structure
 * - alloc_bv_interval_stack must be called before this function
 */
static inline bv_aux_buffers_t *get_bv_aux_buffers(bv_interval_stack_t *stack) {
  assert(stack->size != 0 && stack->buffers != NULL);
  return stack->buffers;
}




/**********************
 *  VARIABLE QUEUES   *
 *********************/

/*
 * Initialize to the empty queue
 */
static inline void init_bv_queue(bv_queue_t *queue) {
  queue->data = NULL;
  queue->top = 0;
  queue->size = 0;
}

/*
 * Make the queue larger
 */
static void bv_queue_extend(bv_queue_t *queue) {
  uint32_t n;

  n = queue->size;
  if (n == 0) {
    // first allocation
    n = DEF_BV_QUEUE_SIZE;
    assert(n > 0 && n <= MAX_BV_QUEUE_SIZE && queue->data == NULL);
  } else {
    n += (n >> 1); // 50% large
    assert(n > queue->size);
    if (n > MAX_BV_QUEUE_SIZE) {
      out_of_memory();
    }
  }

  queue->data = (thvar_t *) safe_realloc(queue->data, n * sizeof(thvar_t));
  queue->size = n;
}


/*
 * Push x on the queue
 */
static void bv_queue_push(bv_queue_t *queue, thvar_t x) {
  uint32_t i;

  i = queue->top;
  if (i == queue->size) {
    bv_queue_extend(queue);
  }
  assert(i < queue->size);
  queue->data[i] = x;
  queue->top = i + 1;
}


/*
 * Empty the queue
 */
static inline void reset_bv_queue(bv_queue_t *queue) {
  queue->top = 0;
}


/*
 * Delete
 */
static void delete_bv_queue(bv_queue_t *queue) {
  if (queue->data != NULL) {
    safe_free(queue->data);
    queue->data = NULL;
  }
}







/********************
 *  PUSH/POP STACK  *
 *******************/

/*
 * Initialize the stack: initial size = 0
 */
static void init_bv_trail(bv_trail_stack_t *stack) {
  stack->size = 0;
  stack->top = 0;
  stack->data = NULL;
}



/*
 * Save a base level
 * - nv = number of variables
 * - na = number of atoms
 * - nb = number of bounds
 * - ns = number of select variables
 * - ndm = number of delayed mapped variables
 * - ndb = number of delayed blasted variables
 * - bb = bitblast pointer
 */
static void bv_trail_save(bv_trail_stack_t *stack, uint32_t nv, uint32_t na, uint32_t nb,
                          uint32_t ns, uint32_t ndm, uint32_t ndb, uint32_t bb) {
  uint32_t i, n;

  i = stack->top;
  n = stack->size;
  if (i == n) {
    if (n == 0) {
      n = DEF_BV_TRAIL_SIZE;
      assert(0<n &&  n<MAX_BV_TRAIL_SIZE);
    } else {
      n += n;
      if (n >= MAX_BV_TRAIL_SIZE) {
        out_of_memory();
      }
    }
    stack->data = (bv_trail_t *) safe_realloc(stack->data, n * sizeof(bv_trail_t));
    stack->size = n;
  }
  assert(i < stack->size);

  stack->data[i].nvars = nv;
  stack->data[i].natoms = na;
  stack->data[i].nbounds = nb;
  stack->data[i].nselects = ns;
  stack->data[i].ndelayed_mapped = ndm;
  stack->data[i].ndelayed_blasted = ndb;
  stack->data[i].nbblasted = bb;

  stack->top = i+1;
}


/*
 * Get the top trail record
 */
static bv_trail_t *bv_trail_top(bv_trail_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}


/*
 * Remove the top record
 */
static inline void bv_trail_pop(bv_trail_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}


/*
 * Delete the stack
 */
static inline void delete_bv_trail(bv_trail_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Empty the stack
 */
static inline void reset_bv_trail(bv_trail_stack_t *stack) {
  stack->top = 0;
}






/***********************
 *  STATISTICS RECORD  *
 **********************/

static void init_bv_stats(bv_stats_t *s) {
  s->eq_atoms = 0;
  s->on_the_fly_atoms = 0;
  s->ge_atoms = 0;
  s->sge_atoms = 0;
  s->equiv_lemmas = 0;
  s->equiv_conflicts = 0;
  s->half_equiv_lemmas = 0;
  s->interface_lemmas = 0;
}

static inline void reset_bv_stats(bv_stats_t *s) {
  init_bv_stats(s);
}



/**************
 *  MARKING   *
 *************/

/*
 * The top-level useful variables are marked and we recursively
 * mark all the variables on which they depend.
 * - the top-level marked variables include:
 *   all variables that occur in atoms
 *   all variables (x, y) such that x := y in the merge table
 *   all variables x that occur in (bit-select x i)
 */
static void bv_solver_mark_variable(bv_solver_t *solver, thvar_t x);

static void bv_solver_mark_poly64_vars(bv_solver_t *solver, bvpoly64_t *p) {
  uint32_t i, n;
  thvar_t x;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    i ++;
  }
  while (i < n ) {
    x = mtbl_get_root(&solver->mtbl, p->mono[i].var);
    bv_solver_mark_variable(solver, x);
    i ++;
  }
}

static void bv_solver_mark_poly_vars(bv_solver_t *solver, bvpoly_t *p) {
  uint32_t i, n;
  thvar_t x;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    i ++;
  }
  while (i < n ) {
    x = mtbl_get_root(&solver->mtbl, p->mono[i].var);
    bv_solver_mark_variable(solver, x);
    i ++;
  }
}

static void bv_solver_mark_pprod_vars(bv_solver_t *solver, pprod_t *p) {
  uint32_t i, n;
  thvar_t x;

  n = p->len;
  for (i=0; i<n; i++) {
    x = mtbl_get_root(&solver->mtbl, p->prod[i].var);
    bv_solver_mark_variable(solver, x);
  }
}

static void bv_solver_mark_variable(bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  bv_ite_t *ite;

  vtbl = &solver->vtbl;

  if (! bvvar_is_marked(vtbl, x)) {
    bvvar_set_mark(vtbl, x);
    switch (bvvar_tag(vtbl, x)) {
    case BVTAG_VAR:
    case BVTAG_CONST64:
    case BVTAG_CONST:
    case BVTAG_BIT_ARRAY:
      // nothing more to do
      break;

    case BVTAG_POLY64:
      bv_solver_mark_poly64_vars(solver, bvvar_poly64_def(vtbl, x));
      break;

    case BVTAG_POLY:
      bv_solver_mark_poly_vars(solver, bvvar_poly_def(vtbl, x));
      break;

    case BVTAG_PPROD:
      bv_solver_mark_pprod_vars(solver, bvvar_pprod_def(vtbl, x));
      break;

    case BVTAG_ITE:
      ite = bvvar_ite_def(vtbl, x);
      // could check whether ite->cond is true or false?
      bv_solver_mark_variable(solver, mtbl_get_root(&solver->mtbl, ite->left));
      bv_solver_mark_variable(solver, mtbl_get_root(&solver->mtbl, ite->right));
      break;

    case BVTAG_UDIV:
    case BVTAG_UREM:
    case BVTAG_SREM:
    case BVTAG_SDIV:
    case BVTAG_SMOD:
    case BVTAG_SHL:
    case BVTAG_LSHR:
    case BVTAG_ASHR:
    case BVTAG_ADD:
    case BVTAG_SUB:
    case BVTAG_MUL:
      bv_solver_mark_variable(solver, mtbl_get_root(&solver->mtbl, vtbl->def[x].op[0]));
      bv_solver_mark_variable(solver, mtbl_get_root(&solver->mtbl, vtbl->def[x].op[1]));
      break;

    case BVTAG_NEG:
      bv_solver_mark_variable(solver, mtbl_get_root(&solver->mtbl, vtbl->def[x].op[0]));
      break;
    }
  }
}




/********************
 *  DELAYED QUEUES  *
 *******************/

/*
 * Check whether x was created before the current base level
 * - if so, add x to the delayed_blasted queue
 */
static void bv_solver_save_delayed_blasted_var(bv_solver_t *solver, thvar_t x) {
  bv_trail_stack_t *trail;

  trail = &solver->trail_stack;
  if (trail->top > 0 && x < bv_trail_top(trail)->nvars) {
    bv_queue_push(&solver->delayed_blasted, x);
  }
}

/*
 * Check whether x was created before the current base level
 * - if so, add x to the delayed_mapped queue
 *
 * If x is in the delayed_mapped, we'll remove x's pseudo map on pop.
 */
static void bv_solver_save_delayed_mapped_var(bv_solver_t *solver, thvar_t x) {
  bv_trail_stack_t *trail;

  trail = &solver->trail_stack;
  if (trail->top > 0 && x < bv_trail_top(trail)->nvars) {
    bv_queue_push(&solver->delayed_mapped, x);
  }
}


/*
 * Store m as pseudo map for variable x. Also add x to the delayed queue
 * if x was created before the current base level.
 * - x must not be mapped already (i.e., solver->vtbl.map[x] must be NULL
 * - m must be a non-null array
 */
static void bv_solver_set_map(bv_solver_t *solver, thvar_t x, literal_t *m) {
  bvvar_set_map(&solver->vtbl, x, m);
  bv_solver_save_delayed_mapped_var(solver, x);
}




/*****************
 *  BIT EXTRACT  *
 ****************/

/*
 * Return the remap table (allocate and initialize it if necessary)
 */
static remap_table_t *bv_solver_get_remap(bv_solver_t *solver) {
  remap_table_t *tmp;

  tmp = solver->remap;
  if (tmp == NULL) {
    tmp = (remap_table_t *) safe_malloc(sizeof(remap_table_t));
    init_remap_table(tmp);
    remap_table_set_level(tmp, solver->base_level);
    solver->remap = tmp;
  }

  return tmp;
}


#ifndef NDEBUG

/*
 * For debugging: check whether x occurs in the select_queue
 */
static bool bvvar_in_select_queue(bv_solver_t *solver, thvar_t x) {
  bv_queue_t *squeue;
  uint32_t i, n;

  squeue = &solver->select_queue;
  n = squeue->top;
  for (i=0; i<n; i++) {
    if (squeue->data[i] == x) return true;
  }

  return false;
}

/*
 * Also for debugging: check whether x is bitblasted or compiled
 * to a variable that's bit-blasted.
 */
static bool bvvar_is_bitblasted_or_compiled(bv_solver_t *solver, thvar_t x) {
  thvar_t y;

  if (bvvar_is_bitblasted(&solver->vtbl, x)) {
    return true;
  }
  if (solver->compiler != NULL) {
    y = bvvar_compiles_to(solver->compiler, x);
    return y > 0 && bvvar_is_bitblasted(&solver->vtbl, y);
  }
  return false;
}

#endif


/*
 * Return the pseudo literal array mapped to x
 * - allocate a new array of n literals if x is not mapped yet
 *   and store x in the select queue
 */
static literal_t *select_bvvar_get_pseudo_map(bv_solver_t *solver, thvar_t x) {
  remap_table_t *rmap;
  literal_t *tmp;
  uint32_t n;

  tmp = bvvar_get_map(&solver->vtbl, x);
  if (tmp == NULL) {
    n = bvvar_bitsize(&solver->vtbl, x);
    rmap = bv_solver_get_remap(solver);
    tmp = remap_table_fresh_array(rmap, n);
    bv_solver_set_map(solver, x, tmp);
    bv_queue_push(&solver->select_queue, x);
  }

  assert(bvvar_is_bitblasted_or_compiled(solver, x) || bvvar_in_select_queue(solver, x));

  return tmp;
}



/*
 * Extract bit i of a 64bit constant x
 * - convert to true_literal or false_literal
 */
static literal_t bvconst64_get_bit(bv_vartable_t *vtbl, thvar_t x, uint32_t i) {
  literal_t l;

  l = false_literal;
  if (tst_bit64(bvvar_val64(vtbl, x), i)) {
    l= true_literal;
  }

  return l;
}


/*
 * Extract bit i of a general constant x
 */
static literal_t bvconst_get_bit(bv_vartable_t *vtbl, thvar_t x, uint32_t i) {
  literal_t l;

  l = false_literal;
  if (bvconst_tst_bit(bvvar_val(vtbl, x), i)) {
    l = true_literal;
  }

  return l;
}


/*
 * Extract bit i of a bvarray variable x
 */
static literal_t bvarray_get_bit(bv_vartable_t *vtbl, thvar_t x, uint32_t i) {
  literal_t *a;

  assert(i < bvvar_bitsize(vtbl, x));

  a = bvvar_bvarray_def(vtbl, x);
  return a[i];
}


/*
 * Extract bit i of variable x:
 * - get it from the pseudo literal array mapped to x
 * - also add x to solver->select_queue
 */
static literal_t bvvar_get_bit(bv_solver_t *solver, thvar_t x, uint32_t i) {
  remap_table_t *rmap;
  literal_t *map;
  literal_t r, l;

  map = select_bvvar_get_pseudo_map(solver, x);

  rmap = solver->remap;
  r = remap_table_find_root(rmap, map[i]); // r := root of map[i]
  l = remap_table_find(rmap, r);           // l := real literal for r
  if (l == null_literal) {
    // nothing attached to r: create a new literal and attach it to r
    l = pos_lit(create_boolean_variable(solver->core));
    remap_table_assign(rmap, r, l);
  }

  return l;
}




/******************
 *  BIT BLASTING  *
 *****************/

/*
 * Allocate and initialize the bit-blaster object if needed
 * - also allocate the remap table if needed
 */
static void bv_solver_prepare_blasting(bv_solver_t *solver) {
  bit_blaster_t *blaster;
  remap_table_t *remap;

  if (solver->blaster == NULL) {
    remap = bv_solver_get_remap(solver);
    blaster = (bit_blaster_t *) safe_malloc(sizeof(bit_blaster_t));
    init_bit_blaster(blaster, solver->core, remap);
    solver->blaster = blaster;
  }
}


/*
 * Allocate and initialize the compiler object (if needed)
 */
static void bv_solver_alloc_compiler(bv_solver_t *solver) {
  bvc_t *c;

  c = solver->compiler;
  if (c == NULL) {
    c = (bvc_t *) safe_malloc(sizeof(bvc_t));
    init_bv_compiler(c, &solver->vtbl, &solver->mtbl);
    bv_compiler_set_level(c, solver->base_level);
    solver->compiler = c;
  }
}


/*
 * Scan the set of atoms created at the current base-level
 * - mark all the variables that occur in these atoms
 */
static void bv_solver_mark_vars_in_atoms(bv_solver_t *solver) {
  bv_atomtable_t *atbl;
  bvatm_t *atm;
  uint32_t i, n;

  /*
   * scan all the atoms and mark their variables
   *
   * TODO: make this more efficient by keeping track
   * of the atoms that have been processed (keep track
   * of this in the trail_stack?)
   */
  atbl = &solver->atbl;
  n = atbl->natoms;
  for (i=0; i<n; i++) {
    atm = bvatom_desc(atbl, i);
    bv_solver_mark_variable(solver, mtbl_get_root(&solver->mtbl, atm->left));
    bv_solver_mark_variable(solver, mtbl_get_root(&solver->mtbl, atm->right));
  }
}


/*
 * Scan the variables
 * - if x == y is in the merge table then mark both x and y
 * - also if x has an eterm, mark x
 */
static void bv_solver_mark_merged_vars(bv_solver_t *solver) {
  bv_vartable_t *vtbl;
  uint32_t i, n;
  thvar_t x;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    x = mtbl_get_root(&solver->mtbl, i);
    if (i != x) {
      bv_solver_mark_variable(solver, i);
      bv_solver_mark_variable(solver, x);
    } else if (bvvar_has_eterm(vtbl, i)) {
      bv_solver_mark_variable(solver, i);
    }
  }
}


/*
 * Mark the variables that are in the select_queue
 */
static void bv_solver_mark_select_vars(bv_solver_t *solver) {
  bv_queue_t *squeue;
  uint32_t i, n;

  squeue = &solver->select_queue;
  n = squeue->top;
  for (i=0; i<n; i++) {
    bv_solver_mark_variable(solver, mtbl_get_root(&solver->mtbl, squeue->data[i]));
  }
}


/*
 * Check whether a variable is useful (i.e., requires bitblasting)
 * - x is useful if it occurs in an atom (i.e., x is marked)
 *   or if it's mapped to another variable y in the merge table
 *   or if it has an egraph term attached.
 */
static bool bvvar_is_useful(bv_solver_t *solver, thvar_t x) {
  thvar_t y;

  y = mtbl_get_root(&solver->mtbl, x);
  return x != y || bvvar_is_marked(&solver->vtbl, x) || bvvar_has_eterm(&solver->vtbl, x);
}


/*
 * Compile all the useful polynomial variables
 */
static void bv_solver_compile_polynomials(bv_solver_t *solver) {
  bv_vartable_t *vtbl;
  bvc_t *compiler;
  uint32_t i, n;

#if 0
  printf("---- COMPILE POLYNOMIALS ----\n");
  print_bv_vartable(stdout, &solver->vtbl);
  print_bv_atomtable(stdout, &solver->atbl);
  printf("\n");
#endif

  bv_solver_alloc_compiler(solver);

  compiler = solver->compiler;
  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    switch (bvvar_tag(vtbl, i)) {
    case BVTAG_POLY64:
    case BVTAG_POLY:
    case BVTAG_PPROD:
      if (bvvar_is_useful(solver, i)) {
#if 0
	printf("  push var: ");
	print_bv_solver_vardef(stdout, solver, i);
	printf("\n");
#endif
        bv_compiler_push_var(compiler, i);
      }
      break;

    default:
      break;
    }
    bvvar_clr_mark(vtbl, i);
  }

  // process the polynomials
  bv_compiler_process_queue(compiler);

  //  print_solver_state(stdout, solver);
}



/*
 * PSEUDO-LITERAL MAPS
 */

/*
 * Convert constant c to an array of pseudo literals
 * - n = number of bits in c
 */
static literal_t *bvconst64_get_pseudo_map(uint64_t c, uint32_t n) {
  literal_t *a;
  uint32_t i;

  assert(0 < n && n <= 64);
  a = (literal_t *) alloc_int_array(n);
  for (i=0; i<n; i++) {
    a[i] = bool2literal(c & 1);
    c >>= 1;
  }

  return a;
}

static literal_t *bvconst_get_pseudo_map(uint32_t *c, uint32_t n) {
  literal_t *a;
  uint32_t i;

  assert(64 < n);
  a = (literal_t *) alloc_int_array(n);
  for (i=0; i<n; i++) {
    a[i] = bool2literal(bvconst_tst_bit(c, i));
  }

  return a;
}


/*
 * Pseudo-literal array mapped to an array of literals a
 * - n = number of literals in a
 */
static literal_t *bvarray_get_pseudo_map(remap_table_t *rmap, literal_t *a, uint32_t n) {
  literal_t *tmp;
  uint32_t i;

  tmp = remap_table_fresh_array(rmap, n);
  for (i=0; i<n; i++) {
    remap_table_assign(rmap, tmp[i], a[i]);
  }

  return tmp;
}


/*
 * Get/create a pseudo map for x
 * - assign a map to x if x is constant or bit array
 * - return map[x]
 */
static literal_t *bvvar_simple_pseudo_map(bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  literal_t *tmp;

  assert(solver->remap != NULL);

  vtbl = &solver->vtbl;
  tmp = bvvar_get_map(vtbl, x);
  if (tmp == NULL) {
    switch (bvvar_tag(vtbl, x)) {
    case BVTAG_CONST64:
      tmp = bvconst64_get_pseudo_map(bvvar_val64(vtbl, x), bvvar_bitsize(vtbl, x));
      bv_solver_set_map(solver, x, tmp);
      break;

    case BVTAG_CONST:
      tmp = bvconst_get_pseudo_map(bvvar_val(vtbl, x), bvvar_bitsize(vtbl, x));
      bv_solver_set_map(solver, x, tmp);
      break;

    case BVTAG_BIT_ARRAY:
      tmp = bvarray_get_pseudo_map(solver->remap, bvvar_bvarray_def(vtbl, x), bvvar_bitsize(vtbl, x));
      bv_solver_set_map(solver, x, tmp);
      break;

    default:
      break;
    }
  }

  return tmp;
}



/*
 * Assert that pseudo literals s1 and s2 are equal
 * - attempt to merge their equivalence classes in the remap table first
 * - if that's not possible, assert (l1 == l2) in the core
 *   where l1 = literal mapped to s1
 *     and l2 = literal mapped to s2
 * - return false if s1 == not s2
 */
static bool merge_pseudo_literals(bv_solver_t *solver, literal_t s1, literal_t s2) {
  remap_table_t *rmap;
  literal_t l1, l2;

  assert(solver->remap != NULL && solver->blaster != NULL);

  rmap = solver->remap;
  s1 = remap_table_find_root(rmap, s1);
  s2 = remap_table_find_root(rmap, s2);
  if (remap_table_mergeable(rmap, s1, s2)) {
    remap_table_merge(rmap, s1, s2);
  } else if (s1 == not(s2)) {
    // contradiction detected
    return false;
  } else if (s1 != s2) {
    l1 = remap_table_find(rmap, s1);
    l2 = remap_table_find(rmap, s2);
    bit_blaster_eq(solver->blaster, l1, l2);
  }

  return true;
}


/*
 * Assert that two arrays a and b of n pseudo literals are equal
 * - return false if a[i] == not b[i] for some i
 */
static bool merge_pseudo_maps(bv_solver_t *solver, literal_t *a, literal_t *b, uint32_t n) {
  uint32_t i;

  if (a == b) {
    return true;
  }

  for (i=0; i<n; i++) {
    if (! merge_pseudo_literals(solver, a[i], b[i])) {
      return false;
    }
  }

  return true;
}



/*
 * Merge the pseudo maps of variables x and y
 * - if x and y have no map, then create a common pseudo-literal array for both
 * - return false if a contradiction is detected
 */
static bool merge_pseudo_maps2(bv_solver_t *solver, thvar_t x, thvar_t y) {
  literal_t *mx, *my;
  uint32_t n;

  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y)
         && x != y && solver->remap != NULL && solver->blaster != NULL);

  mx = bvvar_simple_pseudo_map(solver, x);
  my = bvvar_simple_pseudo_map(solver, y);
  n = bvvar_bitsize(&solver->vtbl, x);

  if (mx == my) {
    if (mx == NULL) {
      // allocate a fresh map
      mx = remap_table_fresh_array(solver->remap, n);
      bv_solver_set_map(solver, x, mx);
      bv_solver_set_map(solver, y, mx);
    }
  } else {
    if (mx == NULL) {
      bv_solver_set_map(solver, x, my);
    } else if (my == NULL) {
      bv_solver_set_map(solver, y, mx);
    } else {
      return merge_pseudo_maps(solver, mx, my, n);
    }
  }

  return true;
}


// merge the maps of x, y, and z
static bool merge_pseudo_map3(bv_solver_t *solver, thvar_t x, thvar_t y, thvar_t z) {
  literal_t *mx, *my, *mz;
  uint32_t n, k;

  assert(x != y && x != z && y != z && solver->remap != NULL && solver->blaster != NULL);

  mx = bvvar_simple_pseudo_map(solver, x);
  my = bvvar_simple_pseudo_map(solver, y);
  mz = bvvar_simple_pseudo_map(solver, z);

  n = bvvar_bitsize(&solver->vtbl, x);

  assert(bvvar_bitsize(&solver->vtbl, y) == n && bvvar_bitsize(&solver->vtbl, z) == n);

  k = 0;
  if (mx != NULL) k |= 4;
  if (my != NULL) k |= 2;
  if (mz != NULL) k |= 1;

  assert(0 <= k && k <= 7);
  switch (k) {
  case 0:
    assert(mx == NULL && my == NULL && mz == NULL);
    mx = remap_table_fresh_array(solver->remap, n);
    bv_solver_set_map(solver, x, mx);
    bv_solver_set_map(solver, y, mx);
    bv_solver_set_map(solver, z, mx);
    break;

  case 1:
    assert(mx == NULL && my == NULL && mz != NULL);
    bv_solver_set_map(solver, x, mz);
    bv_solver_set_map(solver, y, mz);
    break;

  case 2:
    assert(mx == NULL && my != NULL && mz == NULL);
    bv_solver_set_map(solver, x, my);
    bv_solver_set_map(solver, z, my);
    break;

  case 3:
    assert(mx == NULL && my != NULL && mz != NULL);
    bv_solver_set_map(solver, x, my);
    return merge_pseudo_maps(solver, my, mz, n);

  case 4:
    assert(mx != NULL && my == NULL && mz == NULL);
    bv_solver_set_map(solver, y, mx);
    bv_solver_set_map(solver, z, mx);
    break;

  case 5:
    assert(mx != NULL && my == NULL && mz != NULL);
    bv_solver_set_map(solver, y, mx);
    return merge_pseudo_maps(solver, mx, mz, n);

  case 6:
    assert(mx != NULL && my != NULL && mz == NULL);
    bv_solver_set_map(solver, z, mx);
    return merge_pseudo_maps(solver, mx, my, n);

  case 7:
    assert(mx != NULL && my != NULL && mz != NULL);
    return merge_pseudo_maps(solver, mx, my, n) && merge_pseudo_maps(solver, mx, mz, n);
  }

  return true;
}


/*
 * Check whether to merge the maps of x y and z
 * - y = root of x's class
 * - z = what x is compiled to (may be -1)
 */
static bool bv_solver_check_shared_pmaps(bv_solver_t *solver, thvar_t x, thvar_t y, thvar_t z) {
  if (z == null_thvar) {
    z = x;
  }

  if (x == y && z == x) {
    return true;
  } else if (x == y && z != x) {
    return merge_pseudo_maps2(solver, x, z);
  } else if (z == x || z == y) {
    return merge_pseudo_maps2(solver, x, y);
  } else {
    return merge_pseudo_map3(solver, x, y, z);
  }
}


/*
 * Go through all variables and build the shared pseudo maps
 */
static bool bv_solver_make_shared_pseudo_maps(bv_solver_t *solver) {
  bv_vartable_t *vtbl;
  bvc_t *compiler;
  uint32_t i, n;
  thvar_t x, y;

  assert(solver->compiler != NULL);

  compiler = solver->compiler;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    x = mtbl_get_root(&solver->mtbl, i);
    y = bvvar_compiles_to(compiler, i);
    if (! bv_solver_check_shared_pmaps(solver, i, x, y)) {
      return false;
    }
  }

  return true;
}


/*
 * Return the pseudo-map of x
 * - replace x by its root in the merge table
 * - allocate a fresh pseudo map if x doesn't have one already
 */
static literal_t *bvvar_pseudo_map(bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  literal_t *tmp;

  assert(solver->remap != NULL);

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);

  tmp = bvvar_get_map(vtbl, x);
  if (tmp == NULL) {
    switch (bvvar_tag(vtbl, x)) {
    case BVTAG_CONST64:
      tmp = bvconst64_get_pseudo_map(bvvar_val64(vtbl, x), bvvar_bitsize(vtbl, x));
      break;

    case BVTAG_CONST:
      tmp = bvconst_get_pseudo_map(bvvar_val(vtbl, x), bvvar_bitsize(vtbl, x));
      break;

    case BVTAG_BIT_ARRAY:
      tmp = bvarray_get_pseudo_map(solver->remap, bvvar_bvarray_def(vtbl, x), bvvar_bitsize(vtbl, x));
      break;

    case BVTAG_POLY64:
    case BVTAG_POLY:
    case BVTAG_PPROD:
      x = bvvar_compiles_to(solver->compiler, x);
      assert(x != null_thvar); // fall-through intended
    default:
      tmp = remap_table_fresh_array(solver->remap, bvvar_bitsize(vtbl, x));
      break;
    }

    bv_solver_set_map(solver, x, tmp);
  }

  return tmp;
}

/*
 * Check whether array a[0...n-1] is of the form 2^k for some k
 * - if so return k otherwise, return n
 */
static uint32_t bv_is_power_of_two(bit_blaster_t *blaster, literal_t *a, uint32_t n) {
  uint32_t i, k;

  k = n;
  for (i=0; i<n; i++) {
    switch (literal_base_value(blaster->solver, a[i])) {
    case VAL_FALSE:
      break;

    case VAL_TRUE:
      if (k == n) {
	k = i;
	break;
      }

    default:
      goto done;
    }
  }

  return k;

 done:
  return n;
}


/*
 * Check whether a[0 ... n-1] if of the form -2^k for some k (with 0 <= k < n-2)
 * - if so return k, otherwise return n
 */
static uint32_t bv_is_minus_power_of_two(bit_blaster_t *blaster, literal_t *a, uint32_t n) {
  uint32_t i, k;

  k = n;
  for (i=0; i<n; i++) {
    switch (literal_base_value(blaster->solver, a[i])) {
    case VAL_FALSE:
      if (k < n) goto done;
      break;

    case VAL_TRUE:
      if (k == n) {
	k = i;
      }
      break;

    default:
      goto done;
    }
  }

  return k;

 done:
  return n;
}




/*
 * Assert u == (bvadd a b)
 * - check for special cases where a or b is a power of 2
 */
static void bit_blaster_make_bvadd_var(bit_blaster_t *blaster, literal_t *a, literal_t *b, literal_t *u, uint32_t n) {
  uint32_t k;

  k = bv_is_power_of_two(blaster, a, n);
  if (k < n) {
    // a is 2^k
    // printf("bvinc\n");
    bit_blaster_make_bvinc(blaster, b, k, u, n);
    return;
  }

  k = bv_is_power_of_two(blaster, b, n);
  if (k < n) {
    // b is 2^k2
    // printf("bvinc\n");
    bit_blaster_make_bvinc(blaster, a, k, u, n);
    return;
  }

  k = bv_is_minus_power_of_two(blaster, a, n);
  if (k < n) {
    // a is -2^k
    // printf("bvdec\n");
    bit_blaster_make_bvdec(blaster, b, k, u, n);
    return;
  }

  k = bv_is_minus_power_of_two(blaster, b, n);
  if (k < n) {
    // b is -2^k
    // printf("bvdec\n");
    bit_blaster_make_bvdec(blaster, a, k, u, n);
    return;
  }

  // regular adder
  bit_blaster_make_bvadd(blaster, a, b, u, n);
}


/*
 * Assert u == (bvsub a b)
 * - check for the special case where b is a power of 2
 */
static void bit_blaster_make_bvsub_var(bit_blaster_t *blaster, literal_t *a, literal_t *b, literal_t *u, uint32_t n) {
  uint32_t k;

  k = bv_is_power_of_two(blaster, b, n);
  if (k < n) {
    // b is 2^k
    //    printf("bvdec\n");
    bit_blaster_make_bvdec(blaster, a, k, u, n);
    return;
  }

  k = bv_is_minus_power_of_two(blaster, b, n);
  if (k < n) {
    // b is -2^k
    bit_blaster_make_bvinc(blaster, a, k, u, n);
    return;
  }

  // regular subtract
  bit_blaster_make_bvsub(blaster, a, b, u, n);
}


/*
 * Assert (u == (op a b)) for one of the binary operators op
 * - a, b must be fully-defined arrays of n literals
 * - u must be an array of n pseudo literals
 */
static void bit_blaster_make_bvop(bit_blaster_t *blaster, bvvar_tag_t op, literal_t *a, literal_t *b,
                                  literal_t *u, uint32_t n) {
  switch (op) {
  case BVTAG_ADD:
    bit_blaster_make_bvadd_var(blaster, a, b, u, n);
    break;
  case BVTAG_SUB:
    bit_blaster_make_bvsub_var(blaster, a, b, u, n);
    break;
  case BVTAG_MUL:
    bit_blaster_make_bvmul(blaster, a, b, u, n);
    break;
  case BVTAG_SMOD:
    bit_blaster_make_smod(blaster, a, b, u, n);
    break;
  case BVTAG_SHL:
    bit_blaster_make_shift_left(blaster, a, b, u, n);
    break;
  case BVTAG_LSHR:
    bit_blaster_make_lshift_right(blaster, a, b, u, n);
    break;
  case BVTAG_ASHR:
    bit_blaster_make_ashift_right(blaster, a, b, u, n);
    break;

  default:
    assert(false);
  }
}


/*
 * Assert (u == (op a b)) for a division/remainder term (op x y)
 * - a and b must be arrays of n literals
 * - u must be an array of n pseudo-literals
 * Check whether the associate term z = (op' x y) exists and if so
 * apply the bit-blasting operation to z too.
 */
static void bit_blaster_make_bvdivop(bv_solver_t *solver, bvvar_tag_t op, thvar_t x, thvar_t y,
                                     literal_t *a, literal_t *b, literal_t *u, uint32_t n) {
  bv_vartable_t *vtbl;
  literal_t *v;
  thvar_t z;

  vtbl = &solver->vtbl;
  v = NULL;

  switch (op) {
  case BVTAG_UDIV:
    z = find_rem(vtbl, x, y);
    if (z != null_thvar) {
      v = bvvar_pseudo_map(solver, z);
    }
    bit_blaster_make_udivision(solver->blaster, a, b, u, v, n);
    break;

  case BVTAG_UREM:
    z = find_div(vtbl, x, y);
    if (z != null_thvar) {
      v = bvvar_pseudo_map(solver, z);
    }
    bit_blaster_make_udivision(solver->blaster, a, b, v, u, n);
    break;

  case BVTAG_SDIV:
    z = find_srem(vtbl, x, y);
    if (z != null_thvar) {
      v = bvvar_pseudo_map(solver, z);
    }
    bit_blaster_make_sdivision(solver->blaster, a, b, u, v, n);
    break;

  case BVTAG_SREM:
    z = find_sdiv(vtbl, x, y);
    if (z != null_thvar) {
      v = bvvar_pseudo_map(solver, z);
    }
    bit_blaster_make_sdivision(solver->blaster, a, b, v, u, n);
    break;

  default:
    assert(false);
    abort();
  }
}



/*
 * Collect the literals mapped to x in vector v
 * - x must be mapped to an array of pseudo literals
 */
static void collect_bvvar_literals(bv_solver_t *solver, thvar_t x, ivector_t *v) {
  remap_table_t *rmap;
  literal_t *a;
  uint32_t i,  n;
  literal_t s;

  assert(solver->remap != NULL);

  rmap = solver->remap;

  a = bvvar_get_map(&solver->vtbl, x);
  n = bvvar_bitsize(&solver->vtbl, x);

  assert(a != NULL);

  ivector_reset(v);

  for (i=0; i<n; i++) {
    s = a[i];
    assert(s != null_literal);
    ivector_push(v, remap_table_find(rmap, s));
  }
}



/*
 * Recursive bit-blasting:
 * - if x is bitblasted already: do nothing
 */
static void bv_solver_bitblast_variable(bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  bv_ite_t *ite;
  ivector_t *a, *b;
  literal_t *u;
  uint32_t i, n;
  literal_t l;
  bvvar_tag_t op;
  thvar_t y, z;

  assert(solver->remap != NULL && solver->blaster != NULL);

  vtbl = &solver->vtbl;
  rmap = solver->remap;

  if (! bvvar_is_bitblasted(vtbl, x)) {
    /*
     * x has not been bitblasted yet
     */
    u = bvvar_pseudo_map(solver, x);
    n = bvvar_bitsize(vtbl, x);
    op = bvvar_tag(vtbl, x);

    if (bvvar_is_marked(vtbl, x)) {
      /*
       * Cycle in the dependencies: break it by treating x
       * as a variable
       */
      for (i=0; i<n; i++) {
        l = remap_table_find(rmap, u[i]);
        if (l == null_literal) {
          l = bit_blaster_fresh_literal(solver->blaster);
          remap_table_assign(rmap, u[i], l);
        }
      }
    } else {
      /*
       * x has not been visited yet
       */
      bvvar_set_mark(vtbl, x);

      switch (op) {
      case BVTAG_VAR:
        // complete u's
        for (i=0; i<n; i++) {
          l = remap_table_find(rmap, u[i]);
          if (l == null_literal) {
            l = bit_blaster_fresh_literal(solver->blaster);
            remap_table_assign(rmap, u[i], l);
          }
        }
        break;

      case BVTAG_CONST64:
      case BVTAG_CONST:
      case BVTAG_BIT_ARRAY:
        // nothing to do: u is complete
        break;

      case BVTAG_POLY64:
      case BVTAG_POLY:
      case BVTAG_PPROD:
        // replace x
        y = bvvar_compiles_to(solver->compiler, x);
        assert(y != null_thvar);
        bv_solver_bitblast_variable(solver, y);
        break;

      case BVTAG_ITE:
        ite = bvvar_ite_def(vtbl, x);
        l = ite->cond;
        y = ite->left;
        z = ite->right;
#if TRACE
        if (l == true_literal || l == false_literal) {
          if (l == true_literal) {
            printf("---> condition in ite is true\n");
          } else {
            printf("---> condition in ite is false\n");
          }
          print_bv_solver_vardef(stdout, solver, x);
          print_bv_solver_vardef(stdout, solver, ite->left);
          print_bv_solver_vardef(stdout, solver, ite->right);
          fflush(stdout);
        }
#endif
        // TODO? check if l is true/false?
        bv_solver_bitblast_variable(solver, y);
        bv_solver_bitblast_variable(solver, z);
        a = &solver->a_vector;
        b = &solver->b_vector;
        collect_bvvar_literals(solver, y, a);
        collect_bvvar_literals(solver, z, b);
        assert(a->size == n && b->size == n);
        bit_blaster_make_bvmux(solver->blaster, l, a->data, b->data, u, n);
        break;

      case BVTAG_UDIV:
      case BVTAG_UREM:
      case BVTAG_SDIV:
      case BVTAG_SREM:
        y = vtbl->def[x].op[0];
        z = vtbl->def[x].op[1];
        bv_solver_bitblast_variable(solver, y);
        bv_solver_bitblast_variable(solver, z);
        a = &solver->a_vector;
        b = &solver->b_vector;
        collect_bvvar_literals(solver, y, a);
        collect_bvvar_literals(solver, z, b);
        assert(a->size == n && b->size == n);
        bit_blaster_make_bvdivop(solver, op, y, z, a->data, b->data, u, n);
        break;

      case BVTAG_SMOD:
      case BVTAG_SHL:
      case BVTAG_LSHR:
      case BVTAG_ASHR:
      case BVTAG_ADD:
      case BVTAG_SUB:
      case BVTAG_MUL:
        y = vtbl->def[x].op[0];
        z = vtbl->def[x].op[1];
        bv_solver_bitblast_variable(solver, y);
        bv_solver_bitblast_variable(solver, z);
        a = &solver->a_vector;
        b = &solver->b_vector;
        collect_bvvar_literals(solver, y, a);
        collect_bvvar_literals(solver, z, b);
        assert(a->size == n && b->size == n);
        bit_blaster_make_bvop(solver->blaster, op, a->data, b->data, u, n);
        break;

      case BVTAG_NEG:
        y = vtbl->def[x].op[0];
        bv_solver_bitblast_variable(solver, y);
        a = &solver->a_vector;
        collect_bvvar_literals(solver, y, a);
        assert(a->size == n);
        bit_blaster_make_bvneg(solver->blaster, a->data, u, n);
        break;
      }
    }

    /*
     * If x occurs on a dependency cycle, it may be bit-blasted now,
     * even though it wasn't when we entered this function.
     * In this case, we don't want to add x twice to the delayed_blasted queue.
     */
    if (! bvvar_is_bitblasted(vtbl, x)) {
      // mark x as bitblasted
      bvvar_set_bitblasted(vtbl, x);
      bvvar_clr_mark(vtbl, x);

      bv_solver_save_delayed_blasted_var(solver, x);
    }

    assert(bvvar_is_bitblasted(vtbl, x));
    assert(! bvvar_is_marked(vtbl, x));
  }
}

/*
 * Bitblast all the atoms
 */
static void bv_solver_bitblast_atoms(bv_solver_t *solver) {
  bv_atomtable_t *atbl;
  ivector_t *a, *b;
  uint32_t i, n;
  literal_t l;
  thvar_t x, y;

  atbl = &solver->atbl;
  n = atbl->natoms;

  a = &solver->a_vector;
  b = &solver->b_vector;

  for (i=solver->bbptr; i<n; i++) {
    l = atbl->data[i].lit;
    x = atbl->data[i].left;
    y = atbl->data[i].right;

    /*
     * NOTE: checking for redundant disequalities here
     * (using bounds_imply_diseq) does not help
     */

#if TRACE
    if (i < solver->bbptr + 20) {
      printf("BVSOLVER: bitblasting atom[%"PRIu32"]: ", i + solver->bbptr);
      print_bv_solver_atom(stdout, solver, i);
      printf("\n");
    } else if (i == solver->bbptr + 20) {
      printf("...\n\n");
    }
#endif

    /*
     * Process operands x and y
     */
    bv_solver_bitblast_variable(solver, x);
    bv_solver_bitblast_variable(solver, y);
    collect_bvvar_literals(solver, x, a);
    collect_bvvar_literals(solver, y, b);
    assert(a->size == b->size && a->size > 0);

    switch (bvatm_tag(atbl->data + i)) {
    case BVEQ_ATM:
      bit_blaster_make_bveq2(solver->blaster, a->data, b->data, l, a->size);
      break;

    case BVUGE_ATM:
      bit_blaster_make_bvuge2(solver->blaster, a->data, b->data, l, a->size);
      break;

    case BVSGE_ATM:
      bit_blaster_make_bvsge2(solver->blaster, a->data, b->data, l, a->size);
      break;
    }
  }

  // save new ptr
  solver->bbptr = n;
}


#ifndef NDEBUG

/*
 * For debugging: all variables must be unmarked when we start bitblasting
 */
static bool all_bvvars_unmarked(bv_solver_t *solver) {
  bv_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    if (bvvar_is_marked(vtbl, i)) return false;
  }

  return true;
}

#endif


/*
 * Complete bit-blasting:
 * - whenever (x == y) in the merge table, bitblast x and y
 * - if x has an egraph term, then bitblast x
 * - also bit-blast all the variables from the select queue
 */
static void bv_solver_bitblast_variables(bv_solver_t *solver) {
  bv_vartable_t *vtbl;
  bv_queue_t *squeue;
  uint32_t i, n;
  thvar_t x;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    x = mtbl_get_root(&solver->mtbl, i);
    if (x != i) {
      bv_solver_bitblast_variable(solver, x);
      bv_solver_bitblast_variable(solver, i);
    } else if (bvvar_has_eterm(vtbl, i)) {
      bv_solver_bitblast_variable(solver, i);
    }
  }

  squeue = &solver->select_queue;
  n = squeue->top;
  for (i=0; i<n; i++) {
    bv_solver_bitblast_variable(solver, squeue->data[i]);
  }
}



/*
 * Top-level bit-blasting: exported for testing
 */
bool bv_solver_bitblast(bv_solver_t *solver) {
#if DUMP
  bv_solver_dump_state(solver, "before-bitblasting.dmp");
#endif
  bv_solver_prepare_blasting(solver);
  bv_solver_mark_vars_in_atoms(solver);
  bv_solver_mark_merged_vars(solver);
  bv_solver_mark_select_vars(solver);
  bv_solver_compile_polynomials(solver);

  assert(all_bvvars_unmarked(solver));

  if (!bv_solver_make_shared_pseudo_maps(solver)) {
    return false;
  }

#if DUMP
  bv_solver_dump_state(solver, "after-shared-pmaps.dmp");
#endif

  bv_solver_bitblast_atoms(solver);
  bv_solver_bitblast_variables(solver);

#if DUMP
  bv_solver_dump_state(solver, "before-lemmas.dmp");
#endif

  solver->bitblasted = true;

#if 0
  printf("Statistics\n");
  printf("num. bool vars:                 %"PRIu32"\n", num_vars(solver->core));
  printf("num. unit clauses:              %"PRIu32"\n", num_unit_clauses(solver->core));
  printf("num. binary clauses:            %"PRIu32"\n", num_binary_clauses(solver->core));
  printf("num. main clauses:              %"PRIu32"\n", num_prob_clauses(solver->core));
  printf("num. clause literals:           %"PRIu64"\n\n", num_prob_literals(solver->core));
#endif

  //  printf("\nBVSOLVER BITBLAST\n");
  //  print_solver_state(stdout, solver);
  //  printf("\nDONE\n\n");

  return true;
}


/*
 * Variant for testing: stop before the actual bitblasting
 */
bool bv_solver_compile(bv_solver_t *solver) {
#if DUMP
  bv_solver_dump_state(solver, "before-bitblasting.dmp");
#endif
  bv_solver_prepare_blasting(solver);
  bv_solver_mark_vars_in_atoms(solver);
  bv_solver_mark_merged_vars(solver);
  bv_solver_compile_polynomials(solver);

  assert(all_bvvars_unmarked(solver));

  if (!bv_solver_make_shared_pseudo_maps(solver)) {
    return false;
  }

#if DUMP
  bv_solver_dump_state(solver, "after-shared-pmaps.dmp");
#endif

  return true;
}



/************************************************
 *  VARIABLES THAT ARE EQUAL AFTER BITBLASTING  *
 ***********************************************/

/*
 * Check whether arrays of pseudo literals a and b are equal
 * - n = number of bits
 */
static bool equal_literal_maps(bv_solver_t *solver, literal_t *a, literal_t *b, uint32_t n) {
  remap_table_t *rmap;
  uint32_t i;
  literal_t l1, l2;

  rmap = solver->remap;
  for (i=0; i<n; i++) {
    l1 = remap_table_find(rmap, a[i]);
    l2 = remap_table_find(rmap, b[i]);
    assert(l1 != null_literal && l2 != null_literal);
    if (l1 != l2) {
      return false;
    }
  }

  return true;
}

/*
 * Check whether x and y are bitblasted to the same thing
 */
static bool equal_bitblasting(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  literal_t *a, *b;
  uint32_t n;

  assert(solver->bitblasted);

  vtbl = &solver->vtbl;
  n = bvvar_bitsize(vtbl, x);
  if (n != bvvar_bitsize(vtbl, y)) {
    return false;
  }

  a = bvvar_get_map(vtbl, x);
  b = bvvar_get_map(vtbl, y);

  assert(a != NULL && b != NULL);
  return equal_literal_maps(solver, a, b, n);
}


/*
 * Hash code for the bitblasting of x
 */
static uint32_t hash_bitblasting(bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  literal_t *a;
  uint32_t n;

  assert(solver->bitblasted);

  vtbl = &solver->vtbl;
  n = bvvar_bitsize(vtbl, x);
  a = bvvar_get_map(vtbl, x);
  assert(a != NULL);

  return jenkins_hash_intarray(a, n);
}


#if 0
/*
 * Display all bitvector variable in vector v
 */
static void show_partition(bv_solver_t *solver, int32_t *v) {
  uint32_t i, n;

  n = iv_size(v);
  assert(n >= 2);
  for (i=0; i<n; i++) {
    print_bv_solver_var_litarray(stdout, solver, v[i]);
  }
}
#endif

/*
 * Go through vector v: propagate the equality v[0] == v[i] for i=1 ... n
 * to the egraph.
 */
static void propagate_equalities_for_class(bv_solver_t *solver, int32_t *v) {
  bv_vartable_t *vtbl;
  uint32_t i, n;
  eterm_t t, u;

  assert(solver->egraph != NULL);

  vtbl = &solver->vtbl;

  n = iv_size(v);
  assert(n >= 2);

  t = bvvar_get_eterm(vtbl, v[0]);
  assert(t != null_eterm);
  for (i= 1; i<n; i++) {
    u = bvvar_get_eterm(vtbl, v[i]);
    assert(u != null_eterm);
    egraph_propagate_equality(solver->egraph, t, u, EXPL_BV_PROPAGATION, NULL);
  }
}

/*
 * Build an explation for t == u for the egraph
 * - the equality t==u is a strong equality propagated by the previous function
 * - there explanation is empty
 */
static void bv_solver_expand_th_explanation(bv_solver_t *solver, thvar_t t, thvar_t u, void *expl, th_explanation_t *result) {
  // Nothing to do.
}



/*
 * Propagate all strong equalities to the egraph
 */
static void propagate_strong_equalities(bv_solver_t *solver) {
  ipart_t partition;
  bv_vartable_t *vtbl;
  uint32_t i, n;

  init_int_partition(&partition, 0, solver, (ipart_hash_fun_t ) hash_bitblasting,
		     (ipart_match_fun_t) equal_bitblasting);

  vtbl = &solver->vtbl;

  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    if (bvvar_has_eterm(vtbl, i)) {
      int_partition_add(&partition, i);
    }
  }


  n = int_partition_nclasses(&partition);
  for (i=0; i<n; i++) {
#if 0
    printf("Strong Eq Class %"PRIu32"\n", i);
    show_partition(solver, partition.classes[i]);
    printf("----\n");
#endif
    propagate_equalities_for_class(solver, partition.classes[i]);
  }

  delete_int_partition(&partition);
}


/******************
 *  BOUND ATOMS   *
 *****************/

/*
 * Check whether x is a constant
 */
static inline bool is_constant(bv_vartable_t *table, thvar_t x) {
  bvvar_tag_t tag;

  tag = bvvar_tag(table, x);
  return (tag == BVTAG_CONST64) | (tag == BVTAG_CONST);
}


/*
 * Check whether x or y is a constant
 */
static inline bool is_bv_bound_pair(bv_vartable_t *table, thvar_t x, thvar_t y) {
  bvvar_tag_t tag_x, tag_y;

  tag_x = bvvar_tag(table, x);
  tag_y = bvvar_tag(table, y);

  return (tag_x == BVTAG_CONST64) | (tag_x == BVTAG_CONST)
    | (tag_y == BVTAG_CONST64) | (tag_y == BVTAG_CONST);
}



/*
 * Check whether atom i is a 'bound atom' (i.e., inequality between
 * a constant and a non-constant).
 * - all atoms are of the form (op x y), we just check whether x
 *   or y is a bitvector constant.
 * - this is fine since no atom should involve two constants
 *   (constraints between constants are always simplified to true or false)
 */
#ifndef NDEBUG
static inline bool is_bound_atom(bv_solver_t *solver, int32_t i) {
  bvatm_t *a;

  a = bvatom_desc(&solver->atbl, i);
  return is_constant(&solver->vtbl, a->left) || is_constant(&solver->vtbl, a->right);
}
#endif

/*
 * Get the variable in a bound atom
 */
static thvar_t bound_atom_var(bv_solver_t *solver, int32_t i) {
  bvatm_t *a;
  thvar_t x;

  a = bvatom_desc(&solver->atbl, i);
  x = a->left;
  if (is_constant(&solver->vtbl, x)) {
    x = a->right;
  }

  assert(! is_constant(&solver->vtbl, x));

  return x;
}


/*
 * Add (bvge x y) to the bound queue
 * - either x or y must be a constant
 * - the atom (bvge x y) must exist in the atom table
 *   and (bvge x y) must not be a trivial atom
 *   (i.e., not of the form (bvge x 0b00000) or (bvge 0b11111 x))
 */
static void push_bvuge_bound(bv_solver_t *solver, thvar_t x, thvar_t y) {
  int32_t i;

  assert(is_bv_bound_pair(&solver->vtbl, x, y));

  i = find_bvuge_atom(&solver->atbl, x, y);
  assert(i >= 0 && is_bound_atom(solver, i));
  if (is_constant(&solver->vtbl, x)) {
    x = y;
  }

  assert(! is_constant(&solver->vtbl, x));
  bv_bound_queue_push(&solver->bqueue, x, i);
}


/*
 * Same thing for (bvsge x y)
 * - the atom must not be of the form (bvsge x 0b100000)
 *   or (bvsge 0b011111 x)
 */
static void push_bvsge_bound(bv_solver_t *solver, thvar_t x, thvar_t y) {
  int32_t i;

  assert(is_bv_bound_pair(&solver->vtbl, x, y));

  i = find_bvsge_atom(&solver->atbl, x, y);
  assert(i >= 0 && is_bound_atom(solver, i));
  if (is_constant(&solver->vtbl, x)) {
    x = y;
  }

  assert(! is_constant(&solver->vtbl, x));
  bv_bound_queue_push(&solver->bqueue, x, i);
}


/*
 * Same thing for (eq x y)
 */
static void push_bvdiseq_bound(bv_solver_t *solver, thvar_t x, thvar_t y) {
  int32_t i;

  assert(is_bv_bound_pair(&solver->vtbl, x, y));

  i = find_bveq_atom(&solver->atbl, x, y);
  assert(i >= 0 && is_bound_atom(solver, i));
  if (is_constant(&solver->vtbl, x)) {
    x = y;
  }

  assert(! is_constant(&solver->vtbl, x));
  bv_bound_queue_push(&solver->bqueue, x, i);
}



/*
 * Remove all bounds of index >= n
 */
static void bv_solver_remove_bounds(bv_solver_t *solver, uint32_t n) {
  bv_bound_queue_t *queue;
  bv_bound_t *d;
  uint32_t i;
  thvar_t x;

  queue = &solver->bqueue;
  assert(0 <= n && n <= queue->top);

  i = queue->top;
  d = queue->data + i;
  while (i > n) {
    i --;
    d --;
    x = bound_atom_var(solver, d->atom_id);
    assert(0 <= x && x < queue->bsize);
    queue->bound[x] = d->pre;
  }

  queue->top = n;
}



/*
 * SEARCH FOR BOUNDS
 */

/*
 * Check whether a bound atom on x is a lower or upper bound
 * - x must be the variable in bound_atom i
 */
static inline bool lit_is_true(smt_core_t *core, literal_t l) {
  return literal_base_value(core, l) == VAL_TRUE;
}

static inline bool lit_is_false(smt_core_t *core, literal_t l) {
  return literal_base_value(core, l) == VAL_FALSE;
}

// upper bound unsigned
static bool bound_is_ub(bv_solver_t *solver, thvar_t x, int32_t i) {
  bvatm_t *a;

  assert(is_bound_atom(solver, i) && bound_atom_var(solver, i) == x);
  a = bvatom_desc(&solver->atbl, i);
  if (bvatm_is_ge(a)) {
    // either (bvge x c) or (bvge c x)
    return (x == a->left && lit_is_false(solver->core, a->lit)) // (bvge x c) is false so x <= c-1
      || (x == a->right && lit_is_true(solver->core, a->lit));  // (bvge c x) is true so  x <= c
  }

  return false;
}

// lower bound unsigned
static bool bound_is_lb(bv_solver_t *solver, thvar_t x, int32_t i) {
  bvatm_t *a;

  assert(is_bound_atom(solver, i) && bound_atom_var(solver, i) == x);
  a = bvatom_desc(&solver->atbl, i);
  if (bvatm_is_ge(a)) {
    // either (bvge x c) or (bvge c x)
    return (x == a->left && lit_is_true(solver->core, a->lit))  // (bvge x c) is true so x >= c
      || (x == a->right && lit_is_false(solver->core, a->lit)); // (bvge c x) is false so x >= c+1
  }

  return false;
}

// upper bound signed
static bool bound_is_signed_ub(bv_solver_t *solver, thvar_t x, int32_t i) {
  bvatm_t *a;

  assert(is_bound_atom(solver, i) && bound_atom_var(solver, i) == x);
  a = bvatom_desc(&solver->atbl, i);
  if (bvatm_is_sge(a)) {
    // either (bvsge x c) or (bvsge c x)
    return (x == a->left && lit_is_false(solver->core, a->lit)) // (bvge x c) is false so x <= c-1
      || (x == a->right && lit_is_true(solver->core, a->lit));  // (bvge c x) is true so  x <= c
  }

  return false;
}

// lower bound signed
static bool bound_is_signed_lb(bv_solver_t *solver, thvar_t x, int32_t i) {
  bvatm_t *a;

  assert(is_bound_atom(solver, i) && bound_atom_var(solver, i) == x);
  a = bvatom_desc(&solver->atbl, i);
  if (bvatm_is_sge(a)) {
    // either (bvsge x c) or (bvsge c x)
    return (x == a->left && lit_is_true(solver->core, a->lit))  // (bvsge x c) is true so x >= c
      || (x == a->right && lit_is_false(solver->core, a->lit)); // (bvsge c x) is false so x >= c+1
  }

  return false;
}



/*
 * Extract the unsigned or signed upper bound on x from atom i
 * - x must be a bitvector of 64bits or less
 * - for (bvge x c) false, we know (c > 0b00..0)
 * - for (bvsge x c) false, we know (c > 0b1000)
 * In either case, (c-1) can't cause underflow
 * The result is normalized modulo (2 ^ n) where n = size of x
 */
static uint64_t get_upper_bound64(bv_solver_t *solver, thvar_t x, int32_t i) {
  bvatm_t *a;
  uint64_t c;
  uint32_t n;

  a = bvatom_desc(&solver->atbl, i);
  if (x == a->left) {
    // (bvge x c) false: x <= c-1
    n = bvvar_bitsize(&solver->vtbl, x);
    c = norm64(bvvar_val64(&solver->vtbl, a->right) - 1, n);
  } else {
    // (bvge c x) true: x <= c
    assert(x == a->right);
    c = bvvar_val64(&solver->vtbl, a->left);
  }

  assert(c == norm64(c, bvvar_bitsize(&solver->vtbl, x)));

  return c;
}


/*
 * Extract the unsigned or signed lower bound
 * - x must be a bitvector of 64bits or less
 * - for (bvge c x) false, we know (c < 0b11111)
 * - for (bvsge c x) false, we know (c < 0b01111)
 * In either case, (c+1) can't cause overflow
 * The result is normalized modulo (2 ^ n)
 */
static uint64_t get_lower_bound64(bv_solver_t *solver, thvar_t x, int32_t i) {
  bvatm_t *a;
  uint64_t c;
  uint32_t n;

  a = bvatom_desc(&solver->atbl, i);
  if (x == a->left) {
    //(bvge x c) true: x >= c
    c = bvvar_val64(&solver->vtbl, a->right);
  } else {
    // (bvge c x) false: x >= c+1
    assert(x == a->right);
    n = bvvar_bitsize(&solver->vtbl, x);
    c = norm64(bvvar_val64(&solver->vtbl, a->left) + 1, n);
  }

  assert(c == norm64(c, bvvar_bitsize(&solver->vtbl, x)));

  return c;
}



/*
 * Extract the unsigned or signed upper bound on x from atom i
 * - x must be a bitvector of more than 64bits
 * - n = size of x
 * - for (bvge x c) false, we know (c > 0b00..0)
 * - for (bvsge x c) false, we know (c > 0b1000)
 * In either case, (c-1) can't cause underflow
 * The result is returned in c and it's normalized modulo (2 ^ n)
 */
static void get_upper_bound(bv_solver_t *solver, thvar_t x, uint32_t n, int32_t i, bvconstant_t *c) {
  bvatm_t *a;

  a = bvatom_desc(&solver->atbl, i);
  if (x == a->left) {
    // (bvge x c) false: x <= c-1
    bvconstant_copy(c, n, bvvar_val(&solver->vtbl, a->right));
    bvconstant_sub_one(c);
    bvconstant_normalize(c);
  } else {
    // (bvge c x) true: x <= c
    assert(x == a->right);
    bvconstant_copy(c, n, bvvar_val(&solver->vtbl, a->left));
  }
}


/*
 * Extract the unsigned or signed lower bound on x from atom i
 * - x must be a bitvector of more than 64bits
 * - n = size of x
 * - for (bvge x c) false, we know (c > 0b00..0)
 * - for (bvsge x c) false, we know (c > 0b1000)
 * In either case, (c-1) can't cause underflow
 * The result is returned in c and it's normalized modulo (2 ^ n)
 */
static void get_lower_bound(bv_solver_t *solver, thvar_t x, uint32_t n, int32_t i, bvconstant_t *c) {
  bvatm_t *a;

  a = bvatom_desc(&solver->atbl, i);
  if (x == a->left) {
    // (bvge x c) true: x >= c
    bvconstant_copy(c, n, bvvar_val(&solver->vtbl, a->right));
  } else {
    // (bvge c x) false: x >= c+1
    assert(x == a->right);
    bvconstant_copy(c, n, bvvar_val(&solver->vtbl, a->left));
    bvconstant_add_one(c);
    bvconstant_normalize(c);
  }
}



/*
 * Check whether there's a bound asserted on variable x
 * - if so, return true and store the bound in *c
 * - otherwise, return false
 */

// upper bound, 64bits, unsigned
static bool bvvar_has_upper_bound64(bv_solver_t *solver, thvar_t x, uint64_t *c) {
  bv_bound_queue_t *queue;
  bv_bound_t *b;
  int32_t k;

  queue = &solver->bqueue;
  k = bv_bound_for_var(queue, x);
  while (k >= 0) {
    assert(k < queue->top);
    b = queue->data + k;
    if (bound_is_ub(solver, x, b->atom_id)) {
      *c = get_upper_bound64(solver, x, b->atom_id);
      return true;
    }
    k = b->pre;
  }

  return false;
}

// lower bound, 64bits, unsigned
static bool bvvar_has_lower_bound64(bv_solver_t *solver, thvar_t x, uint64_t *c) {
  bv_bound_queue_t *queue;
  bv_bound_t *b;
  int32_t k;

  queue = &solver->bqueue;
  k = bv_bound_for_var(queue, x);
  while (k >= 0) {
    assert(k < queue->top);
    b = queue->data + k;
    if (bound_is_lb(solver, x, b->atom_id)) {
      *c = get_lower_bound64(solver, x, b->atom_id);
      return true;
    }
    k = b->pre;
  }

  return false;
}

// upper bound, 64bits, signed
static bool bvvar_has_signed_upper_bound64(bv_solver_t *solver, thvar_t x, uint64_t *c) {
  bv_bound_queue_t *queue;
  bv_bound_t *b;
  int32_t k;

  queue = &solver->bqueue;
  k = bv_bound_for_var(queue, x);
  while (k >= 0) {
    assert(k < queue->top);
    b = queue->data + k;
    if (bound_is_signed_ub(solver, x, b->atom_id)) {
      *c = get_upper_bound64(solver, x, b->atom_id);
      return true;
    }
    k = b->pre;
  }

  return false;
}


// lower bound, 64bits, signed
static bool bvvar_has_signed_lower_bound64(bv_solver_t *solver, thvar_t x, uint64_t *c) {
  bv_bound_queue_t *queue;
  bv_bound_t *b;
  int32_t k;

  queue = &solver->bqueue;
  k = bv_bound_for_var(queue, x);
  while (k >= 0) {
    assert(k < queue->top);
    b = queue->data + k;
    if (bound_is_signed_lb(solver, x, b->atom_id)) {
      *c = get_lower_bound64(solver, x, b->atom_id);
      return true;
    }
    k = b->pre;
  }

  return false;
}


/*
 * Same thing for bitvectors with more than 64bits
 * - n = number of bits in x
 */

// upper bound, unsigned
static bool bvvar_has_upper_bound(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *c) {
  bv_bound_queue_t *queue;
  bv_bound_t *b;
  int32_t k;

  queue = &solver->bqueue;
  k = bv_bound_for_var(queue, x);
  while (k >= 0) {
    assert(k < queue->top);
    b = queue->data + k;
    if (bound_is_ub(solver, x, b->atom_id)) {
      get_upper_bound(solver, x, n, b->atom_id, c);
      return true;
    }
    k = b->pre;
  }

  return false;
}

// lower bound, unsigned
static bool bvvar_has_lower_bound(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *c) {
  bv_bound_queue_t *queue;
  bv_bound_t *b;
  int32_t k;

  queue = &solver->bqueue;
  k = bv_bound_for_var(queue, x);
  while (k >= 0) {
    assert(k < queue->top);
    b = queue->data + k;
    if (bound_is_lb(solver, x, b->atom_id)) {
      get_lower_bound(solver, x, n, b->atom_id, c);
      return true;
    }
    k = b->pre;
  }

  return false;
}

// upper bound, signed
static bool bvvar_has_signed_upper_bound(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *c) {
  bv_bound_queue_t *queue;
  bv_bound_t *b;
  int32_t k;

  queue = &solver->bqueue;
  k = bv_bound_for_var(queue, x);
  while (k >= 0) {
    assert(k < queue->top);
    b = queue->data + k;
    if (bound_is_signed_ub(solver, x, b->atom_id)) {
      get_upper_bound(solver, x, n, b->atom_id, c);
      return true;
    }
    k = b->pre;
  }

  return false;
}

// lower bound, signed
static bool bvvar_has_signed_lower_bound(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *c) {
  bv_bound_queue_t *queue;
  bv_bound_t *b;
  int32_t k;

  queue = &solver->bqueue;
  k = bv_bound_for_var(queue, x);
  while (k >= 0) {
    assert(k < queue->top);
    b = queue->data + k;
    if (bound_is_signed_lb(solver, x, b->atom_id)) {
      get_lower_bound(solver, x, n, b->atom_id, c);
      return true;
    }
    k = b->pre;
  }

  return false;
}


/*
 * Check whether there's a constraint not (x == 0) on x
 * - this just search for a bound atom of the form (eq x c) or (eq c x)
 *   in the queue
 */
static bool bvvar_is_nonzero(bv_solver_t *solver, thvar_t x) {
  bv_bound_queue_t *queue;
  bv_bound_t *b;
  bvatm_t *a;
  int32_t k;

  queue = &solver->bqueue;
  k = bv_bound_for_var(queue, x);
  while (k >= 0) {
    assert(k < queue->top);
    b = queue->data + k;
    a = bvatom_desc(&solver->atbl, b->atom_id);
    assert(a->left == x || a->right == x);
    if (bvatm_is_eq(a)) {
      return true;
    }
    k = b->pre;
  }

  return false;
}




/**********************
 *  VARIABLE MERGING  *
 *********************/

/*
 * We attempt to keep the simplest element of the class as
 * root of its class, using the following ranking:
 * - constants are simplest:       rank 0
 * - polynomials                   rank 1
 * - bvarray                       rank 2
 * - power products                rank 3
 * - other non-variable terms:     rank 4
 * - variables are last            rank 5
 *
 * The following functions checks whether a is strictly simpler than b
 * based on this ranking.
 */
static const uint8_t bvtag2rank[NUM_BVTAGS] = {
  5,      // BVTAG_VAR
  0,      // BVTAG_CONST64
  0,      // BVTAG_CONST
  1,      // BVTAG_POLY64
  1,      // BVTAG_POLY
  3,      // BVTAG_PPROD
  2,      // BVTAG_BIT_ARRAY
  4,      // BVTAG_ITE
  4,      // BVTAG_UDIV
  4,      // BVTAG_UREM
  4,      // BVTAG_SDIV
  4,      // BVTAG_SREM
  4,      // BVTAG_SMOD
  4,      // BVTAG_SHL
  4,      // BVTAG_LSHR
  4,      // BVTAG_ASHR
};

static inline bool simpler_bvtag(bvvar_tag_t a, bvvar_tag_t b) {
  return bvtag2rank[a] < bvtag2rank[b];
}



/*
 * Merge the equivalence classes of x and y
 * - both x and y must be root of their class
 * - x and y must be distinct variables
 */
static void bv_solver_merge_vars(bv_solver_t *solver, thvar_t x, thvar_t y) {
  mtbl_t *mtbl;
  bvvar_tag_t tag_x, tag_y;
  thvar_t aux;

  mtbl = &solver->mtbl;

  assert(x != y && mtbl_is_root(mtbl, x) && mtbl_is_root(mtbl, y));

  tag_x = bvvar_tag(&solver->vtbl, x);
  tag_y = bvvar_tag(&solver->vtbl, y);

  if (simpler_bvtag(tag_y, tag_x)) {
    aux = x; x = y; y = aux;
  }

  // x is simpler than y, we set map[y] := x
  mtbl_map(mtbl, y, x);
}




/********************************
 *  SUPPORT FOR SIMPLIFICATION  *
 *******************************/

/*
 * Check whether the root of x's class is a 64bit constant
 * - if so return the root, otherwise return x
 */
static thvar_t bvvar_root_if_const64(bv_solver_t *solver, thvar_t x) {
  thvar_t y;

  y = mtbl_get_root(&solver->mtbl, x);
  if (bvvar_is_const64(&solver->vtbl, y)) {
    x = y;
  }

  return x;
}


/*
 * Check whether the root of x's class is a generic constant
 * - if so return the root, otherwise return x
 */
static thvar_t bvvar_root_if_const(bv_solver_t *solver, thvar_t x) {
  thvar_t y;

  y = mtbl_get_root(&solver->mtbl, x);
  if (bvvar_is_const(&solver->vtbl, y)) {
    x = y;
  }

  return x;
}


/*
 * Check whether x is equal to 0b0000...
 */
static bool bvvar_is_zero(bv_vartable_t *vtbl, thvar_t x) {
  uint32_t n, k;

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    return bvvar_val64(vtbl, x) == 0;

  case BVTAG_CONST:
    n = bvvar_bitsize(vtbl, x);
    k = (n + 31) >> 5;
    return bvconst_is_zero(bvvar_val(vtbl, x), k);

  default:
    return false;
  }
}


/*
 * Check whether x is equal to 0b1111...
 */
static bool bvvar_is_minus_one(bv_vartable_t *vtbl, thvar_t x) {
  uint32_t n;

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    n = bvvar_bitsize(vtbl, x);
    return bvconst64_is_minus_one(bvvar_val64(vtbl, x), n);

  case BVTAG_CONST:
    n = bvvar_bitsize(vtbl, x);
    return bvconst_is_minus_one(bvvar_val(vtbl, x), n);

  default:
    return false;
  }
}


/*
 * Check whether x is equal to 0b1000...
 */
static bool bvvar_is_min_signed(bv_vartable_t *vtbl, thvar_t x) {
  uint32_t n;

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    n = bvvar_bitsize(vtbl, x);
    return bvvar_val64(vtbl, x) == min_signed64(n);

  case BVTAG_CONST:
    n = bvvar_bitsize(vtbl, x);
    return bvconst_is_min_signed(bvvar_val(vtbl, x), n);

  default:
    return false;
  }
}


/*
 * Check whether x is equal to 0b0111...
 */
static bool bvvar_is_max_signed(bv_vartable_t *vtbl, thvar_t x) {
  uint32_t n;

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    n = bvvar_bitsize(vtbl, x);
    return bvvar_val64(vtbl, x) == max_signed64(n);

  case BVTAG_CONST:
    n = bvvar_bitsize(vtbl, x);
    return bvconst_is_max_signed(bvvar_val(vtbl, x), n);

  default:
    return false;
  }
}


/*
 * Build the zero constant of n bits
 */
static thvar_t get_zero(bv_solver_t *solver, uint32_t nbits) {
  thvar_t z;

  if (nbits > 64) {
    bvconstant_set_all_zero(&solver->aux1, nbits);
    z = get_bvconst(&solver->vtbl, nbits, solver->aux1.data);
  } else {
    z = get_bvconst64(&solver->vtbl, nbits, 0);
  }

  return z;
}


/*
 * Build the opposite of constant a
 */
static inline thvar_t get_opp_bvconst64(bv_solver_t *solver, uint64_t a, uint32_t nbits) {
  assert(1 <= nbits && nbits <= 64);
  a = norm64(-a, nbits);
  return get_bvconst64(&solver->vtbl, nbits, a);
}

// same thing for a large constant. Use solver->aux1 as buffer.
static thvar_t get_opp_bvconst(bv_solver_t *solver, uint32_t *a, uint32_t nbits) {
  bvconstant_t *aux;

  assert(nbits > 64);
  aux = &solver->aux1;
  bvconstant_copy(aux, nbits, a);
  bvconstant_negate(aux);
  bvconstant_normalize(aux);
  return get_bvconst(&solver->vtbl, nbits, aux->data);
}


/*
 * Check whether p can be written as c0 + a0 t or c0
 * - return true if p has one of these special forms
 * - if p is a constant polynomial, then t is set to null_term
 */
static bool bvpoly64_is_simple(bv_solver_t *solver, bvpoly64_t *p, uint64_t *c0, uint64_t *a0, thvar_t *t) {
  bv_vartable_t *vtbl;
  uint32_t i, n, nbits;
  uint64_t cnst;
  thvar_t x, u;

  vtbl = &solver->vtbl;

  *a0 = 0; // otherwise GCC gives a bogus warning

  n = p->nterms;
  nbits = p->bitsize;
  u = null_thvar;

  cnst = 0;
  i = 0;

  // deal with the constant term of p if any
  if (p->mono[0].var == const_idx) {
    cnst = p->mono[0].coeff;
    i ++;
  }

  // rest of p
  while (i < n) {
    assert(p->mono[i].var != const_idx);

    x = mtbl_get_root(&solver->mtbl, p->mono[i].var);
    if (bvvar_is_const64(vtbl, x)) {
      cnst += p->mono[i].coeff * bvvar_val64(vtbl, x);
    } else if (u == null_thvar) {
      u = x;
      *a0 = p->mono[i].coeff;
    } else if (u == x) {
      // two terms of p have the same root u
      *a0 = norm64(*a0 + p->mono[i].coeff, nbits);
    } else {
      // p has more than one non-constant term
      return false;
    }
    i ++;
  }

  // store the result
  *c0 = norm64(cnst, nbits);
  *t = u;

  return true;
}


/*
 * Same thing for p with large coefficients
 */
static bool bvpoly_is_simple(bv_solver_t *solver, bvpoly_t *p, bvconstant_t *c0, bvconstant_t *a0, thvar_t *t) {
  bv_vartable_t *vtbl;
  uint32_t i, n, nbits, w;
  thvar_t x, u;

  vtbl = &solver->vtbl;

  n = p->nterms;
  nbits = p->bitsize;
  w = p->width;
  u = null_thvar;

  i = 0;

  // c0 := 0 (also make sure c0 has the right size)
  bvconstant_set_all_zero(c0, nbits);

  // deal with the constant of p if any
  if (p->mono[0].var == const_idx) {
    bvconst_set(c0->data, w, p->mono[0].coeff);
    i ++;
  }

  // check the rest of p
  while (i < n) {
    assert(p->mono[i].var != const_idx);

    x = mtbl_get_root(&solver->mtbl, p->mono[i].var);
    if (bvvar_is_const(vtbl, x)) {
      bvconst_addmul(c0->data, w, p->mono[i].coeff, bvvar_val(vtbl, x));
    } else if (u == null_thvar) {
      u = x;
      bvconstant_copy(a0, nbits, p->mono[i].coeff);
    } else if (u == x) {
      assert(a0->bitsize == nbits);
      bvconst_add(a0->data, a0->width, p->mono[i].coeff);
      bvconstant_normalize(a0);
    } else {
      // p has more than one non-constant term
      return false;
    }

    i++;
  }

  bvconstant_normalize(c0);
  *t = u;

  return true;
}



/*********************
 *  EQUALITY CHECKS  *
 ********************/

/*
 * Attempt to simplify (b == 0) to (t == u):
 * - if b is of the form t - u = 0, store t in *vx and u in *vy
 * - if b is of the form t = 0, store t in *vx and zero in *vy
 * - otherwise, leave *vx and *vy unchanged
 * - b is not normalized when this is called
 */
static void simplify_buffer64_eq(bv_solver_t *solver, bvpoly_buffer_t *b, thvar_t *vx, thvar_t *vy) {
  uint64_t a0, a1;
  uint32_t n, nbits;
  thvar_t x, y;

  normalize_bvpoly_buffer(b);
  n = bvpoly_buffer_num_terms(b);
  nbits = bvpoly_buffer_bitsize(b);

  assert(1 <= nbits && nbits <= 64);

  if (n == 2) {
    a0 = bvpoly_buffer_coeff64(b, 0);
    a1 = bvpoly_buffer_coeff64(b, 1);
    x = bvpoly_buffer_var(b, 0);
    y = bvpoly_buffer_var(b, 1);
    if (x == const_idx) {
      if (a1 == 1) {
        // b is a0 + y so (b == 0) iff (y = -a0)
        *vx = y;
        *vy = get_opp_bvconst64(solver, a0, nbits);
      } else if (a1 == mask64(nbits)) {
        // b is a0 - y
        *vx = y;
        *vy = get_bvconst64(&solver->vtbl, nbits, a0);
      }
    } else if ((a0 == 1 && a1 == mask64(nbits)) || (a1 == 1 && a0 == mask64(nbits))) {
      assert(x != const_idx && y != const_idx);
      *vx = x;
      *vy = y;
    }
  } else if (n == 1) {
    a0 = bvpoly_buffer_coeff64(b, 0);
    x = bvpoly_buffer_var(b, 0);
    // we check whether x != const_idx to be safe
    if (x != const_idx && (a0 == 1 || a0 == mask64(nbits))) {
      *vx = bvpoly_buffer_var(b, 0);
      *vy = get_zero(solver, nbits);
    }
  }
}


static void simplify_buffer_eq(bv_solver_t *solver, bvpoly_buffer_t *b, thvar_t *vx, thvar_t *vy) {
  uint32_t *a0, *a1;
  uint32_t n, nbits, w;
  thvar_t x, y;

  normalize_bvpoly_buffer(b);
  n = bvpoly_buffer_num_terms(b);
  nbits = bvpoly_buffer_bitsize(b);
  w = bvpoly_buffer_width(b);

  assert(nbits > 64);

  if (n == 2) {
    a0 = bvpoly_buffer_coeff(b, 0);
    a1 = bvpoly_buffer_coeff(b, 1);
    x = bvpoly_buffer_var(b, 0);
    y = bvpoly_buffer_var(b, 1);
    if (x == const_idx) {
      if (bvconst_is_one(a1, w)) {
        // p is a0 + y
        *vx = y;
        *vy = get_opp_bvconst(solver, a0, nbits);
      } else if (bvconst_is_minus_one(a1, nbits)) {
        // p is a0 - y
        *vx = y;
        *vy = get_bvconst(&solver->vtbl, nbits, a0);
      }
    } else if ((bvconst_is_one(a0, w) && bvconst_is_minus_one(a1, nbits)) ||
               (bvconst_is_one(a1, w) && bvconst_is_minus_one(a0, nbits))) {
      assert(x != const_idx && y != const_idx);
      *vx = x;
      *vy = y;
    }
  } else if (n == 1) {
    a0 = bvpoly_buffer_coeff(b, 0);
    x = bvpoly_buffer_var(b, 0);
    if (x != const_idx &&
        (bvconst_is_one(a0, w) || bvconst_is_minus_one(a0, nbits))) {
      *vx = bvpoly_buffer_var(b, 0);
      *vy = get_zero(solver, nbits);
    }
  }
}


/*
 * Attempt to simplify an equality between two polynomials.
 * Rewrite (p = q) to (p - q) = 0. If p - q is of the
 * form t - u then t is stored into *vx and u is stored in *vy.
 * Otherwise, *vx and *vy are left unchanged.
 */
static void simplify_bvpoly64_eq(bv_solver_t *solver, bvpoly64_t *p, bvpoly64_t *q, thvar_t *vx, thvar_t *vy) {
  bvpoly_buffer_t *b;
  uint32_t n, m;

  assert(p->bitsize == q->bitsize);

  n = p->nterms;
  m = q->nterms;

  if (n <= m+2 && m <= n+2) {
    b = &solver->buffer;
    reset_bvpoly_buffer(b, p->bitsize);
    bvpoly_buffer_add_poly64(b, p);
    bvpoly_buffer_sub_poly64(b, q);
    simplify_buffer64_eq(solver, b, vx, vy);
  }
}

// same thing: large coefficients
static void simplify_bvpoly_eq(bv_solver_t *solver, bvpoly_t *p, bvpoly_t *q, thvar_t *vx, thvar_t *vy) {
  bvpoly_buffer_t *b;
  uint32_t n, m;

  assert(p->bitsize == q->bitsize);

  n = p->nterms;
  m = q->nterms;

  if (n <= m+2 && m <= n+2) {
    b = &solver->buffer;
    reset_bvpoly_buffer(b, p->bitsize);
    bvpoly_buffer_add_poly(b, p);
    bvpoly_buffer_sub_poly(b, q);
    simplify_buffer_eq(solver, b, vx, vy);
  }
}


/*
 * Attempt to simplify an equality between a polynomial p and a constant c
 * - if (p - c) == 0 is of the form (t - u) == 0, then store t in *vx and u in *vy
 * - otherwise leave *vx and *vy unchanged.
 */
static void simplify_bvpoly64_eq_const(bv_solver_t *solver, bvpoly64_t *p, thvar_t c, thvar_t *vx, thvar_t *vy) {
  bvpoly_buffer_t *b;

  assert(bvvar_is_const64(&solver->vtbl, c) && p->bitsize == bvvar_bitsize(&solver->vtbl, c));

  if (p->nterms <= 3) {
    b = &solver->buffer;
    reset_bvpoly_buffer(b, p->bitsize);
    bvpoly_buffer_add_poly64(b, p);
    bvpoly_buffer_sub_const64(b, bvvar_val64(&solver->vtbl, c));
    simplify_buffer64_eq(solver, b, vx, vy);
  }
}

static void simplify_bvpoly_eq_const(bv_solver_t *solver, bvpoly_t *p, thvar_t c, thvar_t *vx, thvar_t *vy) {
  bvpoly_buffer_t *b;

  assert(bvvar_is_const(&solver->vtbl, c) && p->bitsize == bvvar_bitsize(&solver->vtbl, c));

  if (p->nterms <= 3) {
    b = &solver->buffer;
    reset_bvpoly_buffer(b, p->bitsize);
    bvpoly_buffer_add_poly(b, p);
    bvpoly_buffer_sub_constant(b, bvvar_val(&solver->vtbl, c));
    simplify_buffer_eq(solver, b, vx, vy);
  }
}


/*
 * Attempt to simplify an equality between p and a term t
 * - t is not a constant
 * - as before, store the result in *vx and *vy
 */
static void simplify_bvpoly64_eq_term(bv_solver_t *solver, bvpoly64_t *p, thvar_t t, thvar_t *vx, thvar_t *vy) {
  bvpoly_buffer_t *b;

  assert(p->bitsize == bvvar_bitsize(&solver->vtbl, t));

  if (p->nterms <= 3) {
    b = &solver->buffer;
    reset_bvpoly_buffer(b, p->bitsize);
    bvpoly_buffer_add_poly64(b, p);
    bvpoly_buffer_sub_var(b, t);
    simplify_buffer64_eq(solver, b, vx, vy);
  }
}

static void simplify_bvpoly_eq_term(bv_solver_t *solver, bvpoly_t *p, thvar_t t, thvar_t *vx, thvar_t *vy) {
  bvpoly_buffer_t *b;

  assert(p->bitsize == bvvar_bitsize(&solver->vtbl, t));

  if (p->nterms <= 3) {
    b = &solver->buffer;
    reset_bvpoly_buffer(b, p->bitsize);
    bvpoly_buffer_add_poly(b, p);
    bvpoly_buffer_sub_var(b, t);
    simplify_buffer_eq(solver, b, vx, vy);
  }
}


/*
 * Attempt to simplify (eq x y) to an equivalent equality (eq x' y')
 * - on entry, x and y must be stored in *vx and *vy
 * - x and y must be root in solver->mtbl
 * - on exit, the simplified form is stored in *vx and *vy
 * - return true if the equality was simplified (i.e. if *vx != x or *vy != y)
 */
static bool simplify_eq(bv_solver_t *solver, thvar_t *vx, thvar_t *vy) {
  bv_vartable_t *vtbl;
  thvar_t x, y;
  bvvar_tag_t tag_x, tag_y;

  x = *vx;
  y = *vy;

  assert(x != y && mtbl_is_root(&solver->mtbl, x) && mtbl_is_root(&solver->mtbl, y));

  vtbl = &solver->vtbl;

  tag_x = bvvar_tag(vtbl, x);
  tag_y = bvvar_tag(vtbl, y);

  if (tag_x == tag_y) {
    if (tag_x == BVTAG_POLY64) {
      simplify_bvpoly64_eq(solver, bvvar_poly64_def(vtbl, x), bvvar_poly64_def(vtbl, y), vx, vy);
    } else if (tag_x == BVTAG_POLY) {
      simplify_bvpoly_eq(solver, bvvar_poly_def(vtbl, x), bvvar_poly_def(vtbl, y), vx, vy);
    }
  } else if (tag_x == BVTAG_POLY64) {
    if (tag_y == BVTAG_CONST64) {
      simplify_bvpoly64_eq_const(solver, bvvar_poly64_def(vtbl, x), y, vx, vy);
    } else {
      simplify_bvpoly64_eq_term(solver, bvvar_poly64_def(vtbl, x), y, vx, vy);
    }
  } else if (tag_y == BVTAG_POLY64) {
    if (tag_x == BVTAG_CONST64) {
      simplify_bvpoly64_eq_const(solver, bvvar_poly64_def(vtbl, y), x, vx, vy);
    } else {
      simplify_bvpoly64_eq_term(solver, bvvar_poly64_def(vtbl, y), x, vx, vy);
    }
  } else if (tag_x == BVTAG_POLY) {
    if (tag_y == BVTAG_CONST) {
      simplify_bvpoly_eq_const(solver, bvvar_poly_def(vtbl, x), y, vx, vy);
    } else {
      simplify_bvpoly_eq_term(solver, bvvar_poly_def(vtbl, x), y, vx, vy);
    }
  } else if (tag_y == BVTAG_POLY) {
    if (tag_x == BVTAG_CONST64) {
      simplify_bvpoly_eq_const(solver, bvvar_poly_def(vtbl, y), x, vx, vy);
    } else {
      simplify_bvpoly_eq_term(solver, bvvar_poly_def(vtbl, y), x, vx, vy);
    }
  }


  if (x != *vx || y != *vy) {
#if 0
    printf("---> bv simplify (bveq u!%"PRId32" u!%"PRId32")\n", x, y);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, x);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, y);
    printf("     simplified to (bveq u!%"PRId32" u!%"PRId32")\n", *vx, *vy);
    if (is_constant(&solver->vtbl, *vx)) {
      printf("     ");
      print_bv_solver_vardef(stdout, solver, *vx);
    }
    if (is_constant(&solver->vtbl, *vy)) {
      printf("     ");
      print_bv_solver_vardef(stdout, solver, *vy);
    }
    printf("\n");
#endif
    *vx = mtbl_get_root(&solver->mtbl, *vx);
    *vy = mtbl_get_root(&solver->mtbl, *vy);

    return true;
  }

  return false;
}


/*
 * Check whether two variables x and y are equal
 * - x and y must be the roots of their equivalence class in the merge table
 */
static inline bool equal_bvvar(bv_solver_t *solver, thvar_t x, thvar_t y) {
  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y));
  assert(mtbl_is_root(&solver->mtbl, x) && mtbl_is_root(&solver->mtbl, y));
  return x == y;
}




/*******************
 *  INEQUALITIES   *
 ******************/

/*
 * BOUNDS FOR BIT ARRAYS
 */

/*
 * Number of significant bits in a
 * - a is an array of n literals
 * - this searches for the largest m such that a[m-2] /= a[n-1]
 *
 * This is used to deal with sign-extension. If a is equal to
 * (sign-extend k b) where b has m bits, then this function returns m
 * (or something smaller than m).
 */
static uint32_t bitarray_num_significant_bits(literal_t *a, uint32_t n) {
  literal_t sign;

  assert(0 < n);

  n --;
  sign = a[n]; // sign bit
  while (n > 0) {
    if (a[n - 1] != sign) break;
    n --;
  }
  return n + 1;
}


/*
 * Compute a lower and upper bound on a bitarray a
 * - n = number of bits in a. n must be no more than 64
 * - the bounds are returned in intv
 * - both are normalized modulo 2^n
 */
static void bitarray_bounds_unsigned64(literal_t *a, uint32_t n, bv64_interval_t *intv) {
  uint64_t low, high;
  uint32_t i;

  assert(0 < n && n <= 64);
  low = 0;
  high = mask64(n);    // all bits equal to 1
  for (i=0; i<n; i++) {
    if (a[i] == false_literal) {
      high = clr_bit64(high, i);
    } else if (a[i] == true_literal) {
      low = set_bit64(low, i);
    }
  }

  assert(low <= high && low == norm64(low, n) && high == norm64(high, n));

  intv->low = low;
  intv->high = high;
  intv->nbits = n;
}


/*
 * Bounds on a, when interpreted as a sign integer in 2s complement representation.
 * This checks whether a is of the form (sign-extend ... b) to get more
 * precise bounds.  (cf. term_utils.c for more details).
 */
static void bitarray_bounds_signed64(literal_t *a, uint32_t n, bv64_interval_t *intv) {
  uint64_t low, high;
  uint32_t i, m;

  assert(0 < n && n <= 64);

  low = 0;
  high = mask64(n);   // all bits equal to 1

  m = bitarray_num_significant_bits(a, n);
  assert(0 < m && m <= n);

  for (i=0; i<m-1; i++) {
    if (a[i] == false_literal) {
      high = clr_bit64(high, i);
    } else if (a[i] == true_literal) {
      low = set_bit64(low, i);
    }
  }

  // All the bits from m-1 to n-1 are the same; they are equal to a[n-1].
  if (a[n-1] != true_literal) { // the sign bit may be 0
    for (i=m-1; i<n; i++) {
      high = clr_bit64(high, i);
    }
  }
  if (a[n-1] != false_literal) { // the sign bit may be 1
    for (i=m-1; i<n; i++) {
      low = set_bit64(low, i);
    }
  }

  assert(signed64_ge(high, low, n) && low == norm64(low, n) && high == norm64(high, n));

  intv->low = low;
  intv->high = high;
  intv->nbits = n;
}


/*
 * Lower/upper bounds for a bit array of more than 64bits
 * - both are normalized modulo 2^n and stored in intv
 */
static void bitarray_bounds_unsigned(literal_t *a, uint32_t n, bv_interval_t *intv) {
  uint32_t i;

  assert(n > 64);

  bv_triv_interval_u(intv, n); // intv->low = 0b00..0, intv->high = 0b111..1
  for (i=0; i<n; i++) {
    if (a[i] == true_literal) {
      bvconst_set_bit(intv->low, i);
    } else if (a[i] == false_literal) {
      bvconst_clr_bit(intv->high, i);
    }
  }

  assert(bvconst_is_normalized(intv->low, n) && 
	 bvconst_is_normalized(intv->high, n) &&
	 bvconst_le(intv->low, intv->high, n));
}

/*
 * Same for a interpreted as a signed integer.
 */
static void bitarray_bounds_signed(literal_t *a, uint32_t n, bv_interval_t *intv) {
  uint32_t i, m;

  assert(n > 64);

  bv_triv_interval_s(intv, n); // intv->low = 0b100000, intv->high = 0b011111

  m = bitarray_num_significant_bits(a, n);
  assert(0 < m && m <= n);

  for (i=0; i<m-1; i++) {
    if (a[i] == true_literal) {
      bvconst_set_bit(intv->low, i);
    } else if (a[i] == false_literal) {
      bvconst_clr_bit(intv->high, i);
    }
  }

  // All the bits from m-1 to n-1 are the same; they are equal to a[n-1].
  if (a[n-1] != true_literal) { // the sign bit may be 0
    for (i=m-1; i<n; i++) {
      bvconst_clr_bit(intv->high, i);
    }
  }
  if (a[n-1] != false_literal) { // the sign bit may be 1
    for (i=m-1; i<n; i++) {
      bvconst_set_bit(intv->low, i);
    }
  }

  assert(bvconst_is_normalized(intv->low, n) && 
	 bvconst_is_normalized(intv->high, n) &&
	 bvconst_sle(intv->low, intv->high, n));
}


/*
 * GENERAL CASE
 */

/*
 * Recursive computation of bounds on a variable x
 * - d = limit on recursion depth
 * - n = number of bits in x
 */
static void bvvar_bounds_u64(bv_solver_t *solver, thvar_t x, uint32_t n, uint32_t d, bv64_interval_t *intv);
static void bvvar_bounds_s64(bv_solver_t *solver, thvar_t x, uint32_t n, uint32_t d, bv64_interval_t *intv);
static void bvvar_bounds_u(bv_solver_t *solver, thvar_t x, uint32_t n, uint32_t d, bv_interval_t *intv);
static void bvvar_bounds_s(bv_solver_t *solver, thvar_t x, uint32_t n, uint32_t d, bv_interval_t *intv);


/*
 * Bounds on polynomials (unsigned)
 * - d = recursion limit
 */
static void bvpoly64_bounds_u(bv_solver_t *solver, bvpoly64_t *p, uint32_t d, bv64_interval_t *intv) {
  bv64_interval_t aux;
  uint32_t i, n, nbits;
  thvar_t x;

  n = p->nterms;
  nbits = p->bitsize;
  i = 0;

  // constant term if any
  if (p->mono[i].var == const_idx) {
    bv64_point_interval(intv, p->mono[i].coeff, nbits);
    i ++;
  } else {
    bv64_zero_interval(intv, nbits);
  }

  while (i < n) {
    x = mtbl_get_root(&solver->mtbl, p->mono[i].var);
    bvvar_bounds_u64(solver, x, nbits, d, &aux);
    bv64_interval_addmul_u(intv, &aux, p->mono[i].coeff);
    if (bv64_interval_is_triv_u(intv)) break;
    i ++;
  }
}

// signed bounds
static void bvpoly64_bounds_s(bv_solver_t *solver, bvpoly64_t *p, uint32_t d, bv64_interval_t *intv) {
  bv64_interval_t aux;
  uint32_t i, n, nbits;
  thvar_t x;

  n = p->nterms;
  nbits = p->bitsize;
  i = 0;

  // constant term
  if (p->mono[i].var == const_idx) {
    bv64_point_interval(intv, p->mono[i].coeff, nbits);
    i ++;
  } else {
    bv64_zero_interval(intv, nbits);
  }

  while (i < n) {
    x = mtbl_get_root(&solver->mtbl, p->mono[i].var);
    bvvar_bounds_s64(solver, x, nbits, d, &aux);
    bv64_interval_addmul_s(intv, &aux, p->mono[i].coeff);
    if (bv64_interval_is_triv_s(intv)) break;
    i ++;
  }
}


/*
 * Bounds on polynomials (more than 64bits)
 * - d = recursion limit
 * - intv = where the bounds are stored
 * - solver->intv_stack must be allocated before this is called
 */
static void bvpoly_bounds_u(bv_solver_t *solver, bvpoly_t *p, uint32_t d, bv_interval_t *intv) {
  bv_interval_t *aux;
  bv_aux_buffers_t *buffers;
  uint32_t i, n, nbits;
  thvar_t x;

  n = p->nterms;
  nbits = p->bitsize;

  aux = get_bv_interval(&solver->intv_stack);
  if (aux == NULL) {
    // no buffer available: return [0b000.., 0b11...]
    bv_triv_interval_u(intv, n);
  } else {

    buffers = get_bv_aux_buffers(&solver->intv_stack);

    i = 0;
    if (p->mono[i].var == const_idx) {
      bv_point_interval(intv, p->mono[i].coeff, nbits);
      i ++;
    } else {
      bv_zero_interval(intv, nbits);
    }

    while (i < n) {
      x = mtbl_get_root(&solver->mtbl, p->mono[i].var);
      bvvar_bounds_u(solver, x, nbits, d, aux);
      bv_interval_addmul_u(intv, aux, p->mono[i].coeff, buffers);
      if (bv_interval_is_triv_u(intv)) break;
      i ++;
    }

    // cleanup
    release_bv_interval(&solver->intv_stack);
  }
}

// signed bounds
static void bvpoly_bounds_s(bv_solver_t *solver, bvpoly_t *p, uint32_t d, bv_interval_t *intv) {
  bv_interval_t *aux;
  bv_aux_buffers_t *buffers;
  uint32_t i, n, nbits;
  thvar_t x;

  n = p->nterms;
  nbits = p->bitsize;

  aux = get_bv_interval(&solver->intv_stack);
  if (aux == NULL) {
    // no buffer available: return [0b100.., 0b011...]
    bv_triv_interval_s(intv, n);
  } else {

    buffers = get_bv_aux_buffers(&solver->intv_stack);

    i = 0;
    if (p->mono[i].var == const_idx) {
      bv_point_interval(intv, p->mono[i].coeff, nbits);
      i ++;
    } else {
      bv_zero_interval(intv, nbits);
    }

    while (i < n) {
      x = mtbl_get_root(&solver->mtbl, p->mono[i].var);
      bvvar_bounds_s(solver, x, nbits, d, aux);
      bv_interval_addmul_s(intv, aux, p->mono[i].coeff, buffers);
      if (bv_interval_is_triv_s(intv)) break;
      i ++;
    }

    // cleanup
    release_bv_interval(&solver->intv_stack);
  }
}


/*
 * Lower/upper bounds on (bvurem x y)
 * - x is in op[0]
 * - y is in op[1]
 * - n = number of bits in x and y
 */
static void bvurem64_bounds_u(bv_solver_t *solver, thvar_t op[2], uint32_t n, bv64_interval_t *intv) {
  bv_vartable_t *vtbl;
  uint64_t b;
  thvar_t y;

  assert(1 <= n && n <= 64);

  // store default bounds: improve the upper bound if y is a constant
  bv64_triv_interval_u(intv, n);

  vtbl = &solver->vtbl;
  y = op[1];
  if (bvvar_is_const64(vtbl, y)) {
    b = bvvar_val64(vtbl, y);
    if (b != 0) {
      // 0 <= (bvurem x y) <= b-1
      intv->high = norm64(b-1, n);
    }
  }
}

static void bvurem_bounds_u(bv_solver_t *solver, thvar_t op[2], uint32_t n, bv_interval_t *intv) {
  bv_vartable_t *vtbl;
  uint32_t *b;
  uint32_t k;
  thvar_t y;

  assert(n > 64);

  bv_triv_interval_u(intv, n);
  vtbl = &solver->vtbl;
  y = op[1];
  if (bvvar_is_const(vtbl, y)) {
    k = (n + 31) >> 5;
    b = bvvar_val(vtbl, y);
    if (bvconst_is_nonzero(b, k)) {
      // 0 <= (bvurem x y) <= b-1
      bvconst_set(intv->high, k, b);
      bvconst_sub_one(intv->high, k);
      assert(bvconst_is_normalized(intv->high, n));
    }
  }
}


/*
 * Lower/upper bounds on (bvsrem x y) or (bvsmod x y)
 * - x is in op[0]
 * - y is in op[1]
 * - n = number of bits in x and y
 */
static void bvsrem64_bounds_s(bv_solver_t *solver, thvar_t op[2], uint32_t n, bv64_interval_t *intv) {
  bv_vartable_t *vtbl;
  uint64_t b;
  thvar_t y;

  assert(1 <= n && n <= 64);

  // store default bounds: improve the upper bound if y is a constant
  bv64_triv_interval_s(intv, n);

  vtbl = &solver->vtbl;
  y = op[1];
  if (bvvar_is_const64(vtbl, y)) {
    b = bvvar_val64(vtbl, y);
    if (is_neg64(b, n)) {
      // b < 0 so b + 1 <= (bvsrem x y) <= - b - 1
      intv->low = norm64(b + 1, n);
      intv->high = norm64(-b -1, n);
    } else if (b != 0) {
      // b > 0 so -b+1 <= (bvsrem x y) <= b-1
      intv->low = norm64(-b+1, n);
      intv->high = norm64(b-1, n);
    }
    assert(bv64_interval_is_normalized(intv) && signed64_le(intv->low, intv->high, n));
  }
}

static void bvsrem_bounds_s(bv_solver_t *solver, thvar_t op[2], uint32_t n, bv_interval_t *intv) {
  bv_vartable_t *vtbl;
  uint32_t *b;
  uint32_t k;
  thvar_t y;

  assert(n > 64);

  bv_triv_interval_s(intv, n);
  vtbl = &solver->vtbl;
  y = op[1];
  if (bvvar_is_const(vtbl, y)) {
    k = (n + 31) >> 5;
    b = bvvar_val(vtbl, y);
    if (bvconst_is_nonzero(b, k)) {
      if (bvconst_tst_bit(b, n-1)) {
        // negative divider
        // b + 1 <= (bvsrem x y) <= -(b+1)
        bvconst_set(intv->low, k, b);
        bvconst_add_one(intv->low, k);
        bvconst_normalize(intv->low, n); // b+1 needs normalizing if b is -1
        bvconst_set(intv->high, k, intv->low);
        bvconst_negate(intv->high, k);
        bvconst_normalize(intv->high, n);
      } else {
        // positive divider
        // -(b-1) <= (bvsrem x y) <= b-1
        bvconst_set(intv->high, k, b);
        bvconst_sub_one(intv->high, k);
	assert(bvconst_is_normalized(intv->high, n));
        bvconst_set(intv->low, k, intv->high);
        bvconst_negate(intv->low, k);
        bvconst_normalize(intv->low, n);
      }
    }
    assert(bv_interval_is_normalized(intv) && bvconst_sle(intv->low, intv->high, n));
  }
}


/*
 * Lower/upper bound for a bitvector variable x
 * - n = bitsize of x: must be between 1 and 64
 */
static void bvvar_bounds_u64(bv_solver_t *solver, thvar_t x, uint32_t n, uint32_t d, bv64_interval_t *intv) {
  bv_vartable_t *vtbl;
  bvvar_tag_t tag_x;
  uint64_t c;

  vtbl = &solver->vtbl;

  assert(valid_bvvar(vtbl, x) && n == bvvar_bitsize(vtbl, x) && 1 <= n && n <= 64);

  tag_x = bvvar_tag(vtbl, x);

  if (tag_x == BVTAG_CONST64) {
    bv64_point_interval(intv, bvvar_val64(vtbl, x), n);
    return;
  }

  if (tag_x == BVTAG_BIT_ARRAY) {
    bitarray_bounds_unsigned64(bvvar_bvarray_def(vtbl, x), n, intv);
  } else if (tag_x == BVTAG_POLY64 && d>0) {
    bvpoly64_bounds_u(solver, bvvar_poly64_def(vtbl, x), d-1, intv);
  } else if (tag_x == BVTAG_UREM) {
    bvurem64_bounds_u(solver, bvvar_binop(vtbl, x), n, intv);
  } else {
    // default bounds
    bv64_triv_interval_u(intv, n);
  }


  /*
   * Check for better bounds in the bound queue
   *
   * Note: if an asserted lower bound on c is greater than intv->high
   * then the constraints are unsat (but this will be detected later).
   */
  if (bvvar_has_lower_bound64(solver, x, &c) && c > intv->low && c <= intv->high) {
    intv->low = c;
  }
  if (bvvar_has_upper_bound64(solver, x, &c) && c < intv->high && c >= intv->low) {
    intv->high = c;
  }

  assert(bv64_interval_is_normalized(intv) && intv->low <= intv->high);
}


/*
 * Same thing for bitvectors interpreted as signed integers.
 */
static void bvvar_bounds_s64(bv_solver_t *solver, thvar_t x, uint32_t n, uint32_t d, bv64_interval_t *intv) {
  bv_vartable_t *vtbl;
  bvvar_tag_t tag_x;
  uint64_t c;

  vtbl = &solver->vtbl;

  assert(valid_bvvar(vtbl, x) && n == bvvar_bitsize(vtbl, x) && 1 <= n && n <= 64);

  tag_x = bvvar_tag(vtbl, x);

  if (tag_x == BVTAG_CONST64) {
    bv64_point_interval(intv, bvvar_val64(vtbl, x), n);
    return;
  }

  if (tag_x == BVTAG_BIT_ARRAY) {
    bitarray_bounds_signed64(bvvar_bvarray_def(vtbl, x), n, intv);
  } else if (tag_x == BVTAG_POLY64 && d>0) {
    bvpoly64_bounds_s(solver, bvvar_poly64_def(vtbl, x), d-1, intv);
  } else if (tag_x == BVTAG_SREM || tag_x == BVTAG_SMOD) {
    bvsrem64_bounds_s(solver, bvvar_binop(vtbl, x), n, intv);
  } else {
    // default bounds
    bv64_triv_interval_s(intv, n);
  }

  /*
   * Check for better bounds in the queue
   */
  if (bvvar_has_signed_lower_bound64(solver, x, &c) && signed64_gt(c, intv->low, n) &&
      signed64_le(c, intv->high, n)) {
    intv->low = c;
  }
  if (bvvar_has_signed_upper_bound64(solver, x, &c) && signed64_lt(c, intv->high, n) &&
      signed64_ge(c, intv->low, n)) {
    intv->high = c;
  }

  assert(bv64_interval_is_normalized(intv) && signed64_le(intv->low, intv->high, n));
}


/*
 * Lower/upper bound for a bitvector variable x
 * - n = bitsize of x: must be more than 64
 * - the result is stored in intv
 */
static void bvvar_bounds_u(bv_solver_t *solver, thvar_t x, uint32_t n, uint32_t d, bv_interval_t *intv) {
  bv_vartable_t *vtbl;
  bvconstant_t *c;
  bvvar_tag_t tag_x;

  vtbl = &solver->vtbl;

  assert(valid_bvvar(vtbl, x) && n == bvvar_bitsize(vtbl, x) && 64 < n);

  tag_x = bvvar_tag(vtbl, x);

  if (tag_x == BVTAG_CONST) {
    bv_point_interval(intv, bvvar_val(vtbl, x), n);
    return;
  }

  if (tag_x == BVTAG_BIT_ARRAY) {
    bitarray_bounds_unsigned(bvvar_bvarray_def(vtbl, x), n, intv);
  } else if (tag_x == BVTAG_POLY && d > 0) {
    bvpoly_bounds_u(solver, bvvar_poly_def(vtbl, x), d-1, intv);
  } else if (tag_x == BVTAG_UREM) {
    bvurem_bounds_u(solver, bvvar_binop(vtbl, x), n, intv);
  } else {
    // default bounds
    bv_triv_interval_u(intv, n);
  }

  /*
   * Check for better bounds in the queue
   */
  c = &solver->aux1;

  if (bvvar_has_lower_bound(solver, x, n, c) &&
      bvconst_gt(c->data, intv->low, n) &&
      bvconst_le(c->data, intv->high, n)) {
    // c: lower bound on x with c <= intv->high and c > intv->low
    // replace intv->low by c
    assert(bvconstant_is_normalized(c));
    bvconst_set(intv->low, c->width, c->data);
  }

  if (bvvar_has_upper_bound(solver, x, n, c) &&
      bvconst_lt(c->data, intv->high, n) &&
      bvconst_ge(c->data, intv->low, n)) {
    // c: upper bound on x with c >= intv->low and c < intv->high
    // replace intv->high by c
    assert(bvconstant_is_normalized(c));
    bvconst_set(intv->high, c->width, c->data);
  }

  assert(bv_interval_is_normalized(intv) && bvconst_le(intv->low, intv->high, n));
}

static void bvvar_bounds_s(bv_solver_t *solver, thvar_t x, uint32_t n, uint32_t d, bv_interval_t *intv) {
  bv_vartable_t *vtbl;
  bvconstant_t *c;
  bvvar_tag_t tag_x;

  vtbl = &solver->vtbl;

  assert(valid_bvvar(vtbl, x) && n == bvvar_bitsize(vtbl, x) && 64 < n);

  tag_x = bvvar_tag(vtbl, x);

  if (tag_x == BVTAG_CONST) {
    bv_point_interval(intv, bvvar_val(vtbl, x), n);
    return;
  }

  if (tag_x == BVTAG_BIT_ARRAY) {
    bitarray_bounds_signed(bvvar_bvarray_def(vtbl, x), n, intv);
  } else if (tag_x == BVTAG_POLY && d > 0) {
    bvpoly_bounds_s(solver, bvvar_poly_def(vtbl, x), d-1, intv);
  } else if (tag_x == BVTAG_SREM || tag_x == BVTAG_SMOD) {
    bvsrem_bounds_s(solver, bvvar_binop(vtbl, x), n, intv);
  } else {
    // default bounds
    bv_triv_interval_s(intv, n);
  }

  /*
   * Check for better bounds in the queue
   */
  c = &solver->aux1;

  if (bvvar_has_signed_lower_bound(solver, x, n, c) &&
      bvconst_sgt(c->data, intv->low, n) &&
      bvconst_sle(c->data, intv->high, n)) {
    // c: lower bound on x with c <= intv->high and c > intv->low
    // replace intv->low by c
    assert(bvconstant_is_normalized(c));
    bvconst_set(intv->low, c->width, c->data);
  }

  if (bvvar_has_signed_upper_bound(solver, x, n, c) &&
      bvconst_slt(c->data, intv->high, n) &&
      bvconst_sge(c->data, intv->low, n)) {
    // c: upper bound on x with c >= intv->low and c < intv->high
    // replace intv->high by c
    assert(bvconstant_is_normalized(c));
    bvconst_set(intv->high, c->width, c->data);
  }

  assert(bv_interval_is_normalized(intv) && bvconst_sle(intv->low, intv->high, n));
}


/*
 * SIMPLIFY INEQUALITIES
 */

/*
 * Three possible codes returned by the  'check_bvuge' and 'check_bvsge' functions
 * - the order matters: we want BVTEST_FALSE = 0 = false and BVTEST_TRUE = 1 = true
 */
typedef enum {
  BVTEST_FALSE = 0,
  BVTEST_TRUE,
  BVTEST_UNKNOWN,
} bvtest_code_t;


#define MAX_RECUR_DEPTH 4

/*
 * Check whether (x >= y) simplifies (unsigned)
 * - n = number of bits in x and y
 * - both x and y must be 64bits or less
 */
static bvtest_code_t check_bvuge64_core(bv_solver_t *solver, thvar_t x, thvar_t y, uint32_t n) {
  bv64_interval_t intv_x, intv_y;

  bvvar_bounds_u64(solver, x, n, MAX_RECUR_DEPTH, &intv_x);  // intv_x.low <= x <= intv_x.high
  bvvar_bounds_u64(solver, y, n, MAX_RECUR_DEPTH, &intv_y);  // intv_y.low <= y <= intv_y.high

  if (intv_x.low >= intv_y.high) {
    return BVTEST_TRUE;
  }

  if (intv_x.high < intv_y.low) {
    return BVTEST_FALSE;
  }

  return BVTEST_UNKNOWN;
}


/*
 * Check whether (x >= y) simplifies (unsigned)
 * - n = number of bits in x and y
 * - both x and y must be more than 64bits
 */
static bvtest_code_t check_bvuge_core(bv_solver_t *solver, thvar_t x, thvar_t y, uint32_t n) {
  bv_interval_t *bounds_x, *bounds_y;

  // prepare interval stack
  alloc_bv_interval_stack(&solver->intv_stack);
  bounds_x = get_bv_interval(&solver->intv_stack);
  bounds_y = get_bv_interval(&solver->intv_stack);

  assert(bounds_x != NULL && bounds_y != NULL);

  bvvar_bounds_u(solver, x, n, MAX_RECUR_DEPTH, bounds_x);  // bounds_x.low <= x <= bounds_x.high
  bvvar_bounds_u(solver, y, n, MAX_RECUR_DEPTH, bounds_y);  // bounds_y.low <= y <= bounds_y.high


  /*
   * hack: empty the interval stack here
   * bounds_x and bounds_y are still good pointers in stack->data
   */
  assert(solver->intv_stack.top == 2);
  release_all_bv_intervals(&solver->intv_stack);

  if (bvconst_ge(bounds_x->low, bounds_y->high, n)) {
    return BVTEST_TRUE;
  }

  if (bvconst_lt(bounds_x->high, bounds_y->low, n)) {
    return BVTEST_FALSE;
  }

  return BVTEST_UNKNOWN;
}


/*
 * Check whether (x >= y) simplifies (unsigned)
 * - x and y must be roots in the merge table
 * - Return BVTEST_FALSE if (x > y) is known to hold
 * - return BVTEST_TRUE  if (x >= y) is known to hold
 * - return BVTEST_UNKNOWN otherwise
 */
static bvtest_code_t check_bvuge(bv_solver_t *solver, thvar_t x, thvar_t y) {
  uint32_t n;
  bvtest_code_t code;

  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y));
  assert(mtbl_is_root(&solver->mtbl, x) && mtbl_is_root(&solver->mtbl, y));

  if (x == y) return BVTEST_TRUE;

  n = bvvar_bitsize(&solver->vtbl, x);

  if (n <= 64) {
    code = check_bvuge64_core(solver, x, y, n);
  } else {
    code = check_bvuge_core(solver, x, y, n);
  }

  return code;
}


/*
 * Check whether (x >= y) simplifies (signed comparison)
 * - n = number of bits in x and y
 * - both x and y must be 64 bits or less
 */
static bvtest_code_t check_bvsge64_core(bv_solver_t *solver, thvar_t x, thvar_t y, uint32_t n) {
  bv64_interval_t intv_x, intv_y;

  bvvar_bounds_s64(solver, x, n, MAX_RECUR_DEPTH, &intv_x);  // intv_x.low <= x <= intv_x.high
  bvvar_bounds_s64(solver, y, n, MAX_RECUR_DEPTH, &intv_y);  // intv_y.low <= y <= intv_y.high

  if (signed64_ge(intv_x.low, intv_y.high, n)) { // lx >= uy
    return BVTEST_TRUE;
  }

  if (signed64_lt(intv_x.high, intv_y.low, n)) { // ux < ly
    return BVTEST_FALSE;
  }

  return BVTEST_UNKNOWN;
}


/*
 * Check whether (x >= y) simplifies (signed comparison)
 * - n = number of bits in x and y
 * - both x and y must be more than 64 bits
 */
static bvtest_code_t check_bvsge_core(bv_solver_t *solver, thvar_t x, thvar_t y, uint32_t n) {
  bv_interval_t *bounds_x, *bounds_y;

  // prepare interval stack
  alloc_bv_interval_stack(&solver->intv_stack);
  bounds_x = get_bv_interval(&solver->intv_stack);
  bounds_y = get_bv_interval(&solver->intv_stack);

  assert(bounds_x != NULL && bounds_y != NULL);

  bvvar_bounds_s(solver, x, n, MAX_RECUR_DEPTH, bounds_x);  // bounds_x.low <= x <= bounds_x.high
  bvvar_bounds_s(solver, y, n, MAX_RECUR_DEPTH, bounds_y);  // bounds_y.low <= y <= bounds_y.high

  /*
   * hack: empty the interval stack here
   * bounds_x and bounds_y are still good pointers in stack->data
   */
  assert(solver->intv_stack.top == 2);
  release_all_bv_intervals(&solver->intv_stack);

  if (bvconst_sge(bounds_x->low, bounds_y->high, n)) {
    return BVTEST_TRUE;
  }

  if (bvconst_slt(bounds_x->high, bounds_y->low, n)) {
    return BVTEST_FALSE;
  }

  return BVTEST_UNKNOWN;
}


/*
 * Check whether (x <= y) simplifies (signed)
 * - x and y must be roots in the merge table
 * - return BVTEST_FALSE if (x > y) is known to hold
 * - return BVTEST_TRUE  if (x >= y) is known to hold
 * - return BVTEST_UNKNOWN otherwise
 */
static bvtest_code_t check_bvsge(bv_solver_t *solver, thvar_t x, thvar_t y) {
  uint32_t n;
  bvtest_code_t code;

  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y));
  assert(mtbl_is_root(&solver->mtbl, x) && mtbl_is_root(&solver->mtbl, y));

  if (x == y) return BVTEST_TRUE;

  n = bvvar_bitsize(&solver->vtbl, x);

  if (n <= 64) {
    code = check_bvsge64_core(solver, x, y, n);
  } else {
    code = check_bvsge_core(solver, x, y, n);
  }

  return code;
}


/*
 * Check whether (x >= y) simplifies to (y == x)
 * - x and y must be roots in the merge table
 * - returns true if (y >= x) has been asserted as an axiom
 */
static bool bvuge_simplifies_to_bveq(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bvatm_t *a;
  int32_t i;

  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y));
  assert(mtbl_is_root(&solver->mtbl, x) && mtbl_is_root(&solver->mtbl, y));

  i = find_bvuge_atom(&solver->atbl, y, x); // atom (bvuge y x)
  if (i >= 0) {
    a = bvatom_desc(&solver->atbl, i);
    return lit_is_true(solver->core, a->lit); // check whether (bvuge y x) is true 
  }
  return false;
}


// same thing for signed comparison
static bool bvsge_simplifies_to_bveq(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bvatm_t *a;
  int32_t i;

  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y));
  assert(mtbl_is_root(&solver->mtbl, x) && mtbl_is_root(&solver->mtbl, y));

  i = find_bvsge_atom(&solver->atbl, y, x); // atom (bvsge y x)
  if (i >= 0) {
    a = bvatom_desc(&solver->atbl, i);
    return lit_is_true(solver->core, a->lit); // check whether (bvsge y x) is true 
  }
  return false;  
}



/************************
 *  DISEQUALITY CHECKS  *
 ***********************/

/*
 * Check whether two bitarrays a and b are distinct
 * - n = size of both arrays
 * - return true if a and b can't be equal, false if we don't know
 * - for now, this returns true if there's an
 *   index i such that a[i] = not b[i]
 */
static bool diseq_bitarrays(literal_t *a, literal_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (opposite(a[i], b[i])) {
      return true;
    }
  }

  return false;
}


/*
 * Check whether bit array a and small constant c must differ.
 * - n = number of bits in a (and c)
 */
static bool diseq_bitarray_const64(literal_t *a, uint64_t c, uint32_t n) {
  uint32_t i;

  assert(n <= 64);

  /*
   * We use the fact that true_literal = 0 and false_literal = 1
   * So (bit i of c) == a[i] implies a != c
   */
  assert(true_literal == 0 && false_literal == 1);

  for (i=0; i<n; i++) {
    if (((int32_t) (c & 1)) == a[i]) {
      return true;
    }
    c >>= 1;
  }

  return false;
}


/*
 * Same thing for a constant c with more than 64bits
 */
static bool diseq_bitarray_const(literal_t *a, uint32_t *c, uint32_t n) {
  uint32_t i;

  assert(n >= 64);

  /*
   * Same trick as above:
   * - bvconst_tst_bit(c, i) = bit i of c = either 0 or 1
   */
  assert(true_literal == 0 && false_literal == 1);

  for (i=0; i<n; i++) {
    if (bvconst_tst_bit(c, i) == a[i]) {
      return true;
    }
  }

  return false;
}


/*
 * Check whether x and constant c can't be equal
 * - n = number of bits
 * - d = recursion limit
 */
static bool diseq_bvvar_const64(bv_solver_t *solver, thvar_t x, uint64_t c, uint32_t n, uint32_t d) {
  bv_vartable_t *vtbl;
  uint64_t c0, a0;
  thvar_t t;

  assert(bvvar_bitsize(&solver->vtbl, x) == n && 1 <= n && n <= 64);
  assert(c == norm64(c, n));

  vtbl = &solver->vtbl;

  while (d > 0) {
    /*
     * In this loop, we rewrite (x != c) to
     * true or false, or to an equivalent disequality (x' != c')
     */

    // in bvpoly64_is_simple, we follow the roots
    // this could cause looping so we force exit when d == 0
    d --;

    // x should be a root in mtbl
    assert(x == mtbl_get_root(&solver->mtbl, x));

    switch (bvvar_tag(vtbl, x)) {
    case BVTAG_CONST64:
      return bvvar_val64(vtbl, x) != c;

    case BVTAG_BIT_ARRAY:
      return diseq_bitarray_const64(bvvar_bvarray_def(vtbl, x), c, n);

    case BVTAG_POLY64:
      if (bvpoly64_is_simple(solver, bvvar_poly64_def(vtbl, x), &c0, &a0, &t)) {
        if (t == null_thvar || a0 == 0) {
          // x is equal to c0
          return (c0 != c);
        } else if (a0 == 1) {
          // x is equal to c0 + t
          // so (x != c) is equivalent to (t != c - c0);
          x = t;
          c = norm64(c - c0, n);
          continue;
        } else if (a0 == mask64(n)) { // a0 = -1
          // x is equal to c0 - t
          // so (x != c) is equivalent to t != c0 - c
          x = t;
          c = norm64(c0 - c, n);
          continue;
        }
      }

      /*
       * Fall through intended: if x is a poly of the wrong form
       */
    default:
      return false;
    }
  }

  // default answer if d == 0: don't know
  return false;
}


/*
 * Same thing for size > 64
 * - the function uses aux2 and aux3 as buffers so c must not be one of them
 */
static bool diseq_bvvar_const(bv_solver_t *solver, thvar_t x, bvconstant_t *c, uint32_t n, uint32_t d) {
  bv_vartable_t *vtbl;
  bvconstant_t *c0, *a0;
  thvar_t t;

  assert(bvvar_bitsize(&solver->vtbl, x) == n && n > 64);
  assert(c->bitsize == n &&  bvconstant_is_normalized(c));
  assert(c != &solver->aux2 && c != &solver->aux3);

  vtbl = &solver->vtbl;

  while (d > 0) {
    /*
     * In this loop, we rewrite (x != c) to
     * true or false, or to an equivalent disequality (x' != c')
     */

    d --;

    // x should be a root in mtbl
    assert(x == mtbl_get_root(&solver->mtbl, x));

    switch (bvvar_tag(vtbl, x)) {
    case BVTAG_CONST:
      return bvconst_neq(bvvar_val(vtbl, x), c->data, c->width);

    case BVTAG_BIT_ARRAY:
      return diseq_bitarray_const(bvvar_bvarray_def(vtbl, x), c->data, n);

    case BVTAG_POLY:
      c0 = &solver->aux2;
      a0 = &solver->aux3;
      if (bvpoly_is_simple(solver, bvvar_poly_def(vtbl, x), c0, a0, &t)) {
        assert(c0->bitsize == n && bvconstant_is_normalized(c0));
        assert(t == null_thvar || (a0->bitsize == n && bvconstant_is_normalized(a0)));

        if (t == null_thvar || bvconstant_is_zero(a0)) {
          // x is equal to c0
          return bvconst_neq(c0->data, c->data, c->width);
        } else if (bvconstant_is_one(a0)) {
          // x is equal to c0 + t
          // so (x != c) is equivalent to (t != c - c0);
          x = t;
          // compute c := c - c0
          bvconst_sub(c->data, c->width, c0->data);
          bvconstant_normalize(c);
          continue;
        } else if (bvconstant_is_minus_one(a0)) {
          // x is equal to c0 - t
          // so (x != c) is equivalent to t != c0 - c
          x = t;
          // compute c:= c0 - c, normalized
          bvconst_sub(c->data, c->width, c0->data);
          bvconst_negate(c->data, c->width);
          bvconstant_normalize(c);
          continue;
        }
      }

      /*
       * Fall through intended: if x is a poly of the wrong form
       */
    default:
      return false;
    }

  }

  // default answer if d == 0: don't know
  return false;
}


/*
 * Recursion limit for diseq checks
 */
#define MAX_DISEQ_RECUR_DEPTH 4

/*
 * Top-level disequality check
 * - x and y must be roots of their equivalence class in the merge table
 */
static bool diseq_bvvar(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *c;
  bvvar_tag_t tag_x, tag_y;
  uint32_t n;

  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y));
  assert(mtbl_is_root(&solver->mtbl, x) && mtbl_is_root(&solver->mtbl, y));

  if (x == y) return false;

  vtbl = &solver->vtbl;
  tag_x = bvvar_tag(vtbl, x);
  tag_y = bvvar_tag(vtbl, y);

  n = bvvar_bitsize(vtbl, x);
  if (n <= 64) {
    if (tag_x == BVTAG_CONST64) {
      return diseq_bvvar_const64(solver, y, bvvar_val64(vtbl, x), n, MAX_DISEQ_RECUR_DEPTH);
    }

    if (tag_y == BVTAG_CONST64) {
      return diseq_bvvar_const64(solver, x, bvvar_val64(vtbl, y), n, MAX_DISEQ_RECUR_DEPTH);
    }

    if (tag_x == BVTAG_POLY64 && tag_y == BVTAG_POLY64) {
      return disequal_bvpoly64(bvvar_poly64_def(vtbl, x), bvvar_poly64_def(vtbl, y));
    }

    if (tag_x == BVTAG_BIT_ARRAY && tag_y == BVTAG_BIT_ARRAY) {
      return diseq_bitarrays(bvvar_bvarray_def(vtbl, x), bvvar_bvarray_def(vtbl, y), n);
    }

    if (tag_x == BVTAG_POLY64 && tag_y != BVTAG_CONST64) {
      return bvpoly64_is_const_plus_var(bvvar_poly64_def(vtbl, x), y);
    }

    if (tag_y == BVTAG_POLY64 && tag_x != BVTAG_CONST64) {
      return bvpoly64_is_const_plus_var(bvvar_poly64_def(vtbl, y), x);
    }

  } else {

    // More than 64bits
    if (tag_x == BVTAG_CONST) {
      c = &solver->aux1;
      bvconstant_copy(c, n, bvvar_val(vtbl, x));
      return diseq_bvvar_const(solver, y, c, n, MAX_DISEQ_RECUR_DEPTH);
    }

    if (tag_y == BVTAG_CONST) {
      c = &solver->aux1;
      bvconstant_copy(c, n, bvvar_val(vtbl, y));
      return diseq_bvvar_const(solver, x, c, n, MAX_DISEQ_RECUR_DEPTH);
    }

    if (tag_x == BVTAG_POLY && tag_y == BVTAG_POLY) {
      return disequal_bvpoly(bvvar_poly_def(vtbl, x), bvvar_poly_def(vtbl, y));
    }

    if (tag_x == BVTAG_BIT_ARRAY && tag_y == BVTAG_BIT_ARRAY) {
      return diseq_bitarrays(bvvar_bvarray_def(vtbl, x), bvvar_bvarray_def(vtbl, y), n);
    }

    if (tag_x == BVTAG_POLY && tag_y != BVTAG_CONST) {
      return bvpoly_is_const_plus_var(bvvar_poly_def(vtbl, x), y);
    }

    if (tag_y == BVTAG_POLY && tag_x != BVTAG_CONST) {
      return bvpoly_is_const_plus_var(bvvar_poly_def(vtbl, y), x);
    }

  }

  return false;
}



/*
 * PROVISIONAL: MORE DISEQUALITY CHECKS
 */

/*
 * Check disequalities using asserted bounds
 * - x and y are variables
 * - n = number of bits
 * - return true if x and y
 */
static bool diseq_bvvar_by_bounds64(bv_solver_t *solver, thvar_t x, thvar_t y, uint32_t n) {
  bv64_interval_t intv_x, intv_y;

  assert(1 <= n && n <= 64);

  bvvar_bounds_u64(solver, x, n, MAX_RECUR_DEPTH, &intv_x);  // intv_x.low <= x <= intv_x.high
  bvvar_bounds_u64(solver, y, n, MAX_RECUR_DEPTH, &intv_y);  // intv_y.low <= y <= intv_y.high
  if (intv_x.high < intv_y.low || intv_y.high < intv_x.low) {
    // the internals [intv_x.low, intv_x.high] and [intv_y.low, intv_y.high] are disjoint
    return true;
  }

  // Try signed intervals
  bvvar_bounds_s64(solver, x, n, MAX_RECUR_DEPTH, &intv_x);  // intv_x.low <= x <= intv_x.high
  bvvar_bounds_s64(solver, y, n, MAX_RECUR_DEPTH, &intv_y);  // intv_y.low <= y <= intv_y.high

  if (signed64_lt(intv_x.high, intv_y.low, n) || signed64_lt(intv_y.high, intv_x.low, n)) {
    return true;
  }

  return false;
}


static bool diseq_bvvar_by_bounds(bv_solver_t *solver, thvar_t x, thvar_t y, uint32_t n) {
  bv_interval_t *bounds_x, *bounds_y;
  bool result;

  // prepare interval stack
  alloc_bv_interval_stack(&solver->intv_stack);
  bounds_x = get_bv_interval(&solver->intv_stack);
  bounds_y = get_bv_interval(&solver->intv_stack);

  assert(bounds_x != NULL && bounds_y != NULL);

  bvvar_bounds_u(solver, x, n, MAX_RECUR_DEPTH, bounds_x);  // bounds_x.low <= x <= bounds_x.high
  bvvar_bounds_u(solver, y, n, MAX_RECUR_DEPTH, bounds_y);  // bounds_y.low <= y <= bounds_y.high

  if (bvconst_lt(bounds_x->high, bounds_y->low, n) || bvconst_lt(bounds_y->high, bounds_x->low, n)) {
    result = true;
  } else {
    // Try signed intervals
    bvvar_bounds_s(solver, x, n, MAX_RECUR_DEPTH, bounds_x);  // bounds_x.low <= x <= bounds_x.high
    bvvar_bounds_s(solver, y, n, MAX_RECUR_DEPTH, bounds_y);  // bounds_y.low <= y <= bounds_y.high

    result = bvconst_slt(bounds_x->high, bounds_y->low, n) || bvconst_slt(bounds_y->high, bounds_x->low, n);
  }

  release_all_bv_intervals(&solver->intv_stack);

  return result;
}


static bool bounds_imply_diseq(bv_solver_t *solver, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y));
  assert(mtbl_is_root(&solver->mtbl, x) && mtbl_is_root(&solver->mtbl, y));

  n = bvvar_bitsize(&solver->vtbl, x);
  if (n <= 64) {
    return diseq_bvvar_by_bounds64(solver, x, y, n);
  } else {
    return diseq_bvvar_by_bounds(solver, x, y, n);
  }
}



/*****************************************
 *  SIMPLIFICATION + TERM CONSTRUCTION   *
 ****************************************/

/*
 * Add a * x to buffer b
 * - replace x by its value if it's a constant
 * - also replace x by its root value if the root is a constant
 * - b, a, and x must all have the same bitsize
 */
static void bvbuffer_add_mono64(bv_solver_t *solver, bvpoly_buffer_t *b, thvar_t x, uint64_t a) {
  bv_vartable_t *vtbl;
  thvar_t y;

  vtbl = &solver->vtbl;
  y = bvvar_root_if_const64(solver, x);
  if (bvvar_is_const64(vtbl, y)) {
    bvpoly_buffer_add_const64(b, a * bvvar_val64(vtbl, y));
  } else {
    bvpoly_buffer_add_mono64(b, y, a);
  }
}

// same thing for bitsize > 64
static void bvbuffer_add_mono(bv_solver_t *solver, bvpoly_buffer_t *b, thvar_t x, uint32_t *a) {
  bv_vartable_t *vtbl;
  thvar_t y;

  vtbl = &solver->vtbl;
  y = bvvar_root_if_const(solver, x);
  if (bvvar_is_const(vtbl, y)) {
    // add const_idx * a * value of y
    bvpoly_buffer_addmul_monomial(b, const_idx, a, bvvar_val(vtbl, y));
  } else {
    bvpoly_buffer_add_monomial(b, y, a);
  }
}


/*
 * Check whether a polynomial (after expansion) is equal to a constant or
 * an existing variable.
 * - the expanded poly is stored in *b (as a list of monomials)
 * - b must be normalized
 * - return null_thvar (i.e., -1) if there's no simplification
 */
static thvar_t simplify_expanded_poly(bv_solver_t *solver, bvarith_buffer_t *b) {
  bv_vartable_t *vtbl;
  uint32_t n, nbits;
  bvmlist_t *m;
  pprod_t *r;
  thvar_t x;

  vtbl = &solver->vtbl;
  n = bvarith_buffer_size(b);
  nbits = bvarith_buffer_bitsize(b);

  x = null_thvar;
  if (n == 0) {
    bvconstant_set_all_zero(&solver->aux1, nbits);
    x = get_bvconst(vtbl, nbits, solver->aux1.data);

  } else if (n == 1) {
    m = b->list; // unique monomial of b
    r = m->prod; // power product in this monomial
    if (r == empty_pp) {
      // b is a constant
      x = get_bvconst(vtbl, nbits, m->coeff);
    } else if (pp_is_var(r) && bvconst_is_one(m->coeff, (nbits + 31) >> 5)) {
      // b is 1 * x for some x
      x = var_of_pp(r);
    }
  }

  return x;
}


/*
 * Same thing for a 64bit polynomial
 */
static thvar_t simplify_expanded_poly64(bv_solver_t *solver, bvarith64_buffer_t *b) {
  bv_vartable_t *vtbl;
  uint32_t n, nbits;
  bvmlist64_t *m;
  pprod_t *r;
  thvar_t x;

  vtbl = &solver->vtbl;
  n = bvarith64_buffer_size(b);
  nbits = bvarith64_buffer_bitsize(b);

  x = null_thvar;
  if (n == 0) {
    x = get_bvconst64(vtbl, nbits, 0);

  } else if (n == 1) {
    m = b->list; // unique monomial of b
    r = m->prod; // power product in this monomial
    if (r == empty_pp) {
      // b is a constant
      x = get_bvconst64(vtbl, nbits, m->coeff);
    } else if (pp_is_var(r) && m->coeff == 1) {
      // b is 1 * x for some x
      x = var_of_pp(r);
    }
  }

  return x;
}


/*
 * Build the variable for a polynomial stored in buffer
 */
static thvar_t map_bvpoly(bv_solver_t *solver, bvpoly_buffer_t *b) {
  bv_vartable_t *vtbl;
  bvexp_table_t *etbl;
  bvarith_buffer_t *eb;
  thvar_t x;
  uint32_t n, nbits, h;

  vtbl = &solver->vtbl;

  n = bvpoly_buffer_num_terms(b);
  nbits = bvpoly_buffer_bitsize(b);

  /*
   * Check whether p is a constant or of the form 1. x
   */
  if (n == 0) {
    // return the constant 0b000...0
    bvconstant_set_all_zero(&solver->aux1, nbits);
    x = get_bvconst(vtbl, nbits, solver->aux1.data);
    return x;
  }

  if (n == 1) {
    x = bvpoly_buffer_var(b, 0);
    if (x == const_idx) {
      // p is a constant
      x = get_bvconst(vtbl, nbits, bvpoly_buffer_coeff(b, 0));
      return x;
    }

    if (bvconst_is_one(bvpoly_buffer_coeff(b, 0), (nbits + 31) >> 5)) {
      // p is equal to 1 . x
      return x;
    }
  }


  /*
   * Expand p then check whether the expanded form is equal to a constant
   * or an existing variable
   */
  etbl = &solver->etbl;
  eb = &solver->exp_buffer;
  expand_bvpoly(etbl, eb, b);
  x = simplify_expanded_poly(solver, eb);

  if (x < 0) {
    // no simplification: check for an existing variable with
    // the same expanded form
    h = hash_bvmlist(eb->list, nbits);
    x = bvexp_table_find(etbl, eb, h);
    if (x < 0) {
      // not in the etbl
      x = get_bvpoly(vtbl, b);
      bvexp_table_add(etbl, x, eb, h);  // store x and its expansion in etbl
    }
  }

  return x;
}


/*
 * Same thing for a polynomial with 64bit coefficients
 */
static thvar_t map_bvpoly64(bv_solver_t *solver, bvpoly_buffer_t *b) {
  bv_vartable_t *vtbl;
  bvexp_table_t *etbl;
  bvarith64_buffer_t *eb;
  thvar_t x;
  uint32_t n, nbits, h;

  vtbl = &solver->vtbl;

  n = bvpoly_buffer_num_terms(b);
  nbits = bvpoly_buffer_bitsize(b);

  if (n == 0) {
    // return the constant 0b000 ..0
    x = get_bvconst64(vtbl, nbits, 0);
    return x;
  }

  if (n == 1) {
    x = bvpoly_buffer_var(b, 0);
    if (x == const_idx) {
      // constant
      x = get_bvconst64(vtbl, nbits, bvpoly_buffer_coeff64(b, 0));
      return x;
    }

    if (bvpoly_buffer_coeff64(b, 0) == 1) {
      return x;
    }
  }

  // expand p
  etbl = &solver->etbl;
  eb = &solver->exp64_buffer;
  expand_bvpoly64(etbl, eb, b);

  // check whether the expanded form simplifies to a constant
  // or a single variable
  x = simplify_expanded_poly64(solver, eb);

  if (x < 0) {
    h = hash_bvmlist64(eb->list, nbits);
    x = bvexp_table_find64(etbl, eb, h);
    if (x < 0) {
      // nothing equal to p in etbl
      x = get_bvpoly64(vtbl, b);
      bvexp_table_add64(etbl, x, eb, h);
    }
  }

  return x;
}



/*
 * Build the term c * x (as a polynomial)
 * - nbits = number of bits in c and x
 */
static thvar_t make_mono64(bv_solver_t *solver, uint32_t nbits, uint64_t c, thvar_t x) {
  bvpoly_buffer_t *b;

  b = &solver->buffer;
  reset_bvpoly_buffer(b, nbits);
  bvpoly_buffer_add_mono64(b, x, c);

  return get_bvpoly64(&solver->vtbl, b);
}


/*
 * Convert power-product p to a variable
 * - nbits = number of bits
 */
static thvar_t make_bvpprod(bv_vartable_t *vtbl, uint32_t nbits, pp_buffer_t *p) {
  thvar_t x;

  if (p->len == 1 && p->prod[0].exp == 1) {
    x = p->prod[0].var;
  } else {
    x = get_bvpprod(vtbl, nbits, p);
  }

  return x;
}


/*
 * Build the term (c * p)
 * - c is a 64bit constants
 * - p is a power product
 * - nbits = number of bits in c (and in all variables of p)
 */
static thvar_t map_const64_times_product(bv_solver_t *solver, uint32_t nbits, pp_buffer_t *p, uint64_t c) {
  bv_vartable_t *vtbl;
  bvexp_table_t *etbl;
  bvarith64_buffer_t *eb;
  thvar_t x;
  uint32_t h;

  assert(c == norm64(c, nbits));

  vtbl = &solver->vtbl;

  if (c == 0 || p->len == 0) {
    // constant
    x = get_bvconst64(vtbl, nbits, c);
    return x;
  }

  if (p->len == 1 && p->prod[0].exp == 1 && c == 1) {
    // monomial 1 * x
    x = p->prod[0].var;
    return x;
  }


  /*
   * Try expanded form
   */
  etbl = &solver->etbl;
  eb = &solver->exp64_buffer;
  expand_bvpprod64(etbl, eb, p, nbits, c);
  x = simplify_expanded_poly64(solver, eb);

  if (x < 0) {
    h = hash_bvmlist64(eb->list, nbits);
    x = bvexp_table_find64(etbl, eb, h);

    if (x < 0) {
      // not found in etbl: build c * p
      x = make_bvpprod(vtbl, nbits, p);
      if (c != 1) {
        x = make_mono64(solver, nbits, c, x);
      }
      bvexp_table_add64(etbl, x, eb, h);
    }
  }

  return x;
}


/*
 * Build the term c * x (as a polynomial)
 * - nbits = number of bits in c and x (nbits > 64)
 * - c must be normalized
 */
static thvar_t make_mono(bv_solver_t *solver, uint32_t nbits, uint32_t *c, thvar_t x) {
  bvpoly_buffer_t *b;

  b = &solver->buffer;
  reset_bvpoly_buffer(b, nbits);
  bvpoly_buffer_add_monomial(b, x, c);

  return get_bvpoly(&solver->vtbl, b);
}


/*
 * Build the term (c * p)
 * - c is a constants with more than 64bits
 * - p is a power product
 * - nbits = number of bits in c (and in all variables of p)
 */
static thvar_t map_const_times_product(bv_solver_t *solver, uint32_t nbits, pp_buffer_t *p, uint32_t *c) {
  bv_vartable_t *vtbl;
  bvexp_table_t *etbl;
  bvarith_buffer_t *eb;
  uint32_t w, h;
  thvar_t x;

  vtbl = &solver->vtbl;
  w = (nbits + 31) >> 5;

  if (bvconst_is_zero(c, w) || p->len == 0) {
    x = get_bvconst(vtbl, nbits, c);
    return x;
  }

  if (p->len == 1 && p->prod[0].exp == 1 && bvconst_is_one(c, w)) {
    x = p->prod[0].var;
    return x;
  }

  /*
   * Try expanded form
   */
  etbl = &solver->etbl;
  eb = &solver->exp_buffer;
  expand_bvpprod(etbl, eb, p, nbits, c);
  x = simplify_expanded_poly(solver, eb);

  if (x < 0) {
    // search for a matching x in etbl
    h = hash_bvmlist(eb->list, nbits);
    x = bvexp_table_find(etbl, eb, h);
    if (x < 0) {
      // not found
      x = make_bvpprod(vtbl, nbits, p);
      if (!bvconst_is_one(c, w)) {
        x = make_mono(solver, nbits, c, x);
      }
      bvexp_table_add(etbl, x, eb, h);
    }
  }

  return x;
}


/*
 * Check whether all literals in a[0 ... n-1] are constant
 */
static bool bvarray_is_constant(literal_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (var_of(a[i]) != const_bvar) return false;
  }

  return true;
}


/*
 * Convert constant array a[0 ... n-1] to a 64bit unsigned integer
 * - a[0] = low order bit
 * - a[n-1] = high order bit
 */
static uint64_t bvarray_to_uint64(literal_t *a, uint32_t n) {
  uint64_t c;

  assert(1 <= n && n <= 64);
  c = 0;
  while (n > 0) {
    n --;
    assert(a[n] == true_literal || a[n] == false_literal);
    c = (c << 1) | is_pos(a[n]);
  }

  return c;
}


/*
 * Convert constant array a[0 ... n-1] to a bitvector constant
 * - copy the result in c
 */
static void bvarray_to_bvconstant(literal_t *a, uint32_t n, bvconstant_t *c) {
  uint32_t i;

  assert(n > 64);

  bvconstant_set_all_zero(c, n);
  for (i=0; i<n; i++) {
    assert(a[i] == true_literal || a[i] == false_literal);
    if (a[i] == true_literal) {
      bvconst_set_bit(c->data, i);
    }
  }
}



/*
 * Bounds on (urem z y): if y != 0 then 0 <= (urem z y) < y
 * - x must be equal to (urem z y) for some z
 */
static void assert_urem_bounds(bv_solver_t *solver, thvar_t x, thvar_t y) {
  literal_t l0, l1;
  thvar_t zero;
  uint32_t n;

  assert(bvvar_tag(&solver->vtbl, x) == BVTAG_UREM && solver->vtbl.def[x].op[1] == y);

  n = bvvar_bitsize(&solver->vtbl, y);
  zero = get_zero(solver, n);
  l0 = bv_solver_create_eq_atom(solver, y, zero); // (y == 0)
  l1 = bv_solver_create_ge_atom(solver, x, y);    // (bvurem z y) >= y
  add_binary_clause(solver->core, l0, not(l1));
}


/*
 * Bounds on (srem z y) or  (smod z y):
 * - if y > 0 then - y < (srem z y) < y
 * - if y < 0 then   y < (srem z y) < - y
 * Same thing for (smod z y)
 *
 * We don't want to create the term -y so we add only half
 * of these constraints:
 *  y>0 ==> (srem z y) < y
 *  y<0 ==> y < (srem z y)
 */
static void assert_srem_bounds(bv_solver_t *solver, thvar_t x, thvar_t y) {
  literal_t l0, l1;
  thvar_t zero;
  uint32_t n;

  assert(bvvar_tag(&solver->vtbl, x) == BVTAG_SREM || bvvar_tag(&solver->vtbl, x) == BVTAG_SMOD);
  assert(solver->vtbl.def[x].op[1] == y);

  n = bvvar_bitsize(&solver->vtbl, y);
  zero = get_zero(solver, n);

  l0 = bv_solver_create_sge_atom(solver, zero, y); // (y <= 0)
  l1 = bv_solver_create_sge_atom(solver, x, y);    // (bvsrem z y) >= y
  add_binary_clause(solver->core, l0, not(l1));    // (y > 0) ==> (bvsrem z y) < y

  l0 = bv_solver_create_sge_atom(solver, y, zero); // (y >= 0)
  l1 = bv_solver_create_sge_atom(solver, y, x);    // y >= (bvsrem z y)
  add_binary_clause(solver->core, l0, not(l1));    // (y < 0) ==> y < (bvsrem z y)
}


/*
 * SIMPLIFICATIONS FOR IF-THEN-ELSE TERMS
 */

/*
 * Boolean if-then-else (ite c x y)
 * - c is a literal, x and y are true or false
 */
static literal_t bool_const_ite(literal_t c, bool x, bool y) {
  if (x == y) {
    return bool2literal(x);   // (ite c x x) --> x
  } else if (x) {
    return c;             // (ite c true false) --> c
  } else {
    return not(c);        // (ite c false true) --> not(c)
  }
}

/*
 * Convert (ite c x y) to a bitarray:
 * - n = number of bits
 * - x and y are bitvector constants
 * - c is a literal (other than true_literal and false_literal)
 * - x and y are distinct 
 */
static thvar_t create_ite_const64(bv_solver_t *solver, uint32_t n, literal_t c, uint64_t x, uint64_t y) {
  ivector_t *v;
  uint32_t i;

  assert(1 <= n && n <= 64 && x == norm64(x, n) && y == norm64(y, n) &&  x != y);
  assert(c != true_literal && c != false_literal);

  v = &solver->aux_vector;
  ivector_reset(v);
  for (i=0; i<n; i++) {
    ivector_push(v, bool_const_ite(c, tst_bit64(x, i), tst_bit64(y, i)));
  }
  assert(v->size == n && !bvarray_is_constant(v->data, n));
  return get_bvarray(&solver->vtbl, n, v->data);
}

static thvar_t create_ite_const(bv_solver_t *solver, uint32_t n, literal_t c, const uint32_t *x, const uint32_t *y) {
  ivector_t *v;
  uint32_t i;

  assert(n > 64 && bvconst_is_normalized(x, n) && bvconst_is_normalized(y, n));
  assert(c != true_literal && c != false_literal);

  v = &solver->aux_vector;
  ivector_reset(v);
  for (i=0; i<n; i++) {
    ivector_push(v, bool_const_ite(c, bvconst_tst_bit(x, i), bvconst_tst_bit(y, i)));
  }
  assert(v->size == n && !bvarray_is_constant(v->data, n));
  return get_bvarray(&solver->vtbl, n, v->data);
}


/*
 * Checks whether (ite c x y) simplifies to a literal
 * - c must not be true_literal or false_literal
 * - returns the literal if it does
 * - returns null_literal otherwise
 */
static literal_t try_bool_ite(literal_t c, literal_t x, literal_t y) {
  assert(c != true_literal && c != false_literal);

  // (ite c c y)       --> (ite c true y)
  // (ite c (not c) y) --> (ite c false y)
  if (c == x) { 
    x = true_literal;
  } else if (opposite(c, x)) {
    x = false_literal; 
  }

  // (ite c x c)       --> (ite c x false)
  // (ite c x (not c)) --> (ite c x true)
  if (c == y) {
    y = false_literal;
  } else if (opposite(c, y)) {
    y = true_literal;
  }

  // (ite c x x) --> x
  // (ite c true false) --> c
  // (ite c false true) --> (not c)
  if (x == y) return x;
  if (x == true_literal && y == false_literal) return c;
  if (x == false_literal && y == true_literal) return not(c);

  return null_literal;
}


/*
 * Try to convert (ite c x y) to a bitarray
 * - c is a literal other than true_literal and false_literal
 * - x is a bitvector constant of n bits
 * - y is a bitarray of n bits
 *
 * return null_thvar if this fails, a bitarray variable otherwise
 */
static thvar_t try_ite_const64(bv_solver_t *solver, uint32_t n, literal_t c, uint64_t x, const literal_t *y) {
  ivector_t *v;
  literal_t l;
  uint32_t i;
  thvar_t r;

  assert(1 <= n && n <= 64 && x == norm64(x, n));
  assert(c != true_literal && c != false_literal);

  r = null_thvar;
  v = &solver->aux_vector;  
  ivector_reset(v);
  for (i=0; i<n; i++) {
    l = bool2literal(tst_bit64(x, i));  // i-th bit of x converted to a literal
    l = try_bool_ite(c, l, y[i]);       // l = boolean (ite c x[i] y[i])
    if (l == null_literal) goto done;
    ivector_push(v, l);
  }
  
  assert(v->size == n);
  // we use bv_solver_create_bvarray here, because v may contain a constant array
  r = bv_solver_create_bvarray(solver, v->data, n);
  
 done:
  return r;
}

static thvar_t try_ite_const(bv_solver_t *solver, uint32_t n, literal_t c, const uint32_t *x, const literal_t *y) {
  ivector_t *v;
  literal_t l;
  uint32_t i;
  thvar_t r;

  assert(n > 64 && bvconst_is_normalized(x, n));
  assert(c != true_literal && c != false_literal);

  r = null_thvar;
  v = &solver->aux_vector;  
  ivector_reset(v);
  for (i=0; i<n; i++) {
    l = bool2literal(bvconst_tst_bit(x, i));   // i-th bit of x, converted to a literal
    l = try_bool_ite(c, l, y[i]);              // l = boolean (ite c x[i] y[i])
    if (l == null_literal) goto done;
    ivector_push(v, l);
  }
  
  assert(v->size == n);
  r = bv_solver_create_bvarray(solver, v->data, n);
  
 done:
  return r;
}


/*
 * Try to convert (ite c x y) to a bitarray
 * - c is a literal other than true_literal and false_literal
 * - x and y are literal arrays of n bits (distinct)
 */
static thvar_t try_ite_bitarrays(bv_solver_t *solver, uint32_t n, literal_t c, const literal_t *x, const literal_t *y) {
  ivector_t *v;
  literal_t l;
  uint32_t i;
  thvar_t r;

  assert(c != true_literal && c != false_literal);

  r = null_thvar;
  v = &solver->aux_vector;  
  ivector_reset(v);
  for (i=0; i<n; i++) {
    l = try_bool_ite(c, x[i], y[i]);
    if (l == null_literal) goto done;
    ivector_push(v, l);
  }
  
  assert(v->size == n);
  r = get_bvarray(&solver->vtbl, n, v->data);
  
 done:
  return r;
}




/********************************
 *  INTERNALIZATION FUNCTIONS   *
 *******************************/

/*
 * Create a new variable of n bits
 */
thvar_t bv_solver_create_var(bv_solver_t *solver, uint32_t n) {
  assert(n > 0);
  return make_bvvar(&solver->vtbl, n);
}


/*
 * Create a variable equal to constant c
 */
thvar_t bv_solver_create_const(bv_solver_t *solver, bvconst_term_t *c) {
  return get_bvconst(&solver->vtbl, c->bitsize, c->data);
}

thvar_t bv_solver_create_const64(bv_solver_t *solver, bvconst64_term_t *c) {
  return get_bvconst64(&solver->vtbl, c->bitsize, c->value);
}

/*
 * Zero constant:
 * - n = number of bits
 */
thvar_t bv_solver_create_zero(bv_solver_t *solver, uint32_t n) {
  return get_zero(solver, n);
}



/*
 * Internalize a polynomial p:
 * - map = variable renaming
 *   if p is of the form a_0 t_0 + ... + a_n t_n
 *   then map contains n+1 variables, and map[i] is the internalization of t_i
 * - exception: if t_0 is const_idx then map[0] = null_thvar
 */
thvar_t bv_solver_create_bvpoly(bv_solver_t *solver, bvpoly_t *p, thvar_t *map) {
  bvpoly_buffer_t *buffer;
  uint32_t i, n, nbits;

  n = p->nterms;
  nbits = p->bitsize;
  i = 0;

  buffer = &solver->buffer;
  reset_bvpoly_buffer(buffer, nbits);

  // deal with constant term if any
  if (p->mono[0].var == const_idx) {
    assert(map[0] == null_thvar);
    bvpoly_buffer_add_constant(buffer, p->mono[i].coeff);
    i ++;
  }

  // rest of p
  while (i < n) {
    assert(valid_bvvar(&solver->vtbl, map[i]));
    bvbuffer_add_mono(solver, buffer, map[i], p->mono[i].coeff);
    i ++;
  }

  normalize_bvpoly_buffer(buffer);
  return map_bvpoly(solver, buffer);
}

// Same thing: coefficients stored as 64bit integers
thvar_t bv_solver_create_bvpoly64(bv_solver_t *solver, bvpoly64_t *p, thvar_t *map) {
  bvpoly_buffer_t *buffer;
  uint32_t i, n, nbits;

  n = p->nterms;
  nbits = p->bitsize;
  i = 0;

  buffer = &solver->buffer;
  reset_bvpoly_buffer(buffer, nbits);

  // deal with constant term if any
  if (p->mono[0].var == const_idx) {
    assert(map[0] == null_thvar);
    bvpoly_buffer_add_const64(buffer, p->mono[i].coeff);
    i ++;
  }

  // rest of p
  while (i < n) {
    assert(valid_bvvar(&solver->vtbl, map[i]));
    bvbuffer_add_mono64(solver, buffer, map[i], p->mono[i].coeff);
    i ++;
  }

  normalize_bvpoly_buffer(buffer);
  return map_bvpoly64(solver, buffer);
}


/*
 * Product p = t_0^d_0 x ... x t_n ^d_n
 * - map = variable renaming: t_i is replaced by map[i]
 */
thvar_t bv_solver_create_pprod(bv_solver_t *solver, pprod_t *p, thvar_t *map) {
  bv_vartable_t *vtbl;
  pp_buffer_t *buffer;
  uint32_t *a;
  uint64_t c;
  uint32_t i, n, nbits, w;
  thvar_t x;

  vtbl = &solver->vtbl;
  buffer = &solver->prod_buffer;
  pp_buffer_reset(buffer);

  assert(p->len > 0);
  nbits = bvvar_bitsize(vtbl, map[0]);

  /*
   * We build a term (* constant (x_1 ^ d_1 ... x_k^d_k))
   * by replacing any constant map[i] by its value
   */
  if (nbits <= 64) {
    c = 1;
    n = p->len;
    for (i=0; i<n; i++) {
      x = map[i];
      if (bvvar_is_const64(vtbl, x)) {
        c *= upower64(bvvar_val64(vtbl, x), p->prod[i].exp);
      } else {
        pp_buffer_mul_varexp(buffer, x, p->prod[i].exp);
      }
    }

    // normalize c then build the term (c * p)
    c = norm64(c, nbits);
    x = map_const64_times_product(solver, nbits, buffer, c);

  } else {
    // use aux1 to store the constant
    w = (nbits + 31) >> 5;
    bvconstant_set_bitsize(&solver->aux1, nbits);
    a = solver->aux1.data;
    bvconst_set_one(a, w);

    n = p->len;
    for (i=0; i<n; i++) {
      x = map[i];
      if (bvvar_is_const(vtbl, x)) {
        bvconst_mulpower(a, w, bvvar_val(vtbl, x), p->prod[i].exp);
      } else {
        pp_buffer_mul_varexp(buffer, x, p->prod[i].exp);
      }
    }

    // normalize a then build the term (a * p)
    bvconst_normalize(a, nbits);
    x = map_const_times_product(solver, nbits, buffer, a);
  }

  return x;
}


/*
 * Internalize the bit array a[0 ... n-1]
 * - each element a[i] is a literal in the core
 */
thvar_t bv_solver_create_bvarray(bv_solver_t *solver, literal_t *a, uint32_t n) {
  bvconstant_t *aux;
  uint64_t c;
  thvar_t x;

  if (bvarray_is_constant(a, n)) {
    if (n <= 64) {
      c = bvarray_to_uint64(a, n);
      assert(c == norm64(c, n));
      x = get_bvconst64(&solver->vtbl, n, c);
    } else {
      aux = &solver->aux1;
      bvarray_to_bvconstant(a, n, aux);
      x = get_bvconst(&solver->vtbl, n, aux->data);
    }
  } else {
    x = get_bvarray(&solver->vtbl, n, a);
  }

  return x;
}



/*
 * Internalization of (ite c x y)
 */
thvar_t bv_solver_create_ite(bv_solver_t *solver, literal_t c, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  uint32_t n;
  thvar_t aux;
  bvvar_tag_t tagx, tagy;

  vtbl = &solver->vtbl;
  n = bvvar_bitsize(vtbl, x);
  assert(bvvar_bitsize(vtbl, y) == n);

  /// TODO: MORE SIMPLIFICATIONS TO A BIT ARRAY
  /// IF x and y are constants --> convert to an array of Booleans

  /// Other conversions may be possible (as in term_manager.c, mk_bv_ite).

  // Generic simplifications
  if (x == y) return x;
  if (c == true_literal) return x;
  if (c == false_literal) return y;

  // Check whether (ite c x y) simplifies to a bit array
  tagx = bvvar_tag(vtbl, x);
  tagy = bvvar_tag(vtbl, y);
  aux = null_thvar;
  switch (tagx) {
  case BVTAG_CONST64:
    assert(tagy != BVTAG_CONST);
    if (tagy == BVTAG_CONST64) {
      return create_ite_const64(solver, n, c, bvvar_val64(vtbl, x), bvvar_val64(vtbl, y));
    }
    if (tagy == BVTAG_BIT_ARRAY) {
      aux = try_ite_const64(solver, n, c, bvvar_val64(vtbl, x), bvvar_bvarray_def(vtbl, y));
      if (aux != null_thvar) return aux;
    }
    break;

  case BVTAG_CONST:
    assert(tagy != BVTAG_CONST64);
    if (tagy == BVTAG_CONST) {
      return create_ite_const(solver, n, c, bvvar_val(vtbl, x), bvvar_val(vtbl, y));
    }
    if (tagy == BVTAG_BIT_ARRAY) {
      aux = try_ite_const(solver, n, c, bvvar_val(vtbl, x), bvvar_bvarray_def(vtbl, y));
      if (aux != null_thvar) return aux;
    }
    break;

  case BVTAG_BIT_ARRAY:
    if (tagy == BVTAG_CONST64) {
      aux = try_ite_const64(solver, n, not(c), bvvar_val64(vtbl, y), bvvar_bvarray_def(vtbl, x));
    } else if (tagy == BVTAG_CONST) {
      aux = try_ite_const(solver, n, not(c), bvvar_val(vtbl, y), bvvar_bvarray_def(vtbl, x));
    } else if (tagy == BVTAG_BIT_ARRAY) {
      aux = try_ite_bitarrays(solver, n, c, bvvar_bvarray_def(vtbl, x), bvvar_bvarray_def(vtbl, y));
    }
    if (aux != null_thvar) return aux;
    break;

  default:
    break;
  }


  /*
   * Normalize: rewrite (ite (not b) x y) to (ite b y x)
   */
  if (is_neg(c)) {
    aux = x; x = y; y = aux;
    c = not(c);
  }

  return get_bvite(&solver->vtbl, n, c, x, y);
}


/*
 * Binary operators
 */

/*
 * Quotient x/y: unsigned, rounding toward 0
 * - simplify if x and y are both constants
 */
thvar_t bv_solver_create_bvdiv(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint64_t c;
  uint32_t n;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(n == bvvar_bitsize(vtbl, y));

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_udiv2z(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      // large constants
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_udiv2z(aux->data, n, bvvar_val(vtbl, x), bvvar_val(vtbl, y));
      bvconstant_normalize(aux);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  // no simplification
  return get_bvdiv(vtbl, n, x, y);
}


/*
 * Remainder of x/y: unsigned division, rounding toward 0
 */
thvar_t bv_solver_create_bvrem(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint64_t c;
  uint32_t n;
  thvar_t r;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(n == bvvar_bitsize(vtbl, y));

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_urem2z(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      // large constants
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_urem2z(aux->data, n, bvvar_val(vtbl, x), bvvar_val(vtbl, y));
      bvconstant_normalize(aux);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  if (equal_bvvar(solver, x, y)) {
    // (bvrem x x) == 0 (this holds even if x = 0)
    r = get_zero(solver, n);
  } else {
    // no simplification
    r = get_bvrem(&solver->vtbl, n, x, y);
    assert_urem_bounds(solver, r, y);  // EXPERIMENTAL
  }

  return r;
}


/*
 * Quotient x/y: signed division, rounding toward 0
 */
thvar_t bv_solver_create_bvsdiv(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint64_t c;
  uint32_t n;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(n == bvvar_bitsize(vtbl, y));

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_sdiv2z(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      // large constants
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_sdiv2z(aux->data, n, bvvar_val(vtbl, x), bvvar_val(vtbl, y));
      bvconstant_normalize(aux);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  // no simplification
  return get_bvsdiv(&solver->vtbl, n, x, y);
}


/*
 * Remainder of x/y: signed division, rounding toward 0
 */
thvar_t bv_solver_create_bvsrem(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint64_t c;
  uint32_t n;
  thvar_t r;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(n == bvvar_bitsize(vtbl, y));

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_srem2z(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      // large constants
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_srem2z(aux->data, n, bvvar_val(vtbl, x), bvvar_val(vtbl, y));
      bvconstant_normalize(aux);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  if (equal_bvvar(solver, x, y)) {
    // (bvsrem x x) == 0 (this holds even if x = 0)
    r = get_zero(solver, n);
  } else {
    // no simplification
    r = get_bvsrem(&solver->vtbl, n, x, y);
    assert_srem_bounds(solver, r, y);
  }

  return r;
}


/*
 * Remainder in x/y: signed division, rounding toward -infinity
 */
thvar_t bv_solver_create_bvsmod(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint64_t c;
  uint32_t n;
  thvar_t r;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(n == bvvar_bitsize(vtbl, y));

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_smod2z(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      // large constants
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_smod2z(aux->data, n, bvvar_val(vtbl, x), bvvar_val(vtbl, y));
      bvconstant_normalize(aux);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  if (equal_bvvar(solver, x, y)) {
    // (bvsmod x x) == 0 (this holds even if x = 0)
    r = get_zero(solver, n);
  } else {
    // no simplification
    r = get_bvsmod(&solver->vtbl, n, x, y);
    assert_srem_bounds(solver, r, y);
  }

  return r;
}


/*
 * Left shift, padding with zeros
 */
thvar_t bv_solver_create_bvshl(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint32_t n;
  uint64_t c;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(bvvar_bitsize(vtbl, y) == n);

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_lshl(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_lshl(aux->data, bvvar_val(vtbl, x), bvvar_val(vtbl, y), n);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  if (bvvar_is_zero(vtbl, x)) {
    // 0b000..0 unchanged by logical shift
    return x;
  }

  return get_bvshl(vtbl, n, x, y);
}


/*
 * Right shift, padding with zeros
 */
thvar_t bv_solver_create_bvlshr(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint32_t n;
  uint64_t c;


  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(bvvar_bitsize(vtbl, y) == n);

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_lshr(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_lshr(aux->data, bvvar_val(vtbl, x), bvvar_val(vtbl, y), n);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  if (bvvar_is_zero(vtbl, x)) {
    // 0b000..0 unchanged by logical shift
    return x;
  }

  return get_bvlshr(vtbl, n, x, y);
}


/*
 * Arithmetic right shift
 */
thvar_t bv_solver_create_bvashr(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint32_t n;
  uint64_t c;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(bvvar_bitsize(vtbl, y) == n);

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_ashr(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_ashr(aux->data, bvvar_val(vtbl, x), bvvar_val(vtbl, y), n);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  if (bvvar_is_zero(vtbl, x) || bvvar_is_minus_one(vtbl, x)) {
    // 0b000..0 and 0b11...1 are unchanged by any arithmetic shift
    return x;
  }

  return get_bvashr(vtbl, n, x, y);
}


/*
 * Return the i-th bit of theory variable x as a literal
 */
literal_t bv_solver_select_bit(bv_solver_t *solver, thvar_t x, uint32_t i) {
  bv_vartable_t *vtbl;
  literal_t l;

  assert(valid_bvvar(&solver->vtbl, x) && i < bvvar_bitsize(&solver->vtbl, x));

  // apply substitutions
  x = mtbl_get_root(&solver->mtbl, x);

  vtbl = &solver->vtbl;
  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    l = bvconst64_get_bit(vtbl, x, i);
    break;

  case BVTAG_CONST:
    l = bvconst_get_bit(vtbl, x, i);
    break;

  case BVTAG_BIT_ARRAY:
    l = bvarray_get_bit(vtbl, x, i);
    break;

  default:
    l = bvvar_get_bit(solver, x, i);
    break;
  }

  return l;
}


/*
 * ATOM CONSTRUCTORS
 */

/*
 * Atom (eq x y): no simplification
 */
static literal_t bv_solver_make_eq_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_atomtable_t *atbl;
  int32_t i;
  literal_t l;
  bvar_t v;

  atbl = &solver->atbl;
  i = get_bveq_atom(atbl, x, y);
  l = atbl->data[i].lit;

  if (l == null_literal) {
    /*
     * New atom: assign a fresh boolean variable for it
     */
    v = create_boolean_variable(solver->core);
    l = pos_lit(v);
    atbl->data[i].lit = l;
    attach_atom_to_bvar(solver->core, v, bvatom_idx2tagged_ptr(i));
    solver->stats.eq_atoms ++;
  }

  return l;
}


/*
 * Atom (eq x y): try to simplify
 */
literal_t bv_solver_create_eq_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
#if TRACE
  if (bvvar_bitsize(&solver->vtbl, x) == 1) {
    printf("---> create (bveq u!%"PRId32" u!%"PRId32")\n", x, y);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, x);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, y);
  }
#endif
  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  if (equal_bvvar(solver, x, y)) return true_literal;
  if (diseq_bvvar(solver, x, y)) return false_literal;
  //  if (bounds_imply_diseq(solver, x, y)) return false_literal;

  if (simplify_eq(solver, &x, &y)) {
    if (x == y) return true_literal;
    if (diseq_bvvar(solver, x, y)) return false_literal;
    //    if (bounds_imply_diseq(solver, x, y)) return false_literal;
  }

  return bv_solver_make_eq_atom(solver, x, y);
}


/*
 * Create (bvge x y)
 */
static literal_t bv_solver_make_ge_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_atomtable_t *atbl;
  int32_t i;
  literal_t l;
  bvar_t v;

  atbl = &solver->atbl;
  i = get_bvuge_atom(atbl, x, y);
  l = atbl->data[i].lit;
  if (l == null_literal) {
    /*
     * New atom: assign a fresh boolean variable for it
     */
    v = create_boolean_variable(solver->core);
    l = pos_lit(v);
    atbl->data[i].lit = l;
    attach_atom_to_bvar(solver->core, v, bvatom_idx2tagged_ptr(i));
    solver->stats.ge_atoms ++;
  }

  return l;
}


/*
 * Atom (bvge x y) (unsigned comparison)
 */
literal_t bv_solver_create_ge_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  literal_t l;

#if TRACE
  if (bvvar_bitsize(&solver->vtbl, x) == 1) {
    printf("---> create (bvge u!%"PRId32" u!%"PRId32")\n", x, y);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, x);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, y);
  }
#endif

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  /*
   * Rewrite rules:
   * (bvge 0b000...0 y)  <-->  (bveq 0b000...0 y)
   * (bvge x 0b111...1)  <-->  (bveq x 0b111...1)
   */
  if (bvvar_is_zero(&solver->vtbl, x) ||
      bvvar_is_minus_one(&solver->vtbl, y)) {
    return bv_solver_create_eq_atom(solver, x, y);
  }

  switch (check_bvuge(solver, x, y)) {
  case BVTEST_FALSE:
    l = false_literal;
    break;

  case BVTEST_TRUE:
    l = true_literal;
    break;

  default:
    l = bv_solver_make_ge_atom(solver, x, y);
    break;
  }

  return l;
}


/*
 * Create (bvsge x y): no simplification
 */
static literal_t bv_solver_make_sge_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_atomtable_t *atbl;
  int32_t i;
  literal_t l;
  bvar_t v;

  atbl = &solver->atbl;
  i = get_bvsge_atom(atbl, x, y);
  l = atbl->data[i].lit;
  if (l == null_literal) {
    /*
     * New atom: assign a fresh boolean variable for it
     */
    v = create_boolean_variable(solver->core);
    l = pos_lit(v);
    atbl->data[i].lit = l;
    attach_atom_to_bvar(solver->core, v, bvatom_idx2tagged_ptr(i));
    solver->stats.sge_atoms ++;
  }

  return l;
}


/*
 * Atom (bvsge x y) (signed comparison)
 */
literal_t bv_solver_create_sge_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  literal_t l;

#if TRACE
  if (bvvar_bitsize(&solver->vtbl, x) == 1) {
    printf("---> create (bvsge u!%"PRId32" u!%"PRId32")\n", x, y);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, x);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, y);
  }
#endif

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  /*
   * Rewrite rules:
   * (bvsge 0b100...0 y)  <-->  (bveq 0b100...0 y)
   * (bvsge x 0b011...1)  <-->  (bveq x 0b011...1)
   */
  if (bvvar_is_min_signed(&solver->vtbl, x) ||
      bvvar_is_max_signed(&solver->vtbl, y)) {
    return bv_solver_create_eq_atom(solver, x, y);
  }

  switch (check_bvsge(solver, x, y)) {
  case BVTEST_FALSE:
    l = false_literal;
    break;

  case BVTEST_TRUE:
    l = true_literal;
    break;

  default:
    l = bv_solver_make_sge_atom(solver, x, y);
    break;
  }

  return l;
}



/*
 * ATOM ASSERTIONS
 */

/*
 * Assert (x != y) where y is the constant 0b0000..0
 * - this special case is handled separately since we want to add the
 *   constraint (x != y) to the bound queue (unless it's already there).
 */
static void bv_solver_assert_neq0(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_atomtable_t *atbl;
  int32_t i;
  literal_t l;
  bvar_t v;

  assert(bvvar_is_zero(&solver->vtbl, y));
  atbl = &solver->atbl;
  i = get_bveq_atom(atbl, x, y);
  l = atbl->data[i].lit;
  if (l == null_literal) {
    /*
     * New atom: (x != 0) can't be in the bound queue
     */
    v = create_boolean_variable(solver->core);
    l = pos_lit(v);
    atbl->data[i].lit = l;
    attach_atom_to_bvar(solver->core, v, bvatom_idx2tagged_ptr(i));
    push_bvdiseq_bound(solver, x, y);

  } else if (! bvvar_is_nonzero(solver, x)) {
    /*
     * The bound (x != 0) is not in the queue yet: add it
     */
    push_bvdiseq_bound(solver, x, y);
  }

  add_unit_clause(solver->core, not(l));
}


/*
 * Assert (x == y) if tt is true
 * assert (x != y) if tt is false
 */
void bv_solver_assert_eq_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  literal_t l;

#if TRACE
  if (bvvar_bitsize(&solver->vtbl, x) == 1) {
    printf("---> assert (bveq u!%"PRId32" u!%"PRId32")\n", x, y);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, x);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, y);
  }
#endif

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  if (equal_bvvar(solver, x, y)) {
    if (! tt) add_empty_clause(solver->core);     // Contradiction
    return;
  }

  //  if (diseq_bvvar(solver, x, y) || bounds_imply_diseq(solver, x, y)) {
  if (diseq_bvvar(solver, x, y)) {
    if (tt) add_empty_clause(solver->core);       // Contradiction
    return;
  }

  // try to simplify
  if (simplify_eq(solver, &x, &y)) {
    // simplify may result in x == y
    if (x == y) {
      if (! tt) add_empty_clause(solver->core);
      return;
    }

    //    if (diseq_bvvar(solver, x, y) || bounds_imply_diseq(solver, x, y)) {
    if (diseq_bvvar(solver, x, y)) {
      if (tt) add_empty_clause(solver->core);
      return;
    }
  }


  /*
   * No contradiction detected
   */
  if (tt) {
    // x == y: merge the classes of x and y
    bv_solver_merge_vars(solver, x, y);
  } else if (bvvar_is_zero(&solver->vtbl, x)) {
    // y != 0
    bv_solver_assert_neq0(solver, y, x);
  } else if (bvvar_is_zero(&solver->vtbl, y)) {
    // x != 0
    bv_solver_assert_neq0(solver, x, y);
  } else {
    // Add the constraint (x != y)
    l = bv_solver_make_eq_atom(solver, x, y);
    add_unit_clause(solver->core, not(l));
  }
}


/*
 * Assert (bvge x y) if tt is true
 * Assert (not (bvge x y)) if tt is false
 */
void bv_solver_assert_ge_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  literal_t l;

#if TRACE
  if (bvvar_bitsize(&solver->vtbl, x) == 1) {
    printf("---> assert (bvge u!%"PRId32" u!%"PRId32")\n", x, y);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, x);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, y);
  }
#endif

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  /*
   * Rewrite rules:
   * (bvge 0b000...0 y)  <-->  (bveq 0b000...0 y)
   * (bvge x 0b111...1)  <-->  (bveq x 0b111...1)
   *
   * Also if we already have (bvge y x), we can rewrite (bvge x y) to (bveq x y).
   * We do this if tt is true or if introducing (bveq x y) may help.
   */
  if (bvvar_is_zero(&solver->vtbl, x) ||
      bvvar_is_minus_one(&solver->vtbl, y) ||
      (tt && bvuge_simplifies_to_bveq(solver, x, y))) {
    bv_solver_assert_eq_axiom(solver, x, y, tt);

  } else {
    switch (check_bvuge(solver, x, y)) {
    case BVTEST_FALSE:
      if (tt) add_empty_clause(solver->core); // x < y holds
      break;

    case BVTEST_TRUE:
      if (!tt) add_empty_clause(solver->core); // x >= y holds
      break;

    case BVTEST_UNKNOWN:
      l = bv_solver_make_ge_atom(solver, x, y);
      add_unit_clause(solver->core, signed_literal(l, tt));
      // push the bound into the queue
      if (is_bv_bound_pair(&solver->vtbl, x, y)) {
        push_bvuge_bound(solver, x, y);
      }
      break;
    }
  }
}


/*
 * Assert (bvsge x y) if tt is true
 * Assert (not (bvsge x y)) if tt is false
 */
void bv_solver_assert_sge_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  literal_t l;

#if TRACE
  if (bvvar_bitsize(&solver->vtbl, x) == 1) {
    printf("---> assert (bvsge u!%"PRId32" u!%"PRId32")\n", x, y);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, x);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, y);
  }
#endif

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  /*
   * Rewrite rules:
   * (bvsge 0b100...0 y)  <-->  (bveq 0b100...0 y)
   * (bvsge x 0b011...1)  <-->  (bveq x 0b011...1)
   *
   * Also, if we already have (bvsge y x), we can rewrite (bvsge x y) to (bveq x y).
   * We do this if tt is true or if introducing (bveq x y) may help.   
   */
  if (bvvar_is_min_signed(&solver->vtbl, x) ||
      bvvar_is_max_signed(&solver->vtbl, y) ||
      (tt && bvsge_simplifies_to_bveq(solver, x, y))) {
    bv_solver_assert_eq_axiom(solver, x, y, tt);

  } else {
    switch (check_bvsge(solver, x, y)) {
    case BVTEST_FALSE:
      if (tt) add_empty_clause(solver->core); // x < y holds
      break;

    case BVTEST_TRUE:
      if (!tt) add_empty_clause(solver->core); // x >= y holds
      break;

    case BVTEST_UNKNOWN:
      l = bv_solver_make_sge_atom(solver, x, y);
      add_unit_clause(solver->core, signed_literal(l, tt));
      // push the bound into the queue
      if (is_bv_bound_pair(&solver->vtbl, x, y)) {
        push_bvsge_bound(solver, x, y);
      }
      break;
    }
  }
}


/*
 * Assert that bit i of x is equal to tt
 */
void bv_solver_set_bit(bv_solver_t *solver, thvar_t x, uint32_t i, bool tt) {
  literal_t l;

  l = bv_solver_select_bit(solver, x, i);
  add_unit_clause(solver->core, signed_literal(l, tt));
}



/*
 * EGRAPH TERMS
 */

/*
 * Attach egraph term t to variable x
 */
void bv_solver_attach_eterm(bv_solver_t *solver, thvar_t x, eterm_t t) {
  attach_eterm_to_bvvar(&solver->vtbl, x, t);
}


/*
 * Get the egraph term attached to x
 * - return null_eterm if x has no eterm attached
 */
eterm_t bv_solver_eterm_of_var(bv_solver_t *solver, thvar_t x) {
  return bvvar_get_eterm(&solver->vtbl, x);
}



/*
 * COMPILATION RESULTS
 */

/*
 * Get the compilation of variable x
 * - return null_thvar if x is not compiled to anything
 */
thvar_t bv_solver_var_compiles_to(bv_solver_t *solver, thvar_t x) {
  bvc_t *c;
  thvar_t y;

  y = null_thvar;
  c = solver->compiler;
  if (c != NULL) {
    y = bvvar_compiles_to(c, x);
  }

  return y;
}





/*******************************************************
 *  EQUALITIES/DISEQUALITIES RECEIVED FROM THE EGRAPH  *
 ******************************************************/

/*
 * Equality atom created after bitblasting
 */
static literal_t on_the_fly_eq_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_atomtable_t *atbl;
  ivector_t *a, *b;
  int32_t i;
  literal_t l, l0;
  bvar_t v;

#if TRACE
  printf("---> on the fly (bveq u!%"PRId32" u!%"PRId32")\n", x, y);
  printf("     ");
  print_bv_solver_vardef(stdout, solver, x);
  printf("     ");
  print_bv_solver_vardef(stdout, solver, y);
#endif

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  if (equal_bvvar(solver, x, y)) return true_literal;
  if (diseq_bvvar(solver, x, y)) return false_literal;
  //  if (bounds_imply_diseq(solver, x, y)) return false_literal;

  if (simplify_eq(solver, &x, &y)) {
    if (x == y) return true_literal;
    if (diseq_bvvar(solver, x, y)) return false_literal;
    //    if (bounds_imply_diseq(solver, x, y)) return false_literal;
  }

  // check whether (bveq x y) exists already
  atbl = &solver->atbl;
  i = get_bveq_atom(atbl, x, y);
  l = atbl->data[i].lit;
  if (l == null_literal) {
    if (solver->bitblasted) {
      /*
       * After bitblasting
       */
      solver->stats.on_the_fly_atoms ++;

      bv_solver_bitblast_variable(solver, x);
      bv_solver_bitblast_variable(solver, y);
      a = &solver->a_vector;
      b = &solver->b_vector;
      collect_bvvar_literals(solver, x, a);
      collect_bvvar_literals(solver, y, b);
      assert(a->size == b->size && a->size > 0);

      l = bit_blaster_make_bveq(solver->blaster, a->data, b->data, a->size);
      atbl->data[i].lit = l;
      v = var_of(l);
      if (bvar_has_atom(solver->core, v)) {
        // need a fresh variable
        v = create_boolean_variable(solver->core);
        l0 = pos_lit(v);
        atbl->data[i].lit = l0;
        // assert (l == l0) in the core
        bit_blaster_eq(solver->blaster, l, l0);
        l = l0;
      }

    } else {
      /*
       * Before bitblasting: assign a fresh variable to the atom
       */
      solver->stats.eq_atoms ++;

      v = create_boolean_variable(solver->core);
      l = pos_lit(v);
      atbl->data[i].lit = l;
    }

    attach_atom_to_bvar(solver->core, v, bvatom_idx2tagged_ptr(i));

  }

  return l;
}


/*
 * Return the lemma cache
 * - allocate and initialize it if needed
 */
static cache_t *bv_solver_get_cache(bv_solver_t *solver) {
  cache_t *c;

  c = solver->cache;
  if (c == NULL) {
    c = (cache_t *) safe_malloc(sizeof(cache_t));
    // initialize then synchronize the cache with
    // the current push/pop level
    init_cache(c);
    cache_set_level(c, solver->base_level);
    solver->cache = c;
  }

  return c;
}


#if 0
/*
 * PROVISIONAL:
 * - try to check whether a bvequiv_lemma is needed
 */
static void diagnose_bvequiv(bv_solver_t *solver, thvar_t x1, thvar_t y1) {
  bv_atomtable_t *atbl;
  ivector_t *a, *b;
  thvar_t x, y;
  int32_t i;
  literal_t l, l1, l2;
  uint32_t j, n;

  x = mtbl_get_root(&solver->mtbl, x1);
  y = mtbl_get_root(&solver->mtbl, y1);

  if (equal_bvvar(solver, x, y)) {
    printf("---> BVSOLVER: bvequiv: (bveq u!%"PRId32" u!%"PRId32") is true (by mtbl_get_root)\n", x1, y1);
    fflush(stdout);
    return;
  }

  if (diseq_bvvar(solver, x, y)) {
    printf("---> BVSOLVER: bvequiv: (bveq u!%"PRId32" u!%"PRId32") is false (by diseq_bvvar)\n", x1, y1);
    fflush(stdout);
    return;
  }

  if (simplify_eq(solver, &x, &y)) {
    if (x == y) {
      printf("---> BVSOLVER: bvequiv: (bveq u!%"PRId32" u!%"PRId32") is true (by simplify_eq)\n", x1, y1);
      fflush(stdout);
      return;
    }
    if (diseq_bvvar(solver, x, y)) {
      printf("---> BVSOLVER: bvequiv: (bveq u!%"PRId32" u!%"PRId32") is false (by diseq_bvvar)\n", x1, y1);
      fflush(stdout);
      return;
    }
  }

  atbl = &solver->atbl;
  i = find_bveq_atom(atbl, x, y);
  if (i >= 0) {
    // the atom exists
    l = atbl->data[i].lit;
    switch (literal_value(solver->core, l)) {
    case VAL_FALSE:
      printf("---> BVSOLVER: bvequiv: (bveq u!%"PRId32" u!%"PRId32") is false (atom set to false)\n", x1, y1);
      fflush(stdout);
      return;

    case VAL_TRUE:
      printf("---> BVSOLVER: bvequiv: (bveq u!%"PRId32" u!%"PRId32") is true (atom set to true)\n", x1, y1);
      fflush(stdout);
      return;

    case VAL_UNDEF_FALSE:
    case VAL_UNDEF_TRUE:
      break;
    }
  }

  if (solver->bitblasted &&
      bvvar_is_bitblasted(&solver->vtbl, x) &&
      bvvar_is_bitblasted(&solver->vtbl, y)) {

    a = &solver->a_vector;
    b = &solver->b_vector;
    collect_bvvar_literals(solver, x, a);
    collect_bvvar_literals(solver, y, b);
    n = a->size;
    assert(b->size == n);

    for (j=0; j<n; j++) {
      l1 = a->data[j];
      l2 = b->data[j];
      if ((literal_value(solver->core, l1) == VAL_FALSE && literal_value(solver->core, l2) == VAL_TRUE)
          || (literal_value(solver->core, l1) == VAL_TRUE && literal_value(solver->core, l2) == VAL_FALSE)) {
        printf("---> BVSOLVER: bvequiv: (bveq u!%"PRId32" u!%"PRId32") is false (bits %"PRIu32" differ)\n", x1, y1, j);
        fflush(stdout);
        return;
      }
    }
  }
}

#endif


/*
 * Check whether the lemma (eq t1 t2) <=> (bveq x1 x2) is redundant.
 * - return true if the atom (bveq x1 x2) exists and is already true
 */
static bool bv_solver_bvequiv_redundant(bv_solver_t *solver, thvar_t x1, thvar_t x2) {
  bv_atomtable_t *atbl;
  thvar_t y1, y2;
  int32_t i;
  literal_t l;

  y1 = mtbl_get_root(&solver->mtbl, x1);
  y2 = mtbl_get_root(&solver->mtbl, x2);

  if (equal_bvvar(solver, y1, y2)) {
    return true;
  }

  if (simplify_eq(solver, &y1, &y2)  && y1 == y2) {
    return true;
  }

  atbl = &solver->atbl;
  i = find_bveq_atom(atbl, y1, y2);
  if (i >= 0) {
    l = atbl->data[i].lit;
    return literal_value(solver->core, l) == VAL_TRUE;
  }

  return false;
}


#if 0

// DISABLED THIS. DOES NOT SEEM TO HELP

/*
 * Variant of the bvequiv lemma: to avoid creating the egraph atom (eq t1 t2),
 * we can generate the clause (p1 /\ ... /\ p_n => (bveq x1 x2))
 * - where p1 /\ ... /\ p_n is the explanation for (t1 == t2)
 */
static void bv_solver_half_equiv_lemma(bv_solver_t *solver, thvar_t x1, thvar_t x2, eterm_t t1, eterm_t t2) {
  ivector_t *v;
  literal_t l;
  uint32_t i, n;

  l = on_the_fly_eq_atom(solver, x1, x2);
  v = &solver->aux_vector;
  ivector_reset(v);
  egraph_explain_term_eq(solver->egraph, t1, t2, v); // v contains p1 /\ ... /\ p_n

  n = v->size;
  for (i=0; i<n; i++) {
    v->data[i] = not(v->data[i]);
  }
  ivector_push(v, l);
  add_clause(solver->core, v->size, v->data);

  solver->stats.half_equiv_lemmas ++;
}

#endif

/*
 * Create the lemma (eq t1 t2) <=> (bveq x1 x2) if it's not redundant
 * where t1 = egraph term for x1 and t2 = egraph term for x2
 */
static void bv_solver_bvequiv_lemma(bv_solver_t *solver, thvar_t x1, thvar_t x2) {
  bv_vartable_t *vtbl;
  cache_t *cache;
  cache_elem_t *e;
  thvar_t aux;
  eterm_t t1, t2;
  literal_t l, eq;

  vtbl = &solver->vtbl;

  assert(solver->egraph != NULL && x1 != x2 &&
         bvvar_is_bitblasted(vtbl, x1) && bvvar_is_bitblasted(vtbl, x2));

  if (bv_solver_bvequiv_redundant(solver, x1, x2)) {
    return;
  }

  // normalize: we want x1 < x2
  if (x2 < x1) {
    aux = x1, x1 = x2; x2 = aux;
  }


#if TRACE
  t1 = bvvar_get_eterm(vtbl, x1);
  t2 = bvvar_get_eterm(vtbl, x2);
  printf("---> checking bvequiv lemma:\n");
  printf("     x1 = ");
  print_bv_solver_var(stdout, solver, x1);
  printf(", t1 = ");
  print_eterm_id(stdout, t1);
  printf("\n");
  printf("     x2 = ");
  print_bv_solver_var(stdout, solver, x2);
  printf(", t2 = ");
  print_eterm_id(stdout, t2);
  printf("\n");
#endif

  cache = bv_solver_get_cache(solver);
  e = cache_get(cache, BVEQUIV_LEMMA, x1, x2);
  if (e->flag == NEW_CACHE_ELEM) {
    // create the lemma
    e->flag = ACTIVE_BV_LEMMA;

    t1 = bvvar_get_eterm(vtbl, x1);
    t2 = bvvar_get_eterm(vtbl, x2);
    assert(t1 != null_eterm && t2 != null_eterm && t1 != t2);
    eq = egraph_make_simple_eq(solver->egraph, pos_occ(t1), pos_occ(t2));
    l = on_the_fly_eq_atom(solver, x1, x2);

    // add two clauses: (l => eq) and (eq => l)
    add_binary_clause(solver->core, not(l), eq);
    add_binary_clause(solver->core, l, not(eq));

    // update statistics
    solver->stats.equiv_lemmas ++;

#if 0
    printf("---> BVSOLVER: bvequiv lemma for ");
    print_bv_solver_var(stdout, solver, x1);
    printf(" ");
    print_bv_solver_var(stdout, solver, x2);
    printf("\n");
#endif

#if TRACE
    printf("---> bvequiv lemma:\n");
    printf("     x1 = ");
    print_bv_solver_var(stdout, solver, x1);
    printf(", t1 = ");
    print_eterm_id(stdout, t1);
    printf("\n");
    printf("     x2 = ");
    print_bv_solver_var(stdout, solver, x2);
    printf(", t2 = ");
    print_eterm_id(stdout, t2);
    printf("\n");
    printf("     (bveq x1 x2) = ");
    print_literal(stdout, l);
    printf("\n");
    printf("     (eq t1 t2) = ");
    print_literal(stdout, eq);
    printf("\n");
    printf("     ");
    print_bv_solver_vardef(stdout, solver, x1);
    printf("     ");
    print_bv_solver_vardef(stdout, solver, x2);
    printf("     ");
    print_eterm_def(stdout, solver->egraph, t1);
    printf("     ");
    print_eterm_def(stdout, solver->egraph, t2);
    printf("     ");
    print_literal(stdout, eq);
    printf(" := ");
    print_egraph_atom_of_literal(stdout, solver->egraph, eq);
    printf("\n\n");
#endif
  }
}


/*
 * Build the explanation for (x1 == x2) from the Egraph
 * - id = Egraph edge to get the explanation
 * - store the explanation in vector v
 */
static void bv_solver_explain_egraph_eq(bv_solver_t *solver, thvar_t x1, thvar_t x2, int32_t id, ivector_t *v) {
  eterm_t t1, t2;

  assert(v->size == 0);
  t1 = bvvar_get_eterm(&solver->vtbl, x1);
  t2 = bvvar_get_eterm(&solver->vtbl, x2);
  egraph_explain_term_eq(solver->egraph, t1, t2, id, v);
}


/*
 * Convert an explanation (l1 and ... and ln ==> false)
 * into the clause ((not l1) or  .... (not ln))
 * then add the clause as a theory conflict in the core.
 * - v contains the literals l1 ... ln
 */
static void bv_solver_add_conflict(bv_solver_t *solver, ivector_t *v) {
  uint32_t i, n;
  literal_t *a;

  n = v->size;
  a = v->data;
  for (i=0; i<n; i++) {
    a[i] = not(a[i]);
  }

  ivector_push(v, null_literal); // end marker
  record_theory_conflict(solver->core, v->data);
}


/*
 * Check whether x1 and x2 are distinct in the current assignment
 * - x1 and x2 are two variables attached to egraph terms t1 and t2
 * - the egraph has propagated the equality x1 == x2
 * - id = index of the egraph edge that propagated (x1 == x2)
 * - if (x1 != x2), generate a theory conflict and return true
 * - return false if there's no conflict
 */
static bool bv_solver_bvequiv_conflict(bv_solver_t *solver, thvar_t x1, thvar_t x2, int32_t id) {
  ivector_t *v;
  bv_atomtable_t *atbl;
  ivector_t *a, *b;
  thvar_t y1, y2;
  int32_t i;
  literal_t l, l1, l2;
  uint32_t j, n;

  v = &solver->aux_vector;
  ivector_reset(v);
  y1 = mtbl_get_root(&solver->mtbl, x1);
  y2 = mtbl_get_root(&solver->mtbl, x2);

  if (equal_bvvar(solver, y1, y2)) {
    goto no_conflict;
  }

  if (diseq_bvvar(solver, y1, y2)) {
    bv_solver_explain_egraph_eq(solver, x1, x2, id, v);
    goto conflict;
  }

  if (simplify_eq(solver, &y1, &y2)) {
    if (equal_bvvar(solver, y1, y2)) {
      goto no_conflict;
    }
    if (diseq_bvvar(solver, y1, y2)) {
      bv_solver_explain_egraph_eq(solver, x1, x2, id, v);
      goto conflict;
    }
  }

  atbl = &solver->atbl;
  i = find_bveq_atom(atbl, y1, y2);
  if (i >= 0) {
    /*
     * the atom l := (bveq y1 y2) exists, if l is false
     * the conflict is (t1 == t2) and (not l)
     */
    l = atbl->data[i].lit;
    if (literal_value(solver->core, l) == VAL_FALSE) {
      bv_solver_explain_egraph_eq(solver, x1, x2, id, v);
      ivector_push(v, not(l));
      goto conflict;
    }
  }

  if (solver->bitblasted &&
      bvvar_is_bitblasted(&solver->vtbl, y1) &&
      bvvar_is_bitblasted(&solver->vtbl, y2)) {

    a = &solver->a_vector;
    b = &solver->b_vector;
    collect_bvvar_literals(solver, y1, a);
    collect_bvvar_literals(solver, y2, b);
    n = a->size;
    assert(b->size == n);

    for (j=0; j<n; j++) {
      l1 = a->data[j];
      l2 = b->data[j];
      if (literal_value(solver->core, l1) == VAL_FALSE && literal_value(solver->core, l2) == VAL_TRUE) {
        bv_solver_explain_egraph_eq(solver, x1, x2, id, v);
        ivector_push(v, not(l1));
        ivector_push(v, l2);
        goto conflict;
      }

      if (literal_value(solver->core, l1) == VAL_TRUE && literal_value(solver->core, l2) == VAL_FALSE) {
        bv_solver_explain_egraph_eq(solver, x1, x2, id, v);
        ivector_push(v, l1);
        ivector_push(v, not(l2));
        goto conflict;
      }
    }
  }

 no_conflict:
  return false; // no conflict found

 conflict:
  solver->stats.equiv_conflicts ++;
  bv_solver_add_conflict(solver, v);

  return true;
}



/*
 * Process all assertions in the egraph queue
 * - we do nothing for disequalities or distinct
 * - disequalities are handled lazily in reconcile_model
 * - for all equalities (x == y) in the queue, we create the
 *   lemma (bveq x1 x2) <=> (t1 == t2)
 * - return false if a conflict is detected (and record a theory conflict in the core)
 */
static bool bv_solver_process_egraph_assertions(bv_solver_t *solver) {
  eassertion_t *a, *end;
  bool consistent;

  consistent = true;

  a = eassertion_queue_start(&solver->egraph_queue);
  end = eassertion_queue_end(&solver->egraph_queue);

  // first pass: check for conflicts
  while (a < end) {
    assert(eassertion_get_kind(a) == EGRAPH_VAR_EQ);
    if (bv_solver_bvequiv_conflict(solver, a->var[0], a->var[1], a->id)) {
      consistent = false;
      goto done;
    }
    a = eassertion_next(a);
  }

  // second pass: force equalities
  a = eassertion_queue_start(&solver->egraph_queue);
  while (a < end) {
    bv_solver_bvequiv_lemma(solver, a->var[0], a->var[1]);
    a = eassertion_next(a);
  }

 done:
  reset_eassertion_queue(&solver->egraph_queue);
  return consistent;
}


/*
 * Create a variable after bit-blasting (e.g., a skolem constant created
 * by the egraph + array solver).
 */
thvar_t bv_solver_create_on_the_fly_var(bv_solver_t *solver, uint32_t n) {
  bv_vartable_t *vtbl;
  thvar_t x;

#if TRACE
  printf("---> bv: create_var (%"PRIu32" bits)\n", n);
#endif

  assert(n > 0);
  vtbl = &solver->vtbl;
  x = make_bvvar(vtbl, n);
  if (solver->bitblasted) {
    bv_solver_bitblast_variable(solver, x);
  }

  return x;
}




/**********************
 *  SOLVER INTERFACE  *
 *********************/

/*
 * New round of assertions (before start_search)
 */
void bv_solver_start_internalization(bv_solver_t *solver) {
  solver->bitblasted = false;
}


/*
 * Prepare for search after internalization
 * - perform bit blasting
 * - if a conflict is detected by bit blasting, add the empty clause
 *   to the smt_core
 */
void bv_solver_start_search(bv_solver_t *solver) {
  bool feasible;

  solver->stats.equiv_lemmas = 0;
  solver->stats.equiv_conflicts = 0;
  solver->stats.half_equiv_lemmas = 0;
  solver->stats.interface_lemmas = 0;

  feasible = bv_solver_bitblast(solver);
  if (! feasible) {
    add_empty_clause(solver->core);
    return;
  }

  if (solver->egraph != NULL) {
    propagate_strong_equalities(solver);
  }
}


/*
 * Perform one round of propagation
 * - return false if a conflict was found
 * - return true otherwise
 */
bool bv_solver_propagate(bv_solver_t *solver) {
  if (eassertion_queue_is_nonempty(&solver->egraph_queue)) {
    assert(solver->bitblasted);
    return bv_solver_process_egraph_assertions(solver);
  }
  return true;
}

/*
 * Final check: nothing to do
 */
fcheck_code_t bv_solver_final_check(bv_solver_t *solver) {
  return FCHECK_SAT;
}

// clear: do nothing
void bv_solver_clear(bv_solver_t *solver) {
}

void bv_solver_increase_decision_level(bv_solver_t *solver) {
  solver->decision_level ++;

#if DUMP
  if (solver->core->stats.decisions == 1) {
    bv_solver_dump_state(solver, "after-bitblasting.dmp");
  }
#endif
}

void bv_solver_backtrack(bv_solver_t *solver, uint32_t backlevel) {
  assert(solver->base_level <= backlevel && backlevel < solver->decision_level);
  reset_eassertion_queue(&solver->egraph_queue);
  solver->decision_level = backlevel;
}


/*
 * Assert atom attached to literal l
 * This function is called when l is assigned to true by the core
 * - atom is the atom attached to a boolean variable v = var_of(l)
 * - if l is positive (i.e., pos_lit(v)), assert the atom
 * - if l is negative (i.e., neg_lit(v)), assert its negation
 * Return false if that causes a conflict, true otherwise.
 *
 * Do nothing (although we could try more simplification if
 * this is called before start_search).
 */
bool bv_solver_assert_atom(bv_solver_t *solver, void *a, literal_t l) {
  return true;
}


/*
 * This function should never be called.
 */
void bv_solver_expand_explanation(bv_solver_t *solver, literal_t l, void *expl, ivector_t *v) {
  assert(false);
}


/*
 * Support for theory-branching heuristic
 * - we don't do anything
 */
literal_t bv_solver_select_polarity(bv_solver_t *solver, void *a, literal_t l) {
  return l;
}



/**********************
 *  MAIN OPERATIONS   *
 *********************/

/*
 * Initialize a bit-vector solver
 * - core = the attached smt core
 * - egraph = the attached egraph (or NULL)
 */
void init_bv_solver(bv_solver_t *solver, smt_core_t *core, egraph_t *egraph) {
  solver->core = core;
  solver->egraph = egraph;
  solver->base_level = 0;
  solver->decision_level = 0;
  solver->bitblasted = false;
  solver->bbptr = 0;

  init_bv_vartable(&solver->vtbl);
  init_bv_atomtable(&solver->atbl);
  init_bvexp_table(&solver->etbl, &solver->vtbl);
  init_mtbl(&solver->mtbl);
  init_bv_bound_queue(&solver->bqueue);

  solver->compiler = NULL;
  solver->blaster = NULL;
  solver->remap = NULL;

  init_eassertion_queue(&solver->egraph_queue);
  solver->cache = NULL;

  init_bv_stats(&solver->stats);

  init_bv_queue(&solver->select_queue);
  init_bv_queue(&solver->delayed_mapped);
  init_bv_queue(&solver->delayed_blasted);
  init_bv_trail(&solver->trail_stack);

  init_bvpoly_buffer(&solver->buffer);
  init_pp_buffer(&solver->prod_buffer, 10);
  init_ivector(&solver->aux_vector, 0);
  init_bvconstant(&solver->aux1);
  init_bvconstant(&solver->aux2);
  init_bvconstant(&solver->aux3);
  bvexp_init_buffer(&solver->etbl, &solver->exp_buffer);
  bvexp_init_buffer64(&solver->etbl, &solver->exp64_buffer);
  init_bv_interval_stack(&solver->intv_stack);
  init_ivector(&solver->a_vector, 0);
  init_ivector(&solver->b_vector, 0);

  solver->val_map = NULL;

  solver->env = NULL;
}


/*
 * Attach a jump buffer for exception handling
 */
void bv_solver_init_jmpbuf(bv_solver_t *solver, jmp_buf *buffer) {
  solver->env = buffer;
}


/*
 * Delete solver
 */
void delete_bv_solver(bv_solver_t *solver) {
  // exp buffers must be deleted before etbl
  // and etbl must be deleted before vtbl
  delete_bvarith_buffer(&solver->exp_buffer);
  delete_bvarith64_buffer(&solver->exp64_buffer);

  delete_bvexp_table(&solver->etbl);
  delete_bv_vartable(&solver->vtbl);
  delete_bv_atomtable(&solver->atbl);
  delete_mtbl(&solver->mtbl);
  delete_bv_bound_queue(&solver->bqueue);

  if (solver->compiler != NULL) {
    delete_bv_compiler(solver->compiler);
    safe_free(solver->compiler);
    solver->compiler = NULL;
  }

  if (solver->blaster != NULL) {
    delete_bit_blaster(solver->blaster);
    safe_free(solver->blaster);
    solver->blaster = NULL;
  }

  if (solver->remap != NULL) {
    delete_remap_table(solver->remap);
    safe_free(solver->remap);
    solver->remap = NULL;
  }

  delete_eassertion_queue(&solver->egraph_queue);

  if (solver->cache != NULL) {
    delete_cache(solver->cache);
    safe_free(solver->cache);
    solver->cache = NULL;
  }

  delete_bv_queue(&solver->select_queue);
  delete_bv_queue(&solver->delayed_mapped);
  delete_bv_queue(&solver->delayed_blasted);
  delete_bv_trail(&solver->trail_stack);

  delete_bvpoly_buffer(&solver->buffer);
  delete_pp_buffer(&solver->prod_buffer);
  delete_ivector(&solver->aux_vector);
  delete_bvconstant(&solver->aux1);
  delete_bvconstant(&solver->aux2);
  delete_bvconstant(&solver->aux3);
  delete_bv_interval_stack(&solver->intv_stack);
  delete_ivector(&solver->a_vector);
  delete_ivector(&solver->b_vector);

  if (solver->val_map != NULL) {
    delete_bvconst_hmap(solver->val_map);
    safe_free(solver->val_map);
    solver->val_map = NULL;
  }
}



/********************
 *  PUSH/POP/RESET  *
 *******************/

/*
 * Start a new base level
 */
void bv_solver_push(bv_solver_t *solver) {
  uint32_t na, nv, nb, ns, ndm, ndb, bb;

  assert(solver->decision_level == solver->base_level &&
         all_bvvars_unmarked(solver));

  nv = solver->vtbl.nvars;
  na = solver->atbl.natoms;
  nb = solver->bqueue.top;
  ns = solver->select_queue.top;
  ndm = solver->delayed_mapped.top;
  ndb = solver->delayed_blasted.top;
  bb = solver->bbptr;

  bv_trail_save(&solver->trail_stack, nv, na, nb, ns, ndm, ndb, bb);

  mtbl_push(&solver->mtbl);

  if (solver->compiler != NULL) {
    bv_compiler_push(solver->compiler);
  }

  if (solver->remap != NULL) {
    remap_table_push(solver->remap);
  }

  if (solver->cache != NULL) {
    cache_push(solver->cache);
  }

  solver->base_level ++;
  bv_solver_increase_decision_level(solver);
}


/*
 * Remove all eterms whose id >= number of terms in the egraph
 * - if a bitvector variable x is kept after pop but the
 *   eterm[x] is removed from the egraph then we must clear
 *   solver->vtbl.eterm[x]
 */
static void bv_solver_remove_dead_eterms(bv_solver_t *solver) {
  uint32_t nterms;

  if (solver->egraph != NULL) {
    nterms = egraph_num_terms(solver->egraph);
    bv_vartable_remove_eterms(&solver->vtbl, nterms);
  }
}


/*
 * Remove the map of variables in the delayed_mapped queue
 * - n = number of variables in the queue at the corresponding push
 */
static void bv_solver_clean_delayed_mapped_vars(bv_solver_t *solver, uint32_t n) {
  bv_vartable_t *vtbl;
  bv_queue_t *dqueue;
  uint32_t i, top;
  thvar_t x;

  vtbl = &solver->vtbl;

  dqueue = &solver->delayed_mapped;
  top = dqueue->top;
  assert(n <= top);

  for (i=n; i<top; i++) {
    x = dqueue->data[i];
    assert(bvvar_is_mapped(vtbl, x));
    bvvar_reset_map(vtbl, x);
  }
}


/*
 * Remove the 'bitblasted' mark of variables in the delayed_blasted queue
 * - n = number of variables in the queue at the corresponding push
 */
static void bv_solver_clean_delayed_blasted_vars(bv_solver_t *solver, uint32_t n) {
  bv_vartable_t *vtbl;
  bv_queue_t *dqueue;
  uint32_t i, top;
  thvar_t x;

  vtbl = &solver->vtbl;

  dqueue = &solver->delayed_blasted;
  top = dqueue->top;
  assert(n <= top);

  for (i=n; i<top; i++) {
    x = dqueue->data[i];
    assert(bvvar_is_bitblasted(vtbl, x));
    bvvar_clr_bitblasted(vtbl, x);
  }
}



/*
 * Remove the map of variables that will be removed from the select queue
 * - n = number of variables that will remain in the select_queue
 *
 * This is called after bv_solver_clean_delayed_vars
 */
static void bv_solver_clean_select_queue(bv_solver_t *solver, uint32_t n) {
  bv_vartable_t *vtbl;
  bv_queue_t *squeue;
  uint32_t i, top;
  thvar_t x;

  vtbl = &solver->vtbl;
  squeue = &solver->select_queue;
  top = squeue->top;

  assert(n <= top);
  for (i=n; i<top; i++) {
    x = squeue->data[i];
    if (bvvar_is_mapped(vtbl, x)) {
      bvvar_reset_map(vtbl, x);
    }
  }
}



/*
 * Return to the previous base level
 */
void bv_solver_pop(bv_solver_t *solver) {
  bv_trail_t *top;

  assert(solver->base_level > 0 &&
         solver->base_level == solver->decision_level);

  solver->base_level --;
  bv_solver_backtrack(solver, solver->base_level);

  if (solver->remap != NULL) {
    remap_table_pop(solver->remap);
  }

  top = bv_trail_top(&solver->trail_stack);

  if (solver->compiler != NULL) {
    bv_compiler_pop(solver->compiler, top->nvars);
  }

  if (solver->cache != NULL) {
    cache_pop(solver->cache);
  }

  assert(all_bvvars_unmarked(solver));

  /*
   * Remove maps and bitblasted marks of delayed variables.
   */
  bv_solver_clean_delayed_mapped_vars(solver, top->ndelayed_mapped);
  solver->delayed_mapped.top = top->ndelayed_mapped;
  bv_solver_clean_delayed_blasted_vars(solver, top->ndelayed_blasted);
  solver->delayed_blasted.top = top->ndelayed_blasted;

  /*
   * remove vars in the select queue
   */
  bv_solver_clean_select_queue(solver, top->nselects);
  solver->select_queue.top = top->nselects;

  // remove the expanded forms
  // must be done before remove the variables form vtbl
  bvexp_table_remove_vars(&solver->etbl, top->nvars);

  bv_solver_remove_bounds(solver, top->nbounds);
  bv_vartable_remove_vars(&solver->vtbl, top->nvars);
  bv_atomtable_remove_atoms(&solver->atbl, top->natoms);
  bv_solver_remove_dead_eterms(solver);

  // restore the bitblast pointer
  solver->bbptr = top->nbblasted;

  mtbl_pop(&solver->mtbl);

  bv_trail_pop(&solver->trail_stack);
}


/*
 * Reset: remove all variables and atoms
 * and reset base_level to 0.
 */
void bv_solver_reset(bv_solver_t *solver) {
  /*
   * The exp buffers must be deleted first since they use
   * solver->etbl.store/store64, and reset_bvexp_table will reset
   * these two stores. We reconstruct the two buffers after
   * reset_bvexp_table.
   */
  delete_bvarith_buffer(&solver->exp_buffer);
  delete_bvarith64_buffer(&solver->exp64_buffer);
  reset_bvexp_table(&solver->etbl);
  bvexp_init_buffer(&solver->etbl, &solver->exp_buffer);
  bvexp_init_buffer64(&solver->etbl, &solver->exp64_buffer);

  reset_bv_vartable(&solver->vtbl);
  reset_bv_atomtable(&solver->atbl);
  reset_mtbl(&solver->mtbl);
  reset_bv_bound_queue(&solver->bqueue);

  if (solver->compiler != NULL) {
    delete_bv_compiler(solver->compiler);
    safe_free(solver->compiler);
    solver->compiler = NULL;
  }

  if (solver->blaster != NULL) {
    delete_bit_blaster(solver->blaster);
    safe_free(solver->blaster);
    solver->blaster = NULL;
  }

  if (solver->remap != NULL) {
    delete_remap_table(solver->remap);
    safe_free(solver->remap);
    solver->remap = NULL;
  }

  reset_eassertion_queue(&solver->egraph_queue);

  if (solver->cache != NULL) {
    delete_cache(solver->cache);
    safe_free(solver->cache);
    solver->cache = NULL;
  }

  reset_bv_stats(&solver->stats);
  reset_bv_queue(&solver->select_queue);
  reset_bv_queue(&solver->delayed_mapped);
  reset_bv_queue(&solver->delayed_blasted);
  reset_bv_trail(&solver->trail_stack);

  reset_bvpoly_buffer(&solver->buffer, 32);
  pp_buffer_reset(&solver->prod_buffer);
  ivector_reset(&solver->aux_vector);
  reset_bv_interval_stack(&solver->intv_stack);
  ivector_reset(&solver->a_vector);
  ivector_reset(&solver->b_vector);

  if (solver->val_map != NULL) {
    delete_bvconst_hmap(solver->val_map);
    safe_free(solver->val_map);
    solver->val_map = NULL;
  }

  solver->base_level = 0;
  solver->decision_level = 0;
  solver->bitblasted = false;
  solver->bbptr = 0;
}



/**********************
 *  EGRAPH INTERFACE  *
 *********************/

/*
 * Assertion (eq x y) from the Egraph
 * - process it immediately if we're at the base level
 * - otherwise add it to the egraph assertion queue
 */
void bv_solver_assert_var_eq(bv_solver_t *solver, thvar_t x, thvar_t y, int32_t id) {
  assert(bvvar_has_eterm(&solver->vtbl, x) && bvvar_has_eterm(&solver->vtbl, y));

#if TRACE
  printf("---> bvsolver: received egraph equality: ");
  print_bv_solver_var(stdout, solver, x);
  printf(" = ");
  print_bv_solver_var(stdout, solver, y);
  printf("\n");
#endif

  if (! solver->bitblasted) {
    assert(solver->decision_level == solver->base_level);
    bv_solver_assert_eq_axiom(solver, x, y, true);
  } else {
    eassertion_push_eq(&solver->egraph_queue, x, y, id);
  }
}

/*
 * Assertion (x != y) from the Egraph
 */
void bv_solver_assert_var_diseq(bv_solver_t *solver, thvar_t x, thvar_t y, composite_t *hint) {
  assert(bvvar_has_eterm(&solver->vtbl, x) && bvvar_has_eterm(&solver->vtbl, y));

#if TRACE
  printf("---> bvsolver: received egraph disequality: ");
  print_bv_solver_var(stdout, solver, x);
  printf(" != ");
  print_bv_solver_var(stdout, solver, y);
  printf("\n");
#endif

  if (! solver->bitblasted) {
    assert(solver->decision_level == solver->base_level);
    bv_solver_assert_eq_axiom(solver, x, y, false);
  }
}


/*
 * Assert that a[i] != a[j] for all pairs i, j
 */
void bv_solver_assert_var_distinct(bv_solver_t *solver, uint32_t n, thvar_t *a, composite_t *hint) {
  uint32_t i, j;
  thvar_t x, y;

  if (! solver->bitblasted) {
    assert(solver->decision_level == solver->base_level);

    for (i=0; i<n; i++) {
      x = a[i];
      assert(bvvar_has_eterm(&solver->vtbl, x));
      for (j=i+1; j<n; j++) {
        y = a[j];
        bv_solver_assert_eq_axiom(solver, x, y, false);
      }
    }
  }
}


/*
 * Check whether x and y are distinct at the base level
 */
bool bv_solver_check_disequality(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  ivector_t *a, *b;
  literal_t l;

  vtbl = &solver->vtbl;

  if (solver->bitblasted && bvvar_is_bitblasted(vtbl, x) && bvvar_is_bitblasted(vtbl, y)) {
    // both x and y are already bitblasted
    a = &solver->a_vector;
    b = &solver->b_vector;
    collect_bvvar_literals(solver, x, a);
    collect_bvvar_literals(solver, y, b);
    assert(a->size == b->size && a->size > 0);

    l = bit_blaster_eval_bveq(solver->blaster, a->size, a->data, b->data);

    return (l == false_literal);
  } else {
    x = mtbl_get_root(&solver->mtbl, x);
    y = mtbl_get_root(&solver->mtbl, y);
    if (equal_bvvar(solver, x, y)) return false;
    if (diseq_bvvar(solver, x, y)) return true;
    if (bounds_imply_diseq(solver, x, y)) return true;

    if (simplify_eq(solver, &x, &y)) {
      if (x == y) return false;
      if (diseq_bvvar(solver, x, y)) return true;
      if (bounds_imply_diseq(solver, x, y)) return true;
    }
  }

  return false;
}

literal_t bv_solver_select_eq_polarity(bv_solver_t *solver, thvar_t x, thvar_t y, literal_t l) {
  return l;
}


/*
 * Check whether x is a constant
 */
bool bv_solver_var_is_constant(bv_solver_t *solver, thvar_t x) {
  return is_constant(&solver->vtbl, x);
}


/*********************
 *  RECONCILE MODEL  *
 ********************/

/*
 * Check whether x1 and x2 are equal in the model
 * - return false if x1 and x2 have different bitsize
 * - otherwise, check the literal values in the core
 */
static bool bv_solver_var_equal_in_model(bv_solver_t *solver, thvar_t x1, thvar_t x2) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  smt_core_t *core;
  literal_t *m1, *m2;
  literal_t s1, s2;
  literal_t l1, l2;
  bval_t v1, v2;
  uint32_t i, n;

  assert(solver->bitblasted);

  vtbl = &solver->vtbl;

  n = bvvar_bitsize(vtbl, x1);
  if (n != bvvar_bitsize(vtbl, x2)) {
    return false;
  }

  m1 = bvvar_get_map(vtbl, x1);
  m2 = bvvar_get_map(vtbl, x2);

  assert(m1 != NULL && m2 != NULL);

  rmap = solver->remap;
  core = solver->core;

  for (i=0; i<n; i++) {
    s1 = m1[i];
    s2 = m2[i];
    l1 = remap_table_find(rmap, s1);
    l2 = remap_table_find(rmap, s2);
    assert(l1 != null_literal && l2 != null_literal);
    v1 = literal_value(core, l1);
    v2 = literal_value(core, l2);
    assert(bval_is_def(v1) && bval_is_def(v2));
    if (v1 != v2) {
      return false;
    }
  }

  return true;
}


/*
 * 32bit word of x's value formed of bits[k ... k+31]
 * - k must be smaller than x's bit size
 * - if k+31 >= bitsize, then the value is padded with 0s
 */
static uint32_t bvsolver_word_value_in_model(bv_solver_t *solver, thvar_t x, uint32_t k) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  smt_core_t *core;
  literal_t *mx;
  literal_t s, l;
  uint32_t i, n, c;

  assert(solver->bitblasted);

  vtbl = &solver->vtbl;
  rmap = solver->remap;
  core = solver->core;

  n = bvvar_bitsize(vtbl, x);
  mx = bvvar_get_map(vtbl, x);
  assert(mx != NULL && k<n);

  c = 0;

  if (k + 32 <= n) {
    n = k+32;
  }

  for (i=k; i<n; i++) {
    s = mx[i];
    l = remap_table_find(rmap, s);
    assert(l != null_literal && literal_is_assigned(core, l));
    if (literal_value(core, l) == VAL_TRUE) {
      c |= 1; // set low-order bit
    }
    c <<= 1;
  }

  return c;
}



/*
 * Hash function: if x and y have the same value then hash(x) == hash(y).
 * This is based on Jensen's lookup3 code (public domain).
 */
#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))

#define mix(a,b,c) \
{ \
  a -= c;  a ^= rot(c, 4);  c += b; \
  b -= a;  b ^= rot(a, 6);  a += c; \
  c -= b;  c ^= rot(b, 8);  b += a; \
  a -= c;  a ^= rot(c,16);  c += b; \
  b -= a;  b ^= rot(a,19);  a += c; \
  c -= b;  c ^= rot(b, 4);  b += a; \
}

#define final(a,b,c) \
{ \
  c ^= b; c -= rot(b,14); \
  a ^= c; a -= rot(c,11); \
  b ^= a; b -= rot(a,25); \
  c ^= b; c -= rot(b,16); \
  a ^= c; a -= rot(c,4);  \
  b ^= a; b -= rot(a,14); \
  c ^= b; c -= rot(b,24); \
}

static uint32_t bvsolver_model_hash(bv_solver_t *solver, thvar_t x) {
  uint32_t k, n;
  uint32_t a, b, c;

  n = bvvar_bitsize(&solver->vtbl, x);
  k = 0;

  a = b = c = 0xdeadbeef + (n << 2);

  while (n > 96) { // more than 3 words
    a += bvsolver_word_value_in_model(solver, x, k);
    b += bvsolver_word_value_in_model(solver, x, k+32);
    c += bvsolver_word_value_in_model(solver, x, k+64);
    mix(a, b, c);
    n -= 96;
    k += 96;
  }

  // last three words
  assert(1 <= n && n <= 96);
  switch ((n+31) >> 5) {
  case 3: c += bvsolver_word_value_in_model(solver, x, k+64);
  case 2: b += bvsolver_word_value_in_model(solver, x, k+32);
  case 1: a += bvsolver_word_value_in_model(solver, x, k);
    final(a, b, c);
    break;
  default:
    assert(false);
    break;
  }

  return c;
}



/*
 * Check whether x is a root variable:
 * - x is root if it has an egraph term t and x is the theory
 *   variable in the class of t.
 */
static bool is_root_var(bv_solver_t *solver, thvar_t x) {
  egraph_t *egraph;
  eterm_t t;

  t = bvvar_get_eterm(&solver->vtbl, x);
  egraph = solver->egraph;
  return (t != null_eterm) &&
    (egraph_class_thvar(egraph, egraph_term_class(egraph, t)) == x);
}


#if 0

/*
 * For testing: print the parent vectors of all variables in vector v
 */
static void show_parents_of_class(bv_solver_t *solver, int32_t *v) {
  uint32_t i, n;
  int32_t x;
  eterm_t t;

  n = iv_size(v);
  assert(n >= 2);
  for (i=0; i<n; i++) {
    x = v[i];
    t = bvvar_get_eterm(&solver->vtbl, x);
    printf("--- root bvvar = ");
    print_bv_solver_var(stdout, solver, x);
    printf("---\n");
    print_class_of_term(stdout, solver->egraph, t);
    print_parents_of_term(stdout, solver->egraph, t);
  }
}

#endif


/*
 * Heuristic: search for the best interface equality in a class
 * - v = vector
 */
static bool interface_eq_in_class(bv_solver_t *solver, int32_t *v) {
  thvar_t x1, x2;
  eterm_t t1, t2;
  literal_t l, eq;

  assert(iv_size(v) >= 2);

  x1 = v[0];
  x2 = v[1];
  t1 = bvvar_get_eterm(&solver->vtbl, x1);
  t2 = bvvar_get_eterm(&solver->vtbl, x2);
  assert(t1 != null_eterm && t2 != null_eterm && t1 != t2);
  eq = egraph_make_simple_eq(solver->egraph, pos_occ(t1), pos_occ(t2));
  l = on_the_fly_eq_atom(solver, x1, x2);

  // add two clauses: (l => eq) and (eq => l)
  add_binary_clause(solver->core, not(l), eq);
  add_binary_clause(solver->core, l, not(eq));

#if 0
  printf("---> BVSOLVER: interface_eq lemma for ");
  print_bv_solver_var(stdout, solver, x1);
  printf(" ");
  print_bv_solver_var(stdout, solver, x2);
  printf("\n");
#endif

  // update statistics
  solver->stats.interface_lemmas ++;

  return true;
}


/*
 * Search for inconsistencies between the egraph and the bitvector model
 * - An inconsistency is a pair of bit-vector variables x and y
 *   such that x and y have the same value in the solver but
 *   term_of(x) and term_of(y) are in different classes in the egraph.
 * - To resolve inconsistencies we add the lemma
 *     (bveq x y) <=> (eq term_of(x) term_of(y))
 * - max_eq = bound on the number of lemma instances
 * - Return the number of instances created
 */
uint32_t bv_solver_reconcile_model(bv_solver_t *solver, uint32_t max_eq) {
  ipart_t partition;
  uint32_t i, n;
  uint32_t neq;

  assert(max_eq > 0);

#if TRACE
  printf("\n---> bv: reconcile model\n");
  fflush(stdout);
#endif


  /*
   * Build partitions:
   * - two variables x and y are in the same class if both are root
   *   variables and they have the same value in the bit assignment.
   * - i.e., the egraph model says that x != y but the
   *   bitvector model says that x = y
   */
  init_int_partition(&partition, 0, solver, (ipart_hash_fun_t) bvsolver_model_hash,
                     (ipart_match_fun_t) bv_solver_var_equal_in_model);

  n = solver->vtbl.nvars;
  for (i=1; i<n; i++) {
    if (is_root_var(solver, i)) {
      int_partition_add(&partition, i);
    }
  }

  n = int_partition_nclasses(&partition);

#if 0
  for (i=0; i<n; i++) {
    printf("Class %"PRIu32"\n", i);
    show_parents_of_class(solver, partition.classes[i]);
    printf("\n");
  }
#endif

  /*
   * Process the classes: generate the 'best' conflict pairs
   * in each class?
   */
  neq = 0;
  for (i=0; i<n; i++) {
    if (interface_eq_in_class(solver, partition.classes[i])) {
      neq ++;
      if (neq == max_eq) break;
    }
  }


  delete_int_partition(&partition);

  return neq;
}




/*
 * REVISED INTERFACE/RECONCILIATION INTERFACE
 */

/*
 * Prepare model and release model: nothing to do
 * - equal_in_model is the same as bv_solver_var_equal_in_model (defined above)
 */
static void bv_solver_prepare_model(bv_solver_t *solver) {
#if 0
  // PROVISIONAL
  free_bool_vars_t fv;
  uint32_t i, n, frees;

  n = solver->core->nvars;
  init_free_bool_vars(&fv, n);
  collect_free_bool_vars(&fv, solver->core);

  frees = 0;
  for (i=0; i<n; i++) {
    frees += fv.free[i];
  }

  printf("Free/total boolean vars: %"PRIu32"/%"PRIu32"\n", frees, n);

  delete_free_bool_vars(&fv);
#endif
}

static void bv_solver_release_model(bv_solver_t *solver) {
}


/*
 * Add the lemma l => x1 != x2
 * - i.e., the clause (not l) or (not (bveq x1 x2))
 * - if equiv is true: can add the reverse implication too?
 */
static void bv_solver_gen_interface_lemma(bv_solver_t *solver, literal_t l, thvar_t x1, thvar_t x2, bool equiv) {
  literal_t eq;

  assert(solver->egraph != NULL && x1 != x2 &&
         bvvar_is_bitblasted(&solver->vtbl, x1) &&
         bvvar_is_bitblasted(&solver->vtbl, x2));

#if 0
  printf("---> BVSOLVER: interface lemma for u!%"PRId32" and u!%"PRId32"\n", x1, x2);
  print_bv_solver_var_litarray(stdout, solver, x1);
  print_bv_solver_var_litarray(stdout, solver, x2);
  printf("\n");
#endif

  eq = on_the_fly_eq_atom(solver, x1, x2);
  add_binary_clause(solver->core, not(l), not(eq));  // l => not eq
  if (equiv) {
    add_binary_clause(solver->core, l, eq);   // not l => eq
  }

  solver->stats.interface_lemmas ++;

#if TRACE
  printf("---> Bv solver: reconciliation lemma for u!%"PRId32" /= u!%"PRId32" ----\n", x1, x2);
  printf("     Antecedent:\n");
  printf("     ");
  print_literal(stdout, l);
  printf(" := ");
  print_egraph_atom_of_literal(stdout, solver->egraph, l);
  printf("\n");
  printf("     (bveq u!%"PRId32" u!%"PRId32") = ", x1, x2);
  print_literal(stdout, eq);
  printf("\n");
  printf("     Clause: (OR ");
  print_literal(stdout, not(l));
  printf(" ");
  print_literal(stdout, not(eq));
  printf(")\n\n");
#endif
}


/*
 * Build the model partition and return it
 */
static ipart_t *bv_solver_build_model_partition(bv_solver_t *solver) {
  ipart_t *partition;
  uint32_t i, n;

  partition = (ipart_t *) safe_malloc(sizeof(ipart_t));
  init_int_partition(partition, 0, solver, (ipart_hash_fun_t) bvsolver_model_hash,
                     (ipart_match_fun_t) bv_solver_var_equal_in_model);

  n = solver->vtbl.nvars;
  for (i=1; i<n; i++) {
    if (is_root_var(solver, i)) {
      int_partition_add(partition, i);
    }
  }

  return partition;
}


/*
 * Delete the partition
 */
static void bv_solver_release_model_partition(bv_solver_t *solver, ipart_t *p) {
  delete_int_partition(p);
  safe_free(p);
}



/************************
 *  MODEL CONSTRUCTION  *
 ***********************/

/*
 * Interface function: nothing to do
 */
void bv_solver_build_model(bv_solver_t *solver) {
  // do nothing
}


/*
 * Get the internal val_map
 * - allocate and initialize it if needed
 */
static bvconst_hmap_t *bv_solver_get_val_map(bv_solver_t *solver) {
  bvconst_hmap_t *tmp;

  tmp = solver->val_map;
  if (tmp == NULL) {
    tmp = (bvconst_hmap_t *) safe_malloc(sizeof(bvconst_hmap_t));
    init_bvconst_hmap(tmp, 0); // default size?
    solver->val_map = tmp;
  }

  return tmp;
}


/*
 * Copy the value of x in c:
 * - x must be marked as bitblasted
 * - the value is read from the SAT solver assignment
 * - return true if the value is available/false otherwise
 */
static bool get_bitblasted_var_value(bv_solver_t *solver, thvar_t x, uint32_t *c) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  literal_t *mx;
  uint32_t i, n;
  literal_t s, l;

  vtbl = &solver->vtbl;
  rmap = solver->remap;

  n = bvvar_bitsize(vtbl, x);

  assert(bvvar_is_bitblasted(vtbl, x));

  mx = bvvar_get_map(vtbl, x);
  assert(mx != NULL && rmap != NULL);

  for (i=0; i<n; i++) {
    s = mx[i];
    l = remap_table_find(rmap, s);
    if (l == null_literal) return false;

    switch (literal_value(solver->core, l)) {
    case VAL_FALSE:
      bvconst_clr_bit(c, i);
      break;

    case VAL_TRUE:
      bvconst_set_bit(c, i);
      break;

    case VAL_UNDEF_FALSE:
    case VAL_UNDEF_TRUE:
      return false;
    }
  }

  bvconst_normalize(c, n);

  return true;
}


/*
 * Copy the value of bit-array a[0 ... n-1] into c
 * - return true if all literals have a value in the sat solver
 * - return false otherwise
 */
static bool get_bvarray_value(bv_solver_t *solver, literal_t *a, uint32_t n, uint32_t *c) {
  uint32_t i;

  for (i=0; i<n; i++) {
    switch (literal_value(solver->core, a[i])) {
    case VAL_FALSE:
      bvconst_clr_bit(c, i);
      break;

    case VAL_TRUE:
      bvconst_set_bit(c, i);
      break;

    case VAL_UNDEF_FALSE:
    case VAL_UNDEF_TRUE:
      return false;
    }
  }

  bvconst_normalize(c, n);

  return true;
}



/*
 * Copy a 64bit constant into word array c
 * - c is large enough for n bits
 */
static void copy_constant64(uint32_t *c, uint64_t a, uint32_t n) {
  assert(1 <= n && n <= 64 && a == norm64(a, n));

  c[0] = (uint32_t) (a & 0xFFFFFFFF);
  if (n > 32) {
    c[1] = (uint32_t) (a >> 32);
  }
}


/*
 * Same thing for a constant of more than 32 bits
 */
static void copy_constant(uint32_t *c, uint32_t *a, uint32_t n) {
  uint32_t k;

  assert(n > 64 && bvconst_is_normalized(a, n));

  k = (n + 31) >> 5;
  bvconst_set(c, k, a);
  assert(bvconst_is_normalized(c, n));
}


/*
 * Convert word array c to a 64bit constant
 * - n = number of bits in c
 */
static uint64_t convert_to64(uint32_t *c, uint32_t n) {
  uint64_t a;

  assert(1 <= n && n <= 64);

  a = c[0];
  if (n > 32) {
    a |= ((uint64_t) c[1]) << 32;
  }

  assert(a == norm64(a, n));

  return a;
}



/*
 * Get the value of x in the current Boolean assignment
 * - if x is bitblasted, get it from the pseudo-map of x
 * - otherwise, compute it from x's definition
 *   then store the value in the internal val_map
 * - make a copy in vector c:
 *   c must be an array of k 32bit words where k = ceil(nbits of x/32)
 *
 * - return true if the value can be computed, false otherwise
 */
static bool bv_solver_get_variable_value(bv_solver_t *solver, thvar_t x, uint32_t *c);


/*
 * Get the value of x, store the opposite  in c
 * - n = number of bits
 * - return true if found, false otherwise
 */
static bool bv_solver_neg_value(bv_solver_t *solver, thvar_t x, uint32_t n, uint32_t *c) {
  uint32_t aux[4];
  uint32_t *a;
  uint32_t k;
  bool found;

  k = (n + 31) >> 5;
  a = aux;
  if (k > 4) {
    a = (uint32_t *) safe_malloc(k * sizeof(uint32_t));
  }

  found = bv_solver_get_variable_value(solver, x, c);
  if (found) {
    bvconst_negate2(c, k, a);
    bvconst_normalize(c, n);
  }

  if (k > 4) {
    safe_free(a);
  }

  return found;
}


/*
 * Get the values of x[0] and x[1] the apply op to this pair of values
 * - store the result in c
 * - n = number of bits in x[0] and x[1]
 */
static bool bv_solver_binop_value(bv_solver_t *solver, bvvar_tag_t op, thvar_t x[2], uint32_t n, uint32_t *c) {
  uint32_t aux1[4];
  uint32_t aux2[4];
  uint32_t *a1, *a2;
  uint32_t k;
  bool found;


  k = (n + 31) >> 5;
  a1 = aux1;
  a2 = aux2;
  if (k >4) {
    a1 = (uint32_t *) safe_malloc(k * sizeof(uint32_t));
    a2 = (uint32_t *) safe_malloc(k * sizeof(uint32_t));
  }

  found = bv_solver_get_variable_value(solver, x[0], a1)
    && bv_solver_get_variable_value(solver, x[1], a2);

  if (found) {
    switch (op) {
    case BVTAG_UDIV:
      bvconst_udiv2z(c, n, a1, a2);
      break;

    case BVTAG_UREM:
      bvconst_urem2z(c, n, a1, a2);
      break;

    case BVTAG_SDIV:
      bvconst_sdiv2z(c, n, a1, a2);
      break;

    case BVTAG_SREM:
      bvconst_srem2z(c, n, a1, a2);
      break;

    case BVTAG_SMOD:
      bvconst_smod2z(c, n, a1, a2);
      break;

    case BVTAG_SHL:
      bvconst_lshl(c, a1, a2, n);
      break;

    case BVTAG_LSHR:
      bvconst_lshr(c, a1, a2, n);
      break;

    case BVTAG_ASHR:
      bvconst_ashr(c, a1, a2, n);
      break;

    case BVTAG_ADD:
      bvconst_add2(c, k, a1, a2);
      break;

    case BVTAG_SUB:
      bvconst_sub2(c, k, a1, a2);
      break;

    case BVTAG_MUL:
      bvconst_mul2(c, k, a1, a2);
      break;

    default:
      assert(false);
      break;
    }

    bvconst_normalize(c, n);
  }


  if (k > 4) {
    safe_free(a1);
    safe_free(a2);
  }

  return found;
}



/*
 * Evaluate polynomial p
 * - store the result in c
 * - n = number of bits
 */
static bool bv_solver_poly64_value(bv_solver_t *solver, bvpoly64_t *p, uint32_t n, uint32_t *c) {
  uint32_t aux[2];
  uint64_t a, b;
  uint32_t i, nterms;
  bool found;

  assert(1 <= n && n <= 64 && n == p->bitsize && p->nterms > 0);

  nterms = p->nterms;

  i = 0;
  a = 0;
  if (p->mono[0].var == 0) {
    a = p->mono[0].coeff;
    i = 1;
  }

  aux[0] = 0;
  aux[1] = 0;

  found = true;

  while (i < nterms) {
    found = bv_solver_get_variable_value(solver, p->mono[i].var, aux);
    if (!found) goto done;
    assert(bvconst_is_normalized(aux, n));
    b = convert_to64(aux, n);
    a += p->mono[i].coeff * b;
    i ++;
  }

  assert(found);

  a = norm64(a, n);
  copy_constant64(c, a, n);

  assert(bvconst_is_normalized(c, n));

 done:
  return found;
}


static bool bv_solver_poly_value(bv_solver_t *solver, bvpoly_t *p, uint32_t n, uint32_t *c) {
  uint32_t aux[4];
  uint32_t *a;
  uint32_t k, i, nterms;
  bool found;

  assert(64 < n && n == p->bitsize && p->nterms > 0);

  nterms = p->nterms;

  k = (n + 31) >> 5;
  a = aux;
  if (k > 4) {
    a = (uint32_t *) safe_malloc(k * sizeof(uint32_t));
  }

  i = 0;
  bvconst_clear(c, k);
  if (p->mono[0].var == const_idx) {
    bvconst_set(c, k, p->mono[0].coeff);
    i = 1;
  }

  found = true;

  while (i < nterms) {
    found = bv_solver_get_variable_value(solver, p->mono[i].var, a);
    if (!found) goto done;
    assert(bvconst_is_normalized(a, n));
    bvconst_addmul(c, k, a, p->mono[i].coeff);
    i ++;
  }

  assert(found);
  bvconst_normalize(c, n);

 done:
  if (k > 4) {
    safe_free(a);
  }

  return found;
}



/*
 * Evaluate power-product p
 */
static bool bv_solver_pprod_value(bv_solver_t *solver, pprod_t *p, uint32_t n, uint32_t *c) {
  uint32_t aux[4];
  uint32_t *a;
  uint32_t k, i, nterms;
  bool found;

  nterms = p->len;

  k = (n + 31) >> 5;
  a = aux;
  if (k > 4) {
    a = (uint32_t *) safe_malloc(k * sizeof(uint32_t));
  }

  found = true;
  bvconst_set_one(c, k);
  for (i=0; i<nterms; i++) {
    found = bv_solver_get_variable_value(solver, p->prod[i].var, a);
    if (!found) goto done;
    assert(bvconst_is_normalized(a, n));
    bvconst_mulpower(c, k, a, p->prod[i].exp);
  }

  assert(found);
  bvconst_normalize(c, n);

 done:
  if (k > 4) {
    safe_free(a);
  }

  return found;
}




/*
 * Compute the value of x based on its definition
 * - check the val_map first: if x's value is in the map return it
 * - otherwise, compute if then add it to the val_map
 *
 * - return true if the value can be computed/false otherwise
 */
static bool bv_solver_compute_var_value(bv_solver_t *solver, thvar_t x, uint32_t *c) {
  bv_vartable_t *vtbl;
  bvconst_hmap_t *val_map;
  bvconst_hmap_rec_t *r;
  uint32_t n;
  bvvar_tag_t op;
  bool found;

  vtbl = &solver->vtbl;
  val_map = bv_solver_get_val_map(solver);

  n = bvvar_bitsize(vtbl, x);
  r = bvconst_hmap_find(val_map, x);

  if (r != NULL) {
    // found value in val_map
    assert(r->key == x && r->nbits == n && n>0);
    if (n <= 64) {
      copy_constant64(c, r->val.c, n);
    } else {
      copy_constant(c, r->val.p, n);
    }
    return true;
  }


  /*
   * Compute the value
   */
  found = false; // stop GCC warning

  op = bvvar_tag(vtbl, x);
  switch (op) {
  case BVTAG_VAR:
    // assign 0b000... as default value
    bvconst_clear(c, (n + 31) >> 5);
    found = true;
    break;

  case BVTAG_CONST64:
    copy_constant64(c, bvvar_val64(vtbl, x), n);
    found = true;
    break;

  case BVTAG_CONST:
    copy_constant(c, bvvar_val(vtbl, x), n);
    found = true;
    break;

  case BVTAG_BIT_ARRAY:
    found = get_bvarray_value(solver, bvvar_bvarray_def(vtbl, x), n, c);
    break;

  case BVTAG_POLY64:
    found = bv_solver_poly64_value(solver, bvvar_poly64_def(vtbl, x), n, c);
    break;

  case BVTAG_POLY:
    found = bv_solver_poly_value(solver, bvvar_poly_def(vtbl, x), n, c);
    break;

  case BVTAG_PPROD:
    found = bv_solver_pprod_value(solver, bvvar_pprod_def(vtbl, x), n, c);
    break;

  case BVTAG_ITE:
    found = false;
    break;

  case BVTAG_UDIV:
  case BVTAG_UREM:
  case BVTAG_SDIV:
  case BVTAG_SREM:
  case BVTAG_SMOD:
  case BVTAG_SHL:
  case BVTAG_LSHR:
  case BVTAG_ASHR:
  case BVTAG_ADD:
  case BVTAG_SUB:
  case BVTAG_MUL:
    found = bv_solver_binop_value(solver, op, bvvar_binop(vtbl, x), n, c);
    break;

  case BVTAG_NEG:
    found = bv_solver_neg_value(solver, bvvar_binop(vtbl, x)[0], n, c);
    break;
  }

  if (found) {
    // store the value in val_map
    if (n <= 64) {
      bvconst_hmap_set_val64(val_map, x, convert_to64(c, n), n);
    } else {
      bvconst_hmap_set_val(val_map, x, c, n);
    }
  }

  return found;
}


static bool bv_solver_get_variable_value(bv_solver_t *solver, thvar_t x, uint32_t *c) {
  if (bvvar_is_bitblasted(&solver->vtbl, x)) {
    return get_bitblasted_var_value(solver, x, c);
  } else {
    return bv_solver_compute_var_value(solver, x, c);
  }
}



/*
 * Copy the value assigned to x in the model into buffer c
 * - return true if the value is available
 * - return false if the solver has no model
 */
bool bv_solver_value_in_model(bv_solver_t *solver, thvar_t x, bvconstant_t *c) {
  uint32_t n;
  bool found;

  n = bvvar_bitsize(&solver->vtbl, x);
  assert(n > 0);

  bvconstant_set_bitsize(c, n);
  found = bv_solver_get_variable_value(solver, x, c->data);
  assert(!found || bvconst_is_normalized(c->data, n));

  return found;
}



/*
 * Delete whatever is used to store the model
 */
void bv_solver_free_model(bv_solver_t *solver) {
  if (solver->val_map != NULL) {
    delete_bvconst_hmap(solver->val_map);
    safe_free(solver->val_map);
    solver->val_map = NULL;
  }
}






/*******************************
 *  INTERNALIZATION INTERFACE  *
 ******************************/

static bv_interface_t bv_solver_context = {
  (create_bv_var_fun_t) bv_solver_create_var,
  (create_bv_const_fun_t) bv_solver_create_const,
  (create_bv64_const_fun_t) bv_solver_create_const64,
  (create_bv_zero_fun_t) bv_solver_create_zero,
  (create_bv_poly_fun_t) bv_solver_create_bvpoly,
  (create_bv64_poly_fun_t) bv_solver_create_bvpoly64,
  (create_bv_pprod_fun_t) bv_solver_create_pprod,
  (create_bv_array_fun_t) bv_solver_create_bvarray,
  (create_bv_ite_fun_t) bv_solver_create_ite,
  (create_bv_binop_fun_t) bv_solver_create_bvdiv,
  (create_bv_binop_fun_t) bv_solver_create_bvrem,
  (create_bv_binop_fun_t) bv_solver_create_bvsdiv,
  (create_bv_binop_fun_t) bv_solver_create_bvsrem,
  (create_bv_binop_fun_t) bv_solver_create_bvsmod,
  (create_bv_binop_fun_t) bv_solver_create_bvshl,
  (create_bv_binop_fun_t) bv_solver_create_bvlshr,
  (create_bv_binop_fun_t) bv_solver_create_bvashr,

  (select_bit_fun_t) bv_solver_select_bit,
  (create_bv_atom_fun_t) bv_solver_create_eq_atom,
  (create_bv_atom_fun_t) bv_solver_create_ge_atom,
  (create_bv_atom_fun_t) bv_solver_create_sge_atom,

  (assert_bv_axiom_fun_t) bv_solver_assert_eq_axiom,
  (assert_bv_axiom_fun_t) bv_solver_assert_ge_axiom,
  (assert_bv_axiom_fun_t) bv_solver_assert_sge_axiom,
  (set_bit_fun_t) bv_solver_set_bit,

  (attach_eterm_fun_t) bv_solver_attach_eterm,
  (eterm_of_var_fun_t) bv_solver_eterm_of_var,

  (build_model_fun_t) bv_solver_build_model,
  (free_model_fun_t) bv_solver_free_model,
  (bv_val_in_model_fun_t) bv_solver_value_in_model,
};


/*
 * Return the interface descriptor
 */
bv_interface_t *bv_solver_bv_interface(bv_solver_t *solver) {
  return &bv_solver_context;
}



/********************************
 *  SMT AND CONTROL INTERFACES  *
 *******************************/

static th_ctrl_interface_t bv_solver_control = {
  (start_intern_fun_t) bv_solver_start_internalization,
  (start_fun_t) bv_solver_start_search,
  (propagate_fun_t) bv_solver_propagate,
  (final_check_fun_t) bv_solver_final_check,
  (increase_level_fun_t) bv_solver_increase_decision_level,
  (backtrack_fun_t) bv_solver_backtrack,
  (push_fun_t) bv_solver_push,
  (pop_fun_t) bv_solver_pop,
  (reset_fun_t) bv_solver_reset,
  (clear_fun_t) bv_solver_clear,
};

static th_smt_interface_t bv_solver_smt = {
  (assert_fun_t) bv_solver_assert_atom,
  (expand_expl_fun_t) bv_solver_expand_explanation,
  (select_pol_fun_t) bv_solver_select_polarity,
  NULL,
  NULL,
};


/*
 * Get the control and smt interfaces
 */
th_ctrl_interface_t *bv_solver_ctrl_interface(bv_solver_t *solver) {
  return &bv_solver_control;
}

th_smt_interface_t *bv_solver_smt_interface(bv_solver_t *solver) {
  return &bv_solver_smt;
}



/*********************************************
 *  SATELLITE SOLVER INTERFACE (FOR EGRAPH)  *
 ********************************************/

static th_egraph_interface_t bv_solver_egraph = {
  (assert_eq_fun_t) bv_solver_assert_var_eq,
  (assert_diseq_fun_t) bv_solver_assert_var_diseq,
  (assert_distinct_fun_t) bv_solver_assert_var_distinct,
  (check_diseq_fun_t) bv_solver_check_disequality,
  (is_constant_fun_t) bv_solver_var_is_constant,
  (expand_eq_exp_fun_t) bv_solver_expand_th_explanation,
  (reconcile_model_fun_t) bv_solver_reconcile_model,
  (prepare_model_fun_t) bv_solver_prepare_model,
  (equal_in_model_fun_t) bv_solver_var_equal_in_model,
  (gen_inter_lemma_fun_t) bv_solver_gen_interface_lemma,
  (release_model_fun_t) bv_solver_release_model,
  (build_partition_fun_t) bv_solver_build_model_partition,
  (free_partition_fun_t) bv_solver_release_model_partition,
  (attach_to_var_fun_t) bv_solver_attach_eterm,
  (get_eterm_fun_t) bv_solver_eterm_of_var,
  (select_eq_polarity_fun_t) bv_solver_select_eq_polarity,
};


static bv_egraph_interface_t bv_solver_bv_egraph = {
  (make_bv_var_fun_t) bv_solver_create_on_the_fly_var,
  (bv_val_fun_t) bv_solver_value_in_model,
};


/*
 * Get the egraph interfaces
 */
th_egraph_interface_t *bv_solver_egraph_interface(bv_solver_t *solver) {
  return &bv_solver_egraph;
}

bv_egraph_interface_t *bv_solver_bv_egraph_interface(bv_solver_t *solver) {
  return &bv_solver_bv_egraph;
}




#if DUMP

/*******************
 *  FOR DEBUGGING  *
 ******************/

static void bv_solver_dump_state(bv_solver_t *solver, const char *filename) {
  FILE *f;

  f = fopen(filename, "w");
  if (f != NULL) {
    //    fprintf(f, "\n--- Terms ---\n");
    //    print_term_table(f, __yices_globals.terms);
    fprintf(f, "\n--- Bitvector Partition ---\n");
    print_bv_solver_partition(f, solver);
    fprintf(f, "\n--- Bitvector Variables ---\n");
    print_bv_solver_vars(f, solver);
    fprintf(f, "\n--- Bitvector Atoms ---\n");
    print_bv_solver_atoms(f, solver);
    fprintf(f, "\ntotal: %"PRIu32" atoms\n", solver->atbl.natoms);
    fprintf(f, "\n--- Bitvector Bounds ---\n");
    print_bv_solver_bounds(f, solver);
    fprintf(f, "\n--- DAG ---\n");
    print_bv_solver_dag(f, solver);
    if (solver->blaster != NULL) {
      fprintf(f, "\n--- Gates ---\n");
      print_gate_table(f, solver->blaster->htbl);
    }
    fprintf(f, "\n--- Clauses ---\n");
    print_clauses(f, solver->core);
    fprintf(f, "\n");
    fclose(f);
  }
}

#endif
