/*
 * FRONT-END FOR DIFFERENCE LOGIC SOLVERS
 */

#include <assert.h>

#include "memalloc.h"
#include "hash_functions.h"
#include "dl_front_end.h"



/*
 * VARIABLE TABLE
 */

/*
 * Initialize: n = initial size
 */
static void init_dl_vartable(dl_vartable_t *tbl, uint32_t n) {
  assert(n < MAX_DL_VARTABLE_SIZE);
  tbl->nvars = 0;
  tbl->size = n;
  tbl->triple = (dl_triple_t *) safe_malloc(n * sizeof(dl_triple_t));
  init_int_htbl(&tbl->htbl, 0);
}

/*
 * Make the table 50% larger
 */
static void extend_dl_vartable(dl_vartable_t *tbl) {
  uint32_t n;

  n = tbl->size + 1;
  n += n >> 1;
  if (n >= MAX_DL_VARTABLE_SIZE) {
    out_of_memory();
  }
  tbl->triple = (dl_triple_t *) safe_realloc(tbl->triple, n * sizeof(dl_triple_t));
}

/*
 * Delete the table
 */
static void delete_dl_vartable(dl_vartable_t *tbl) {
  safe_free(tbl->triple);
  tbl->triple = NULL;
  delete_int_htbl(&tbl->htbl);
}

/*
 * Empty the table
 */
static void reset_dl_vartable(dl_vartable_t *tbl) {
  tbl->nvars = 0;
  reset_int_htbl(&tbl->htbl);
}

/*
 * Allocate a new variable index i
 */
static int32_t dl_vartable_alloc(dl_vartable_t *tbl) {
  int32_t i;

  i = tbl->nvars;
  if (i == tbl->size) {
    extend_dl_vartable(tbl);
  }
  assert(i < tbl->size);
  tbl->nvars = i + 1;

  return i;
}


/*
 * Hash code for triple t
 */
static uint32_t hash_dl_triple(dl_triple_t *t) {
  uint32_t h1, h2;

  q_hash_decompose(&t->q, &h1, &h2);
  return jenkins_hash_quad(t->target, t->source, h1, h2, 0x78312a3e);
}

static bool eq_dl_triple(dl_triple_t *t1, dl_triple_t *t2) {
  return t1->target == t2->target && t1->source == t2->source && q_eq(&t1->q, &t2->q);
}


/*
 * Hash consing
 */
typedef struct dl_var_hobj_s {
  int_hobj_t m;
  dl_vartable_t *table;
  dl_triple_t triple;
} dl_var_hobj_t;


// Hash code
static uint32_t hash_dl_var(dl_var_hobj_t *o) {
  return hash_dl_triple(&o->triple);
}

// Equality test
static bool eq_dl_var(dl_var_hobj_t *o, thvar_t x) {
  dl_vartable_t *tbl;

  tbl = o->table;
  assert(0 <= x && x < tbl->nvars);
  return eq_dl_triple(&o->triple, tbl->triple + x);
}

// Build new variable 
static int32_t build_dl_var(dl_var_hobj_t *o) {
  dl_vartable_t *tbl;
  int32_t x;

  tbl = o->table;
  x = dl_vartable_alloc(tbl);
  assert(0 <= x && x < tbl->size);
  tbl->triple[x].target = o->triple.target;
  tbl->triple[x].source = o->triple.source;
  q_init(&tbl->triple[x].q);
  q_set(&tbl->triple[x].q, &o->triple.q);

  return x;
}


/*
 * Get the variable for triple [target, source, c]
 */
static int32_t get_dl_var(dl_vartable_t *tbl, int32_t target, int32_t source, rational_t *c) {
  dl_var_hobj_t hobj;

  hobj.m.hash = (hobj_hash_t) hash_dl_var;
  hobj.m.eq = (hobj_eq_t) eq_dl_var;
  hobj.m.build = (hobj_build_t) build_dl_var;

  hobj.table = tbl;

  hobj.triple.target = target;
  hobj.triple.source = source;
  q_init(&hobj.triple.q);
  q_set(&hobj.triple.q, c);

  return int_htbl_get_obj(&tbl->htbl, (int_hobj_t*) &hobj);
}


/*
 * Remove all variables of index >= n
 */
static void dl_vartable_remove_vars(dl_vartable_t *tbl, uint32_t n) {
  uint32_t i, h;

  assert(n <= tbl->nvars);

  for (i=n; i<tbl->nvars; i++) {
    h = hash_dl_triple(tbl->triple + i);
    int_htbl_erase_record(&tbl->htbl, h, i);
  }

  tbl->nvars = n;
}


/*
 * TRAIL STACK
 */

/*
 * Initialize stack with default size
 */
static void init_dl_trail_stack(dl_trail_stack_t *stack) {
  uint32_t n;

  n = DEF_DL_TRAIL_SIZE;
  assert(n < MAX_DL_TRAIL_SIZE);

  stack->size = n;
  stack->top = 0;
  stack->data = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
}

/*
 * Make the stack 50% larger
 */
static void extend_dl_trail_stack(dl_trail_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n>>1;
  if (n >= MAX_DL_TRAIL_SIZE) {
    out_of_memory();
  }
  stack->data = (uint32_t *) safe_realloc(stack->data, n * sizeof(uint32_t));
  stack->size = n;
}

/*
 * Push n on top of the stack
 */
static void dl_trail_stack_push(dl_trail_stack_t *stack, uint32_t n) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_dl_trail_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i] = n;
  stack->top = i+1;
}

/*
 * Delete the stack
 */
static void delete_dl_trail_stack(dl_trail_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}

/*
 * Empty the stack
 */
static inline void reset_dl_trail_stack(dl_trail_stack_t *stack) {
  stack->top = 0;
}

/*
 * Check emptiness
 */
static inline bool dl_trail_stack_is_empty(dl_trail_stack_t *stack) {
  return stack->top == 0;
}

/*
 * Get the top element from the stack
 */
static inline uint32_t dl_trail_stack_top(dl_trail_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data[stack->top - 1];
}

/*
 * Remove the top element
 */
static inline void dl_trail_stack_pop(dl_trail_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}



/*
 * Replacement RDL interface when the solver is for IDL
 */




/*
 * FRONT END
 */

/*
 * Initialize dl:
 * - core = attached core
 * - gates = gate manager
 */
void init_dl_front_end(dl_front_end_t *dl, smt_core_t *core, gate_manager_t *gates) {
  dl->core = core;
  dl->gate_manager = gates;

  init_dl_vartable(&dl->vtbl, DEF_DL_VARTABLE_SIZE);
  init_dl_trail_stack(&dl->trail_stack);

  dl->solver = NULL;
  dl->is_idl = false;
  // rdl and idl interface descriptors not initialized

  dl->aux.target = nil_vertex;
  dl->aux.source = nil_vertex;
  q_init(&dl->aux.q);
  q_init(&dl->q0);

  dl->env = NULL;
}


/*
 * Attach an IDL solver
 */
void dl_front_end_attach_idl_solver(dl_front_end_t *dl, void *solver, idl_interface_t *idl) {
  assert(dl->solver == NULL);
  dl->solver = solver;
  dl->is_idl = true;
  dl->idl = *idl;
}

/*
 * Attach an RDL solver
 */
void dl_front_end_attach_rdl_solver(dl_front_end_t *dl, void *solver, rdl_interface_t *rdl) {
  assert(dl->solver == NULL);
  dl->solver = solver;
  dl->is_idl = false;
  dl->rdl = *rdl;
}

/*
 * Attach buffer for exceptions
 */
void dl_front_end_init_jmpbuf(dl_front_end_t *dl, jmp_buf *buffer) {
  dl->env = buffer;
}

/*
 * Delete the whole solver
 */
void delete_dl_front_end(dl_front_end_t *dl) {
  delete_dl_vartable(&dl->vtbl);
  delete_dl_trail_stack(&dl->trail_stack);
  q_clear(&dl->aux.q);
  q_clear(&dl->q0);
}


/*
 * Push
 */
void dl_front_end_push(dl_front_end_t *dl) {
  uint32_t n;

  n = dl->vtbl.nvars;
  dl_trail_stack_push(&dl->trail_stack, n);
  // TODO: propagate to dl->solver  
}

/*
 * Pop
 */
void dl_front_end_pop(dl_front_end_t *dl) {
  uint32_t n;

  assert(! dl_trail_stack_is_empty(&dl->trail_stack));
  n = dl_trail_stack_top(&dl->trail_stack);
  dl_vartable_remove_vars(&dl->vtbl, n);
  dl_trail_stack_pop(&dl->trail_stack);
  // TODO: propagate to dl->solver
}

/*
 * Reset
 */
void dl_front_end_reset(dl_front_end_t *dl) {
  reset_dl_vartable(&dl->vtbl);
  reset_dl_trail_stack(&dl->trail_stack);

  dl->aux.target = nil_vertex;
  dl->aux.source = nil_vertex;
  q_clear(&dl->aux.q);
  q_clear(&dl->q0);
  // TODO: propagate to dl->solver
}



/*
 * RAISE EXCEPTION OR ABORT
 */
static __attribute__ ((noreturn)) void dl_exception(dl_front_end_t *dl, int code) {
  if (dl->env != NULL) {
    longjmp(*dl->env, code);
  }
  abort();
}


/*
 * INTERNALIZATION FUNCTIONS
 */

/*
 * New variable
 */
thvar_t dl_create_var(dl_front_end_t *dl, bool is_int) {
  int32_t v;

  if (dl->is_idl) {
    if (! is_int) {
      dl_exception(dl, FORMULA_NOT_IDL);
    }
    v = dl->idl.make_vertex(dl->solver);

  } else {
    if (is_int) {
      dl_exception(dl, FORMULA_NOT_RDL);
    }
    v = dl->rdl.make_vertex(dl->solver);
  }

  if (v < 0) {
    dl_exception(dl, TOO_MANY_ARITH_VARS);
  }

  q_clear(&dl->q0);
  return get_dl_var(&dl->vtbl, v, nil_vertex, &dl->q0);
}

/*
 * Constant q
 */
thvar_t dl_create_const(dl_front_end_t *dl, rational_t *q) {
  if (dl->is_idl && ! q_is_integer(q)) {
    dl_exception(dl, FORMULA_NOT_IDL);
  }
  return get_dl_var(&dl->vtbl, nil_vertex, nil_vertex, q);
}

/*
 * Product: always fail
 */
thvar_t dl_create_pprod(dl_front_end_t *dl, pprod_t *p, thvar_t *map) {
  int code;

  code = dl->is_idl ? FORMULA_NOT_IDL: FORMULA_NOT_RDL;
  dl_exception(dl, code);
}
