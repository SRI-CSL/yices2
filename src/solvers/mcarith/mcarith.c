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
 * MCARITH SOLVER
 *
 * Uses MCSAT to implement a non-linear arithmetic solver.
 */

#include "context/context.h"
#include "solvers/mcarith/mcarith.h"
#include "solvers/simplex/simplex.h"

#include "mcsat/trail.h"
#include "mcsat/variable_db.h"

#include "model/models.h"
#include "model/model_queries.h"

#include "yices.h"

void simplex_attach_eterm(simplex_solver_t *solver, thvar_t v, eterm_t t);
thvar_t simplex_create_const(simplex_solver_t *solver, rational_t *q);
eterm_t simplex_eterm_of_var(simplex_solver_t *solver, thvar_t v);
void simplex_start_internalization(simplex_solver_t *solver);
void simplex_assert_clause_vareq_axiom(simplex_solver_t *solver, uint32_t n, literal_t *c, thvar_t x, thvar_t y);
void simplex_assert_cond_vareq_axiom(simplex_solver_t *solver, literal_t c, thvar_t x, thvar_t y);

/**
 * Allocate a polynomial from an existing polynomial, but mapping variables.
 */
static
polynomial_t* alloc_polynomial_from_map(polynomial_t* p, thvar_t* map, int32_t var_count) {
  uint32_t n = p->nterms;
  polynomial_t* pv = alloc_raw_polynomial(n);
  if (n == 0) return pv;

  q_set(&pv->mono[0].coeff, &p->mono[0].coeff);
  if (p->mono[0].var == const_idx) {
    pv->mono[0].var = 0;
  } else {
    assert(0 <= map[0] && map[0] < var_count);
    pv->mono[0].var = map[0];
  }
  for (uint32_t i = 1; i < n; ++i) {
    q_set(&pv->mono[i].coeff, &p->mono[i].coeff);
    assert(0 <= map[i] && map[i] < var_count);
    pv->mono[i].var = map[i];
  }
  return pv;
}

// Indicates if the variable is free or a poly.
enum mcarith_var_type { VAR_FREE, VAR_CONST, VAR_POLY };

struct mcarith_var_s {
  enum mcarith_var_type type;
  union {
    rational_t *rat;
    pprod_t* prod;
  } def;
};

typedef struct mcarith_var_s mcarith_var_t;

enum mcarith_assertion_type { VAR_EQ, VAR_EQ0, VAR_GE0, POLY_EQ0, POLY_GE0, ATOM_ASSERT };

/**
 * Assertion for mcarith.
 *
 * type and def value determine the assertion.
 * tt indicates if the assertion is true or false.
 * lit indicates the literal associated with the assetion (or null_literal if none).
 *
 *
 * VAR_EQ: An equality between two theory variables.
 *   def.eq contains the left-hand and right hand side theory variables.
 * VAR_EQ0: A theory variable is equal to 0.
 *   def.var contains the variable
 * VAR_GE0: A theory variable is greater than or equal to 0.
 *   def.var contains the variable
 * POLY_EQ0: A polynomial is equal to 0.
 *   def.poly contains the polynomial over theory variables.
 * POLY_GE0: A polynomial is greater than or equal to 0.
 *   def.poly contains the polynomial over theory variables.
 * ATOM_ASSERT: An atom is asserted to be true.
 */
typedef struct mcarith_assertion_s {
  // Indicates the type of the assertion.
  enum mcarith_assertion_type type;
  // A polynomial over theory variables.
  union {
    thvar_t var;
    polynomial_t* poly;
    struct { thvar_t lhs; thvar_t rhs; } eq;
    int32_t atom;
  } def;
  // tt is true if the poly should be non-negative and false if negative.
  bool tt;
  // Literal associated with assertion (or null_literal if none).
  literal_t lit;
} mcarith_assertion_t;

void free_mcarith_assertion(const mcarith_assertion_t* a) {
  switch (a->type) {
  case POLY_EQ0:
  case POLY_GE0:
    free_polynomial(a->def.poly);
    break;
  default:
    break;
  }
}

/*
 * On entry to each decision level k we store:
 * - the number of asserted bounds (i.e., arith_stack.top)
 * - the number of asserted atoms (i.e., arith_queue.top)
 *
 * At level 0: n_bounds = 0, n_assertions = 0
 */
typedef struct mcarith_undo_record_s {
  uint32_t n_assertions;
} mcarith_undo_record_t;

typedef struct mcarith_undo_stack_s {
  uint32_t size;
  uint32_t top;
  mcarith_undo_record_t *data;
} mcarith_undo_stack_t;

/*
 * Initialize: n = initial size
 */
static void init_mcarith_undo_stack(mcarith_undo_stack_t *stack, uint32_t n) {
  assert(0 < n);

  stack->size = n;
  stack->top = 0;
  stack->data = safe_malloc(n * sizeof(mcarith_undo_record_t));
}

/*
 * Double the undo stack size
 */
static void extend_mcarith_undo_stack(mcarith_undo_stack_t* stack) {
    stack->size = 2 * stack->size;
    // Check for overflow.
    if (stack->size == 0)
      out_of_memory();
    stack->data = safe_realloc(stack->data, stack->size * sizeof(mcarith_undo_record_t));
}

/*
 * Push an undo record to the stack.
 */
static void mcarith_undo_push_record(mcarith_undo_stack_t* stack, uint32_t n_a) {
  uint32_t i = stack->top;
  assert (stack->size > 0);
  // Double stack size if needed
  if (i == stack->size) {
    extend_mcarith_undo_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i].n_assertions = n_a;
  stack->top = i+1;
}

/*
 * Pop an undo record to the stack.
 */
static mcarith_undo_record_t* mcarith_undo_pop_record(mcarith_undo_stack_t* stack) {
  assert(stack->top > 0);
  return stack->data + --stack->top;
}

/*
 * Reset to given undo level (which should be greater than current one.
 */
static
mcarith_undo_record_t* mcarith_undo_backtrack(mcarith_undo_stack_t* stack, uint32_t back_level) {
  assert(stack->top > back_level);
  stack->top = back_level;
  return stack->data + back_level;
}

// Reset undo stack.
static
void mcarith_undo_reset(mcarith_undo_stack_t* stack) {
  stack->top = 0;
}

// Variables kinds specific to mcsat
typedef enum {
  MCVAR_SIMPLEX = 0,  // Defined in simplex variable table
  MCVAR_PPROD = 1, // A power product
  MCVAR_RDIV = 2 // A real division
} mcsatvar_kind_t;

typedef struct {
  mcsatvar_kind_t kind;
  union {
    pprod_t* pprod;
    struct {
      thvar_t num;
      thvar_t den;
    } rdiv;
  } def;
} mcsatvar_def_t;

// Note.
//  This conditional causes MCSAT to create new tables for types products and terms.
// Disabling it causes mcsat to share those tables with yices.
#define MCSAT_STANDALONE_TERMS

struct mcarith_solver_s {
  // Simple solver
  simplex_solver_t simplex;
  // Context for mcsat solver
  context_t mcsat_ctx;
  // MCSat solver
  mcsat_solver_t* mcsat;
  // Model returned by mcsat
  model_t* model;

#ifdef MCSAT_STANDALONE_TERMS
  // Type table for mcsat
  type_table_t types;
  // Power product table for mcsat
  pprod_table_t pprods;
  // Term Table for mcsat
  term_table_t terms;
#else
  // Type table for mcsat
  type_table_t* types;
  // Power product table for mcsat
  pprod_table_t* pprods;
  // Term Table for mcsat
  term_table_t* terms;
#endif
  // Size of var_terms array
  uint32_t var_terms_size;
  // Map theory variables to term so we can send them to MCSat
  term_t* var_terms;

  // Size of atom term array
  uint32_t atom_terms_size;
  // Map atom indices to term (or NULL_TERM if unassigned).
  term_t* atom_terms;

  // Assertion array
  mcarith_assertion_t* assertions;
  // Number of entries in the array
  uint32_t assertion_capacity;
  // Number of assertions so far.
  uint32_t assertion_count;

  mcarith_undo_stack_t undo_stack;
};

void mcarith_enable_row_saving(mcarith_solver_t *solver) {
  simplex_enable_row_saving(&solver->simplex);
}

#ifdef MCSAT_STANDALONE_TERMS
static
pprod_table_t* mcarith_solver_pprods(mcarith_solver_t* s) {
  return &s->pprods;
}

static
type_table_t* mcarith_solver_types(mcarith_solver_t* s) {
  return &s->types;
}

static
term_table_t* mcarith_solver_terms(mcarith_solver_t* s) {
  return &s->terms;
}
#else
static
pprod_table_t* mcarith_solver_pprods(mcarith_solver_t* s) {
  return s->pprods;
}

static
type_table_t* mcarith_solver_types(mcarith_solver_t* s) {
  return s->types;
}

static
term_table_t* mcarith_solver_terms(mcarith_solver_t* s) {
  return s->terms;
}
#endif

/*
 * Initialize a mcarith solver
 */
void init_mcarith_solver(mcarith_solver_t **solver, context_t* ctx) {
  const uint32_t init_assertion_capacity = 64;

  mcarith_solver_t* s = safe_malloc(sizeof(mcarith_solver_t));
  init_simplex_solver(&s->simplex, ctx->core, &ctx->gate_manager, ctx->egraph);

  s->mcsat = 0;
  s->model = 0;

#ifdef MCSAT_STANDALONE_TERMS
  // Initialize mcsat type table
  init_type_table(&s->types, 64);
  // Initialize mcsat power product table.
  init_pprod_table(&s->pprods, 0); // Use default size
  // Initialize term table
  const uint32_t init_termtable_size = 1024;
  init_term_table(&s->terms, init_termtable_size, &s->types, &s->pprods);
#else
  s->types = ctx->types;
  s->pprods = ctx->terms->pprods;
  s->terms = ctx->terms;
  assert(ctx->types == ctx->terms->types);
#endif

  // Create array for mapping theory variables to initial term.
  assert(s->simplex.vtbl.nvars == 1);
  s->var_terms = safe_malloc(sizeof(term_t));
  s->var_terms_size = 1;
  rational_t one;
  q_set_one(&one);
  s->var_terms[0] = arith_constant(mcarith_solver_terms(s), &one);


  s->atom_terms = 0;
  s->atom_terms_size = 0;

  // Initialize assertion table
  s->assertions = safe_malloc(init_assertion_capacity * sizeof(mcarith_assertion_t));
  s->assertion_capacity = init_assertion_capacity;
  s->assertion_count = 0;

  // Create undo stack
  const uint32_t init_undo_stack_size = 32;
  init_mcarith_undo_stack(&s->undo_stack, init_undo_stack_size);

  *solver = s;
}

static
void mcarith_free_mcsat(mcarith_solver_t* s) {
  if (s->mcsat) {
    mcsat_destruct(s->mcsat);
    safe_free(s->mcsat);
    delete_context(&s->mcsat_ctx);
    s->mcsat = 0;
  }
}

void destroy_mcarith_solver(mcarith_solver_t* s) {
  mcarith_free_mcsat(s);
  // Free assertions
  for (uint32_t i = 0; i != s->assertion_count; ++i) {
    free_mcarith_assertion(s->assertions + i);
  }
  safe_free(s->assertions);
  // Free MCSat terms
  safe_free(s->var_terms);
  safe_free(s->atom_terms);

#ifdef MCSAT_STANDALONE_TERMS
  delete_term_table(&s->terms);
  delete_pprod_table(&s->pprods);
  delete_type_table(&s->types);
#endif
  // Free solver
  delete_simplex_solver(&s->simplex);
  // Free solver itself
  safe_free(s);
}

/*
 * This resizes a size_ptr and term array so that it can accomodate the new_size entries.
 */
static inline
void realloc_term_array(uint32_t* size_ptr, term_t** term_array, uint32_t new_size) {
  if (new_size > *size_ptr) {
    *term_array = safe_realloc(*term_array, sizeof(term_t) * new_size);
    for (int i = *size_ptr; i < new_size; ++i) {
      (*term_array)[i] = NULL_TERM;
    }
    *size_ptr = new_size;
  }
}

/*
 * This resizes var_terms to make sure it is large enough
 * to reference all vtbl entries.
 */
static inline
void mcarith_check_var_size(mcarith_solver_t *solver) {
  uint32_t new_size = solver->simplex.vtbl.size;
  realloc_term_array(&solver->var_terms_size, &solver->var_terms, new_size);
}

/*
 * This resizes the atom_terms to make sure it is large enough
 * to reference all atbl entries.
 */
static inline
void mcarith_check_atom_size(mcarith_solver_t *solver) {
  uint32_t new_size = solver->simplex.atbl.size;
  realloc_term_array(&solver->atom_terms_size, &solver->atom_terms, new_size);
}

static
void rba_buffer_add_mono_mcarithvar(mcarith_solver_t* solver, rba_buffer_t* b, rational_t *a, thvar_t v);

static
term_t get_term(mcarith_solver_t* solver, thvar_t v) {
  arith_vartable_t* table;
  term_table_t* terms;


  table = &solver->simplex.vtbl;
  assert(0 <= v && v < table->nvars);

  terms = mcarith_solver_terms(solver);

  term_t t = solver->var_terms[v];
  if (t != NULL_TERM) return t;


  uint8_t tag = table->tag[v];
  bool is_int = (tag & AVARTAG_INT_MASK) != 0;
  switch (tag & AVARTAG_KIND_MASK) {
  // Uninterpreted
  case AVARTAG_KIND_FREE:
    {
      type_t tp = is_int ? int_type(mcarith_solver_types(solver)) : real_type(mcarith_solver_types(solver));
      t = new_uninterpreted_term(terms, tp);
    }
    break;
  case AVARTAG_KIND_POLY:
    {
      rba_buffer_t b;
      polynomial_t* p = table->def[v];
      init_rba_buffer(&b, mcarith_solver_pprods(solver));
      uint32_t n = p->nterms;
      for (uint32_t j = 0; j < n; ++j) {
        rational_t* r = &p->mono[j].coeff;
        if (j == 0 && p->mono[j].var == const_idx) {
          rba_buffer_add_const(&b, r);
        } else {
          thvar_t v = p->mono[j].var;
          rba_buffer_add_mono_mcarithvar(solver, &b, r, v);
        }
      }
      t = arith_poly(terms, &b);
    }
    break;
  case AVARTAG_KIND_PPROD:
    //pprod_t* p = table->def[v];
    longjmp(*solver->simplex.env, INTERNAL_ERROR);
    break;
  case AVARTAG_KIND_CONST:
    t = arith_constant(terms, table->def[v]);
    break;
  default:
    longjmp(*solver->simplex.env, INTERNAL_ERROR);
  }
  solver->var_terms[v] = t;
  return t;
}

/* This adds the theory var value to the buffer while ensuring a nested polynomial term is not created. */
static
void rba_buffer_add_mono_mcarithvar(mcarith_solver_t* solver, rba_buffer_t* b, rational_t *a, thvar_t v) {
  arith_vartable_t* table;
  term_table_t* terms;
  polynomial_t* p;
  rational_t* c;
  rational_t aux;
  term_t t;

  q_init(&aux);

  table = &solver->simplex.vtbl;
  terms = mcarith_solver_terms(solver);

  assert(0 <= v && v < table->nvars);

  uint8_t tag = table->tag[v];
  switch (tag & AVARTAG_KIND_MASK) {
  case AVARTAG_KIND_POLY: {
    p = table->def[v];
    uint32_t n = p->nterms;
    for (uint32_t j = 0; j < n; ++j) {
      c = &p->mono[j].coeff;
      q_set(&aux, a);
      q_mul(&aux, c);
      if (j == 0 && p->mono[j].var == const_idx) {
        rba_buffer_add_const(b, &aux);
      } else {
        t = get_term(solver, p->mono[j].var);
        assert(term_kind(terms, t) != ARITH_POLY);
        rba_buffer_add_mono(b, &aux, var_pp(t));
      }
    }
    break;
  }
  case AVARTAG_KIND_PPROD:
    //pprod_t* p = table->def[v];
    longjmp(*solver->simplex.env, INTERNAL_ERROR);
    break;
  case AVARTAG_KIND_CONST:
    q_set(&aux, a);
    q_mul(&aux, table->def[v]);
    rba_buffer_add_const(b, &aux);
    break;
  default:
    t = get_term(solver, v);
    assert(term_kind(terms, t) != ARITH_POLY);
    rba_buffer_add_mono(b, a, var_pp(t));
  }
  q_clear(&aux);
}

/* This adds the theory var value to the buffer while ensuring a nested polynomial term is not created. */
static
void rba_buffer_add_mcarithvar(mcarith_solver_t* solver, rba_buffer_t* b, thvar_t v) {
  arith_vartable_t* table;
  term_table_t* terms;
  polynomial_t* p;
  rational_t* c;
  term_t t;
  thvar_t mv;

  table = &solver->simplex.vtbl;
  terms = mcarith_solver_terms(solver);

  assert(0 <= v && v < table->nvars);

  uint8_t tag = table->tag[v];
  switch (tag & AVARTAG_KIND_MASK) {
  case AVARTAG_KIND_POLY: {
    p = table->def[v];
    uint32_t n = p->nterms;
    for (uint32_t j = 0; j < n; ++j) {
      c = &p->mono[j].coeff;
      mv = p->mono[j].var;
      if (j == 0 && mv == const_idx) {
        rba_buffer_add_const(b, c);
      } else {
        rba_buffer_add_mono_mcarithvar(solver, b, c, mv);
      }
    }
    break;
  }
  case AVARTAG_KIND_PPROD:
    //pprod_t* p = table->def[v];
    longjmp(*solver->simplex.env, INTERNAL_ERROR);
    break;
  case AVARTAG_KIND_CONST:
    rba_buffer_add_const(b, table->def[v]);
    break;
  default:
    t = get_term(solver, v);
    assert(term_kind(terms, t) != ARITH_POLY);
    rba_buffer_add_pp(b, var_pp(t));
  }
}

/* This subtracts the theory var value from the buffer while ensuring a nested polynomial term is not created. */
static
void rba_buffer_sub_mcarithvar(mcarith_solver_t* solver, rba_buffer_t* b, thvar_t v) {
  arith_vartable_t* table;
  term_table_t* terms;
  uint32_t j;
  uint32_t n;
  polynomial_t* p;
  rational_t* c;
  term_t t;
  thvar_t mv;
  rational_t aux;

  table = &solver->simplex.vtbl;
  terms = mcarith_solver_terms(solver);

  assert(0 <= v && v < table->nvars);

  uint8_t tag = table->tag[v];
  switch (tag & AVARTAG_KIND_MASK) {
  case AVARTAG_KIND_POLY: {
    p = table->def[v];
    n = p->nterms;
    for (j = 0; j < n; ++j) {
      c = &p->mono[j].coeff;
      mv = p->mono[j].var;
      if (j == 0 && mv == const_idx) {
        rba_buffer_sub_const(b, c);
      } else {
        q_init(&aux);
        q_set(&aux, c);
        q_neg(&aux);
        rba_buffer_add_mono_mcarithvar(solver, b, &aux, mv);
        q_clear(&aux);
      }
    }
    break;
  }
  case AVARTAG_KIND_PPROD:
    //pprod_t* p = table->def[v];
    longjmp(*solver->simplex.env, INTERNAL_ERROR);
    break;
  case AVARTAG_KIND_CONST:
    rba_buffer_sub_const(b, table->def[v]);
    break;
  default:
    t = get_term(solver, v);
    assert(term_kind(terms, t) != ARITH_POLY);
    rba_buffer_sub_pp(b, var_pp(t));
  }
}

/*
 * Return the term associated with the given atom index.
 */
static
term_t get_atom(mcarith_solver_t* solver, int32_t atom_index) {
  arith_atomtable_t *atbl;
  term_t result;
  term_table_t* terms;
  arith_atom_t* ap;
  term_t v;
  rational_t* bnd;
  rba_buffer_t b;
  term_t polyTerm;


  mcarith_check_atom_size(solver);

  atbl = &solver->simplex.atbl;
  assert(0 <= atom_index && atom_index < atbl->natoms);

  result = solver->atom_terms[atom_index];
  if (result != NULL_TERM) return result;

  terms = mcarith_solver_terms(solver);

  ap = atbl->atoms + atom_index;
  //  Get variable in ap
  v = var_of_atom(ap);
  // Get bound
  bnd = bound_of_atom(ap);

  switch (tag_of_atom(ap)) {
  // Assert v-b >= 0
  case GE_ATM: {
    if (q_is_zero(bnd)) {
      polyTerm = get_term(solver, var_of_atom(ap));
    } else {
      // Create buffer b = v - bnd
      init_rba_buffer(&b, mcarith_solver_pprods(solver));
      rba_buffer_add_mcarithvar(solver, &b, v);
      rba_buffer_sub_const(&b, bnd);
      // Create term and free buffer.
      polyTerm = arith_poly(terms, &b);
      delete_rba_buffer(&b);
    }
    result = arith_geq_atom(terms, polyTerm);
    break;
  }
  // Assert v <= b by asserting b-v >= 0
  case LE_ATM: {
    // Create buffer b = bnd - v
    init_rba_buffer(&b, mcarith_solver_pprods(solver));
    rba_buffer_sub_mcarithvar(solver, &b, v);
    rba_buffer_add_const(&b, bnd);
    polyTerm = arith_poly(terms, &b);
    delete_rba_buffer(&b);
    result = arith_geq_atom(terms, polyTerm);
    break;
  }
  // Assert v == bnd
  case EQ_ATM: {
    result = arith_bineq_atom(terms, get_term(solver, v), arith_constant(terms, bnd));
    break;
  }
  default:
    longjmp(*solver->simplex.env, INTERNAL_ERROR);
  }
  solver->atom_terms[atom_index] = result;
  return result;
}

/*
 * Create a power of products.
 */
static
thvar_t mcarith_create_pprod(void *s, pprod_t *p, thvar_t *map) {
  mcarith_solver_t *solver = s;
  assert(pprod_degree(p) > 1);
  assert(!pp_is_empty(p));
  assert(!pp_is_var(p));

  // Create theory variable
  thvar_t v = simplex_create_var(&solver->simplex, false);
  // Remap variables in powerproduct
  mcarith_check_var_size(solver);
  pp_buffer_t b;
  init_pp_buffer(&b, p->len);
  for (uint32_t i = 0; i < p->len; ++i) {
    thvar_t mv = map[i];
    assert(mv < v);
    term_t t = get_term(solver, mv);
    pp_buffer_set_varexp(&b, t, p->prod[i].exp);
  }
  pp_buffer_normalize(&b);

  // Create term
  assert(solver->var_terms_size > v);
  solver->var_terms[v] = pprod_term_from_buffer(mcarith_solver_terms(solver), &b);
  // Free buffer and return
  delete_pp_buffer(&b);
  return v;
}

/*
 * Create a divison
 */
static
thvar_t mcarith_create_rdiv(void *s, thvar_t num, thvar_t den) {
  mcarith_solver_t *solver;
  thvar_t v;
  term_t nt;
  term_t dt;

  solver = s;
  // Create theory variable
  v = simplex_create_var(&solver->simplex, false);

  // Assign term
  mcarith_check_var_size(solver);
  nt = get_term(solver, num);
  dt = get_term(solver, den);
  solver->var_terms[v] = arith_rdiv(mcarith_solver_terms(solver), nt, dt);

  return v;
}

/**
 * Allocate an assertion for storing on array.
 */
static
mcarith_assertion_t* alloc_top_assertion(mcarith_solver_t* s) {
  size_t cnt = s->assertion_count;
  if (cnt >= s->assertion_capacity) {
    assert(cnt == s->assertion_capacity);
    s->assertion_capacity = 2 * s->assertion_capacity;
    if (s->assertion_capacity == 0)
      out_of_memory();
    s->assertions = safe_realloc(s->assertions, s->assertion_capacity * sizeof(mcarith_assertion_t));
  }
  s->assertion_count = cnt + 1;
  return s->assertions + cnt;
}

/********************************
 *  SMT AND CONTROL INTERFACES  *
 *******************************/

/*
 * This is called before any new atom/variable is created
 * (before start_search).
 * - we reset the tableau and restore the matrix if needed
 */
void mcarith_start_internalization(mcarith_solver_t *solver) {
  simplex_start_internalization(&solver->simplex);
}

/*
 * Start search:
 * - simplify the matrix
 * - initialize the tableau
 * - compute the initial assignment
 */
static void mcarith_start_search(mcarith_solver_t *solver) {
  simplex_start_search(&solver->simplex);
}

/*
 * Process all assertions
 * - this function may be called before start_search
 * - if it's called before start_search, the tableau is not ready
 * return true if no conflict is found.
 */
bool mcarith_propagate(mcarith_solver_t *solver) {
  return simplex_propagate(&solver->simplex);
}

/*
 * Initializes an rba buffer from a polynomial while translating polynomial variables
 * using the var_terms array.
 *
 * @param pprods Power product table for rba buffer.
 * @param b Buffer to initialize
 * @param p Polynomial to initialize
 * @param var_terms Variable term array used to map from polynomial variables to terms.
 * @param var_count Size of var_terms array
 */
static
void init_rba_buffer_from_poly(mcarith_solver_t* solver,
                               rba_buffer_t* b,
                               polynomial_t* p) {
  init_rba_buffer(b, mcarith_solver_pprods(solver));
  uint32_t n = p->nterms;
  for (uint32_t j = 0; j < n; ++j) {
    if (j == 0 && p->mono[j].var == const_idx) {
      rba_buffer_add_const(b, &p->mono[j].coeff);
    } else {
      rational_t* c = &p->mono[j].coeff;
      thvar_t v = p->mono[j].var;
      rba_buffer_add_mono_mcarithvar(solver, b, c, v);
    }
  }
}

/*
 * Check for integer feasibility
 */
static
fcheck_code_t mcarith_final_check(void* s) {
  mcarith_solver_t *solver;
  term_table_t* terms;
  uint32_t acnt;


  solver = s;
  terms = mcarith_solver_terms(solver);

  yices_pp_t printer;
  pp_area_t area;

  area.width = 72;
  area.height = 8;
  area.offset = 2;
  area.stretch = false;
  area.truncate = true;

  init_default_yices_pp(&printer, stdout, &area);

  mcarith_free_mcsat(solver);

  const bool qflag = false; // Quantifiers not allowed
  init_context(&solver->mcsat_ctx, terms, QF_NRA, CTX_MODE_ONECHECK, CTX_ARCH_MCSAT, qflag);
  solver->mcsat = mcsat_new(&solver->mcsat_ctx);

  acnt = solver->assertion_count;
  term_t* assertions = safe_malloc(sizeof(term_t) * (acnt + 1));
  literal_t* literals = safe_malloc(sizeof(literal_t) * acnt);
  size_t literal_count = 0;
  mcarith_check_var_size(solver);
  for (size_t i = 0; i < acnt; ++i) {
    mcarith_assertion_t* a = solver->assertions + i;

    rba_buffer_t b;
    term_t p;
    switch (a->type) {
    case VAR_EQ: {
      term_t lhs;
      term_t rhs;
      lhs = get_term(solver, a->def.eq.lhs);
      rhs = get_term(solver, a->def.eq.rhs);
      p = arith_bineq_atom(terms, lhs, rhs);
      break;
    }
    case VAR_EQ0:
      p = arith_eq_atom(terms, get_term(solver, a->def.var));
      break;
    case VAR_GE0:
      p = arith_geq_atom(terms, get_term(solver, a->def.var));
      break;
    case POLY_EQ0:
      init_rba_buffer_from_poly(solver, &b, a->def.poly);
      p = arith_eq_atom(terms, arith_poly(terms, &b));
      delete_rba_buffer(&b);
      break;
    case POLY_GE0:
      init_rba_buffer_from_poly(solver, &b, a->def.poly);
      p = arith_geq_atom(terms, arith_poly(terms, &b));
      delete_rba_buffer(&b);
      break;
    case ATOM_ASSERT:
      p = get_atom(solver, a->def.atom);
      break;
    default:
      longjmp(*solver->simplex.env, INTERNAL_ERROR);
    }
    if (a->lit != null_literal) {
      smt_core_t* c = solver->simplex.core;
      assert(literal_value(c, a->lit) == VAL_TRUE);
      literals[literal_count++] = not(a->lit);
    }
    assertions[i] = a->tt ? p : not_term(terms, p);
  }
  literals[literal_count] = end_clause;

  int32_t r = mcsat_assert_formulas(solver->mcsat, acnt, assertions);
  fcheck_code_t result;
  if (r == TRIVIALLY_UNSAT) {
    record_theory_conflict(solver->simplex.core, literals);
      mcarith_free_mcsat(solver);
    result = FCHECK_CONTINUE;
  } else if (r == CTX_NO_ERROR) {
    result = FCHECK_SAT;
    mcsat_solve(solver->mcsat, 0, 0, 0, 0);
    switch (mcsat_status(solver->mcsat)) {
    case STATUS_UNKNOWN:
      mcarith_free_mcsat(solver);
      safe_free(literals);
      result = FCHECK_UNKNOWN;
      break;
    case STATUS_SAT:
      safe_free(literals);
      result = FCHECK_SAT;
      break;
    case STATUS_UNSAT:
      mcarith_free_mcsat(solver);
      // - record a conflict (by calling record_theory_conflict)
      // - create lemmas or atoms in the core
      record_theory_conflict(solver->simplex.core, literals);
      result = FCHECK_CONTINUE;
      break;
    case STATUS_IDLE:
    case STATUS_SEARCHING:
    case STATUS_INTERRUPTED:
    case STATUS_ERROR:
    default:
      mcarith_free_mcsat(solver);
      safe_free(literals);
      longjmp(*solver->simplex.env, INTERNAL_ERROR);
      break;
    }
  } else {
    mcarith_free_mcsat(solver);
    safe_free(literals);
    longjmp(*solver->simplex.env, INTERNAL_ERROR);
  }

  return result;
}

/*
 * Free assertions added since undo record was created.
 */
static
void mcarith_backtrack_assertions(mcarith_solver_t* solver, uint32_t assertion_count) {
  assert(assertion_count <= solver->assertion_count);
  for (uint32_t i = assertion_count; i != solver->assertion_count; ++i) {
    free_mcarith_assertion(solver->assertions + i);
  }
  solver->assertion_count = assertion_count;
}

/*
 * Increase dlevel in simplex and eqprop
 */
void mcarith_increase_decision_level(mcarith_solver_t *solver) {
  simplex_increase_decision_level(&solver->simplex);
  mcarith_undo_push_record(&solver->undo_stack, solver->assertion_count);
}

/*
 * Full backtrack
 */
void mcarith_backtrack(mcarith_solver_t *solver, uint32_t back_level) {
  mcarith_undo_record_t* r = mcarith_undo_backtrack(&solver->undo_stack, back_level);
  mcarith_backtrack_assertions(solver, r->n_assertions);
  simplex_backtrack(&solver->simplex, back_level);
}

/*
 * Start a new base level
 */
static void mcarith_push(mcarith_solver_t *solver) {
  simplex_push(&solver->simplex);
  mcarith_undo_push_record(&solver->undo_stack, solver->assertion_count);
}

/*
 * Return to the previous base level
 */
void mcarith_pop(mcarith_solver_t *solver) {
  uint32_t vc;
  uint32_t vc0;
  term_t* t;
  term_t* end;
  mcarith_undo_record_t* r;
  // Reset assertions
  r =  mcarith_undo_pop_record(&solver->undo_stack);
  mcarith_backtrack_assertions(solver, r->n_assertions);
  // Pop simplex state
  vc = solver->simplex.vtbl.nvars;
  simplex_pop(&solver->simplex);
  vc0 = solver->simplex.vtbl.nvars;

  end = solver->var_terms + vc;
  for (t = solver->var_terms + vc0; t != end; ++t) {
    *t = NULL_TERM;
  }
}

/*
 * Reset to the empty solver
 */
void mcarith_reset(mcarith_solver_t *solver) {
  simplex_reset(&solver->simplex);

  mcarith_undo_reset(&solver->undo_stack);
  mcarith_backtrack_assertions(solver, 0);
}

/*
 * Clear: nothing to clear.
 */
void mcarith_clear(mcarith_solver_t *solver) {
}

static th_ctrl_interface_t mcarith_control = {
  .start_internalization = (start_intern_fun_t) mcarith_start_internalization,
  .start_search = (start_fun_t) mcarith_start_search,
  .propagate = (propagate_fun_t) mcarith_propagate,
  .final_check = mcarith_final_check,
  .increase_decision_level = (increase_level_fun_t) mcarith_increase_decision_level,
  .backtrack = (backtrack_fun_t) mcarith_backtrack,
  .push = (push_fun_t) mcarith_push,
  .pop = (pop_fun_t) mcarith_pop,
  .reset = (reset_fun_t) mcarith_reset,
  .clear = (clear_fun_t) mcarith_clear,
};


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
bool mcarith_assert_atom(mcarith_solver_t *solver, void *atom_pointer, literal_t l) {
  bool r = simplex_assert_atom(&solver->simplex, atom_pointer, l);
  if (!r) return false;

  simplex_solver_t* simplex = &solver->simplex;
  arith_atomtable_t *atbl = &simplex->atbl;

  // Get atom index from pointer
  int32_t atom_index = arithatom_tagged_ptr2idx(atom_pointer);
  assert(0 <= atom_index && atom_index < atbl->natoms);

  arith_atom_t* ap = atbl->atoms + atom_index;
  assert(boolvar_of_atom(ap) == var_of(l));

  mcarith_assertion_t* assert = alloc_top_assertion(solver);
  assert->type = ATOM_ASSERT;
  assert->def.atom = atom_index;
  assert->tt = is_pos(l);
  assert->lit = l;
  return true;
}

/*
 * Expand a propagation object into a conjunction of literals
 * - expl is a pointer to a propagation object in solver->arena
 */
void mcarith_expand_explanation(mcarith_solver_t *solver, literal_t l, void *expl, ivector_t *v) {
  simplex_expand_explanation(&solver->simplex, l, expl, v);
}

/*
 * Return l or (not l)
 * - a = atom attached to l = mcarith atom index packed in a void* pointer
 */
literal_t mcarith_select_polarity(mcarith_solver_t *solver, void *a, literal_t l) {
  return simplex_select_polarity(&solver->simplex, a, l);
}

static th_smt_interface_t mcarith_smt = {
  .assert_atom = (assert_fun_t) mcarith_assert_atom,
  .expand_explanation = (expand_expl_fun_t) mcarith_expand_explanation,
  .select_polarity = (select_pol_fun_t) mcarith_select_polarity,
  .delete_atom = NULL,
  .end_atom_deletion = NULL,
};

static const uint32_t theory_var_verb = 5;

static
thvar_t mcarith_create_const(void* s, rational_t *q) {
  mcarith_solver_t *solver;

  solver = s;
  return simplex_create_const(&solver->simplex, q);
}

/*
 * Create a theory variable equal to p
 * - arith_map maps variables of p to corresponding theory variables
 *   in the solver
 */
static
thvar_t mcarith_create_poly(void* s, polynomial_t *p, thvar_t *map) {
  mcarith_solver_t *solver;

  solver = s;
  return simplex_create_poly(&solver->simplex, p, map);
}

/*
 * Assert a top-level equality constraint (either x == 0 or x != 0)
 * - tt indicates whether the constraint or its negation must be asserted
 *   tt == true  --> assert x == 0
 *   tt == false --> assert x != 0
 */
static void mcarith_assert_eq_axiom(void* s, thvar_t x, bool tt) {
  mcarith_solver_t *solver;
  mcarith_assertion_t* assert;

  solver = s;
  simplex_assert_eq_axiom(&solver->simplex, x, tt);

  // Record assertion for sending to mcarith solver.
  assert = alloc_top_assertion(solver);
  assert->type = VAR_EQ0;
  assert->def.var = x;
  assert->tt = tt;
  assert->lit = null_literal;
}

/*
 * Assert a top-level inequality (either x >= 0 or x < 0)
 * - tt indicates whether the constraint or its negation must be asserted
 *   tt == true  --> assert x >= 0
 *   tt == false --> assert x < 0
 */
static void mcarith_assert_ge_axiom(void* s, thvar_t x, bool tt){
  mcarith_solver_t *solver;
  mcarith_assertion_t* assert;

  solver = s;
  simplex_assert_ge_axiom(&solver->simplex, x, tt);

  assert = alloc_top_assertion(solver);
  assert->type = VAR_GE0;
  assert->def.var = x;
  assert->tt = tt;
  assert->lit = null_literal;
}

/*
 * Assert top-level equality or disequality (either p == 0 or p != 0)
 * - map: convert p's variables to mcarith variables
 * - if tt is true  ---> assert p == 0
 * - if tt is false ---> assert p != 0
 */
static void mcarith_assert_poly_eq_axiom(void * s, polynomial_t *p, thvar_t *map, bool tt) {
  mcarith_solver_t *solver;
  mcarith_assertion_t* assert;

  solver = s;
  assert(p->nterms > 0);

  simplex_assert_poly_eq_axiom(&solver->simplex, p, map, tt);

  assert = alloc_top_assertion(solver);
  assert->type = POLY_EQ0;
  assert->def.poly = alloc_polynomial_from_map(p, map, solver->simplex.vtbl.nvars);
  assert->tt = tt;
  assert->lit = null_literal;
}

/*
 * Assert a top-level inequality that p >= 0 is true or false.
 * - map: an array that maps the `i`th variable in `p` to the mcarith theory variable.
 * - tt indicates if `p >= 0` is asserted be true or false.
 */
static void mcarith_assert_poly_ge_axiom(void *s, polynomial_t *p, thvar_t *map, bool tt) {
  mcarith_solver_t *solver;
  mcarith_assertion_t* assert;

  solver = s;
  assert(p->nterms > 0);

  simplex_assert_poly_ge_axiom(&solver->simplex, p, map, tt);

  assert = alloc_top_assertion(solver);
  assert->type = POLY_GE0;
  assert->def.poly = alloc_polynomial_from_map(p, map, solver->simplex.vtbl.nvars);
  assert->tt = tt;
  assert->lit = null_literal;
}

/*
 * If tt == true --> assert (x - y == 0)
 * If tt == false --> assert (x - y != 0)
 */
static
void mcarith_assert_vareq_axiom(void* s, thvar_t x, thvar_t y, bool tt) {
  mcarith_solver_t *solver;
  mcarith_assertion_t* assert;

  solver = s;
  simplex_assert_vareq_axiom(&solver->simplex, x, y, tt);

  assert = alloc_top_assertion(solver);
  assert->type = VAR_EQ;
  assert->def.eq.lhs = x;
  assert->def.eq.rhs = y;
  assert->tt = tt;
  assert->lit = null_literal;
}

/*
 * Assert (c ==> x == y)
 */
static
void mcarith_assert_cond_vareq_axiom(void* s, literal_t c, thvar_t x, thvar_t y) {
  mcarith_solver_t *solver;
  solver = s;
  simplex_assert_cond_vareq_axiom(&solver->simplex, c, x, y);
}

/*
 * Assert (c[0] \/ ... \/ c[n-1] \/ x == y)
 */
static
void mcarith_assert_clause_vareq_axiom(void* s, uint32_t n, literal_t *c, thvar_t x, thvar_t y) {
  mcarith_solver_t *solver = s;
  simplex_assert_clause_vareq_axiom(&solver->simplex, n, c, x, y);
}

/*
 * Get the type of variable x
 */
static
bool mcarith_var_is_integer(void* s, thvar_t x) {
  mcarith_solver_t *solver = s;
  return arith_var_is_int(&solver->simplex.vtbl, x);
}

#pragma region Models

/*
 * Model construction
 */
static void mcarith_build_model(void* s) {
  mcarith_solver_t* solver = s;

  model_t *model;
  assert(solver->mcsat);
  assert(!solver->model);
  // Create model
  model = safe_malloc(sizeof(model_t));
  init_model(model, mcarith_solver_terms(solver), true);
  mcsat_build_model(solver->mcsat, model);
  solver->model = model;

  mcarith_free_mcsat(solver);
}

/*
 * Free the model
 */
static void mcarith_free_model(void* s) {
  mcarith_solver_t* solver;

  solver = s;
  assert(solver->model);
  delete_model(solver->model);
  free(solver->model);
  solver->model = 0;
}

/*
 * This tries to return the value associated with the variable x in the model.
 * If x has a value, then this returns true and sets v.  If not, then it returns
 * false.
 */
static
bool mcarith_value_in_model(void* s, thvar_t x, arithval_in_model_t* res) {
  mcarith_solver_t* solver;
  term_t t;
  model_t* mdl;
  value_t v;
  value_table_t* vtbl;

  assert(res->tag == ARITHVAL_RATIONAL);

  solver = s;
  t = solver->var_terms[x];
  if (t == NULL_TERM)
    return false;

  mdl = solver->model;
  assert(mdl);

  v  = model_get_term_value(mdl, t);
  if (v < 0) {
    return false;
  }

  vtbl = model_get_vtbl(mdl);
  if (object_is_rational(vtbl, v)) {
    q_set(&res->val.q, vtbl_rational(vtbl, v));
    return true;
  } else if (object_is_algebraic(vtbl, v)) {
    lp_algebraic_number_t* n = vtbl_algebraic_number(vtbl, v);
    q_clear(&res->val.q);
    res->tag = ARITHVAL_ALGEBRAIC;
    lp_algebraic_number_construct_copy(&res->val.alg_number, n);
    return true;
  }

  // Should not happen.
  return false;
}

#pragma endregion Models

/******************************
 *  INTERFACE TO THE CONTEXT  *
 *****************************/

static arith_interface_t mcarith_context = {
  .create_var = (create_arith_var_fun_t) simplex_create_var,
  .create_const = mcarith_create_const,
  .create_poly = mcarith_create_poly,
  .create_pprod = mcarith_create_pprod,
  .create_rdiv = mcarith_create_rdiv,

  .create_eq_atom = (create_arith_atom_fun_t) simplex_create_eq_atom,
  .create_ge_atom = (create_arith_atom_fun_t) simplex_create_ge_atom,
  .create_poly_eq_atom = (create_arith_patom_fun_t) simplex_create_poly_eq_atom,
  .create_poly_ge_atom = (create_arith_patom_fun_t) simplex_create_poly_ge_atom,
  .create_vareq_atom = (create_arith_vareq_atom_fun_t) simplex_create_vareq_atom,

  .assert_eq_axiom = mcarith_assert_eq_axiom,
  .assert_ge_axiom = mcarith_assert_ge_axiom,
  .assert_poly_eq_axiom = mcarith_assert_poly_eq_axiom,
  .assert_poly_ge_axiom = mcarith_assert_poly_ge_axiom,
  .assert_vareq_axiom = mcarith_assert_vareq_axiom,
  .assert_cond_vareq_axiom = mcarith_assert_cond_vareq_axiom,
  .assert_clause_vareq_axiom = mcarith_assert_clause_vareq_axiom,

  .attach_eterm = (attach_eterm_fun_t) simplex_attach_eterm,
  .eterm_of_var = (eterm_of_var_fun_t) simplex_eterm_of_var,

  .build_model    = mcarith_build_model,
  .free_model     = mcarith_free_model,
  .value_in_model = mcarith_value_in_model,

  .arith_var_is_int = mcarith_var_is_integer,
};

/*
 * Return the interface descriptor
 */
arith_interface_t *mcarith_arith_interface(mcarith_solver_t *solver) {
  return &mcarith_context;
}

/*
 * Get the control and smt interfaces
 */
th_ctrl_interface_t *mcarith_ctrl_interface(mcarith_solver_t *solver) {
  return &mcarith_control;
}

th_smt_interface_t *mcarith_smt_interface(mcarith_solver_t *solver) {
  return &mcarith_smt;
}