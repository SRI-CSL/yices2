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

extern void simplex_attach_eterm(simplex_solver_t *solver, thvar_t v, eterm_t t);
extern thvar_t simplex_create_const(simplex_solver_t *solver, rational_t *q);
extern eterm_t simplex_eterm_of_var(simplex_solver_t *solver, thvar_t v);
extern void simplex_start_internalization(simplex_solver_t *solver);

/**
 * Initialize b from a power product with variables translated by map. 
 */
static
void init_pp_buffer_from_pprod_map(pp_buffer_t* b, pprod_t* p, int32_t* map, size_t map_size) {
  init_pp_buffer(b, p->len);
  for (uint32_t i = 0; i < p->len; ++i) {
    varexp_t* v = p->prod + i;
    assert(v->var < map_size);
    pp_buffer_set_varexp(b, map[v->var], v->exp);
  }
  pp_buffer_normalize(b);
}

/**
 * Initialize b from a power product with variables translated by map. 
 */
static
void init_pp_buffer_from_index_pprod_map(pp_buffer_t* b, pprod_t* p, int32_t* map, size_t map_size) {
  init_pp_buffer(b, p->len);
  for (uint32_t i = 0; i < p->len; ++i) {
    varexp_t* v = p->prod + i;
    assert(v->var < map_size);
    pp_buffer_set_varexp(b, map[v->var], v->exp);
  }
  pp_buffer_normalize(b);
}

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
static void mcarith_push_undo_record(mcarith_undo_stack_t* stack, uint32_t n_a) {
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
 * Push an undo record to the stack.
 */
static mcarith_undo_record_t* mcarith_pop_undo_record(mcarith_undo_stack_t* stack) {
  assert(stack->top > 0);
  return stack->data + --stack->top;
}

// Note.
//  This conditional causes MCSAT to create new tables for types products and terms.
// Disabling it causes mcsat to share those tables with yices.
#define MCSAT_STANDALONE_TERMS

struct mcarith_solver_s {
  // Simple solver
  simplex_solver_t simplex;

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
  // Map theory variables to term.
  term_t* var_terms;
  
  // Size of atom term array
  uint32_t atom_terms_size;
  // Map atom indices to term (or NULL_TERM if unassigned).
  term_t* atom_terms;

  // Information about theory variables.
  //mcarith_var_t* vars;

  // Assertion array
  mcarith_assertion_t* assertions;
  // Number of entries in the array
  uint32_t assertion_capacity;
  // Number of assertions so far.
  uint32_t assertion_count;

  mcarith_undo_stack_t undo_stack;
};

#ifdef MCSAT_STANDALONE_TERMS
static 
pprod_table_t* mcarith_solver_pprods(const mcarith_solver_t* s) {
  return &s->pprods;
}

static
type_table_t* mcarith_solver_types(const mcarith_solver_t* s) {
  return &s->types;
}

static
term_table_t* mcarith_solver_terms(const mcarith_solver_t* s) {
  return &s->terms;
}
#else
static 
pprod_table_t* mcarith_solver_pprods(const mcarith_solver_t* s) {
  return s->pprods;
}

static
type_table_t* mcarith_solver_types(const mcarith_solver_t* s) {
  return s->types;
}

static
term_table_t* mcarith_solver_terms(const mcarith_solver_t* s) {
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

void destroy_mcarith_solver(mcarith_solver_t* s) {
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
 * This resizes var_Terms to make sure it is large enough
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
term_t get_term(mcarith_solver_t* solver, thvar_t v) {
  arith_vartable_t* table = &solver->simplex.vtbl;
  assert(0 <= v && v < table->nvars);
  
  term_t t = solver->var_terms[v];  
  if (t != NULL_TERM) return t;

  uint8_t tag = table->tag[v];
  bool is_int = (tag & AVARTAG_INT_MASK) != 0;
  switch (tag & AVARTAG_KIND_MASK) {
  // Uninterpreted
  case AVARTAG_KIND_FREE:
    {
      type_t tp = is_int ? int_type(mcarith_solver_types(solver)) : real_type(mcarith_solver_types(solver));
      t = new_uninterpreted_term(mcarith_solver_terms(solver), tp);
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
          term_t t = get_term(solver, p->mono[j].var);
          rba_buffer_add_mono(&b, r, var_pp(t));
        }
      }
      t = arith_poly(mcarith_solver_terms(solver), &b);
    }
    break;
  case AVARTAG_KIND_PPROD:
    //pprod_t* p = table->def[v];
    longjmp(*solver->simplex.env, INTERNAL_ERROR);
    break;
  case AVARTAG_KIND_CONST:
    t = arith_constant(mcarith_solver_terms(solver), table->def[v]);
    break;
  default:
    longjmp(*solver->simplex.env, INTERNAL_ERROR);
  }
  solver->var_terms[v] = t;
  return t;
}

/* This addsthe theory var value to the buffer while ensuring a nested polynomial term is not created. */
static
void rba_buffer_add_mcarithvar(mcarith_solver_t* solver, rba_buffer_t* b, thvar_t v) {
  arith_vartable_t* table = &solver->simplex.vtbl;
  assert(0 <= v && v < table->nvars);
  
  uint8_t tag = table->tag[v];
  switch (tag & AVARTAG_KIND_MASK) {
  case AVARTAG_KIND_POLY: {
    polynomial_t* p = table->def[v];
    uint32_t n = p->nterms;
    for (uint32_t j = 0; j < n; ++j) {
      rational_t* r = &p->mono[j].coeff;
      if (j == 0 && p->mono[j].var == const_idx) {
        rba_buffer_add_const(b, r);
      } else {
        term_t t = get_term(solver, p->mono[j].var);
        rba_buffer_add_mono(b, r, var_pp(t));
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
    rba_buffer_add_pp(b, var_pp(get_term(solver, v)));
  }
}

/* This subtracts the theory var value from the buffer while ensuring a nested polynomial term is not created. */
static
void rba_buffer_sub_mcarithvar(mcarith_solver_t* solver, rba_buffer_t* b, thvar_t v) {
  arith_vartable_t* table = &solver->simplex.vtbl;
  assert(0 <= v && v < table->nvars);
  
  uint8_t tag = table->tag[v];
  switch (tag & AVARTAG_KIND_MASK) {
  case AVARTAG_KIND_POLY: {
    polynomial_t* p = table->def[v];
    uint32_t n = p->nterms;
    for (uint32_t j = 0; j < n; ++j) {
      rational_t* r = &p->mono[j].coeff;
      if (j == 0 && p->mono[j].var == const_idx) {
        rba_buffer_sub_const(b, r);
      } else {
        term_t t = get_term(solver, p->mono[j].var);
        rba_buffer_sub_mono(b, r, var_pp(t));
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
    rba_buffer_sub_pp(b, var_pp(get_term(solver, v)));
  }
}

/* 
 * Return the term associated with the given atom index.
 */
static
term_t get_atom(mcarith_solver_t* solver, int32_t atom_index) {
  mcarith_check_atom_size(solver);

  arith_atomtable_t *atbl = &solver->simplex.atbl;
  assert(0 <= atom_index && atom_index < atbl->natoms);

  term_t p = solver->atom_terms[atom_index];
  if (p != NULL_TERM) return p;

  arith_atom_t* ap = atbl->atoms + atom_index;
  rational_t* bnd = bound_of_atom(ap);
  term_table_t* terms = mcarith_solver_terms(solver);

  switch (tag_of_atom(ap)) {
  // Assert v-b >= 0
  case GE_ATM: {
    term_t polyTerm;
    if (q_is_zero(bnd)) {
      polyTerm = get_term(solver, var_of_atom(ap));
    } else {
      rba_buffer_t b;
      init_rba_buffer(&b, mcarith_solver_pprods(solver));
      rba_buffer_add_mcarithvar(solver, &b, var_of_atom(ap));
      rba_buffer_sub_const(&b, bnd);
      polyTerm = arith_poly(terms, &b);
      delete_rba_buffer(&b);
    }
    p = arith_geq_atom(terms, polyTerm);
    break;
  }
  // Assert v <= b by asserting b-v >= 0
  case LE_ATM: {
    rba_buffer_t b;
    init_rba_buffer(&b, mcarith_solver_pprods(solver));
    rba_buffer_sub_mcarithvar(solver, &b, var_of_atom(ap));
    rba_buffer_add_const(&b, bnd);
    term_t polyTerm = arith_poly(terms, &b);
    delete_rba_buffer(&b);
    p = arith_geq_atom(terms, polyTerm);
    break;
  }
  // Assert v == bnd
  case EQ_ATM: {
    term_t t = get_term(solver, var_of_atom(ap));
    p = arith_bineq_atom(terms, t, arith_constant(terms, bnd));
    break;
  }
  default:
    longjmp(*solver->simplex.env, INTERNAL_ERROR);
  }
  solver->atom_terms[atom_index] = p;
  return p;
}

/*
 * Create a new variable that represents constant q
 * - add a matrix column if that's a new variable
 */
thvar_t mcarith_create_const(mcarith_solver_t *solver, rational_t *q) {
  thvar_t v = simplex_create_const(&solver->simplex, q);
  uint8_t tag = solver->simplex.vtbl.tag[v];
  assert((tag & AVARTAG_KIND_MASK) == AVARTAG_KIND_CONST);
  return v;
}

/*
 * Create a power of products.
 */
static
thvar_t mcarith_create_pprod(mcarith_solver_t *solver, pprod_t *p, thvar_t *map) {
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
  solver->var_terms[v] = pprod_term_from_buffer(mcarith_solver_terms(solver), &b);

  // Free buffer and return
  delete_pp_buffer(&b);
  return v;
}

/**
 * Allocate an assertion for storing on array.
 */
static
mcarith_assertion_t* alloc_top_assertion(mcarith_solver_t* s) {
  size_t cnt = s->assertion_count;
  if (cnt < s->assertion_capacity) {
    ++s->assertion_count;
    return s->assertions + cnt;
  } else {
    assert(cnt == s->assertion_capacity);
    s->assertion_capacity = 2 * s->assertion_capacity;
    if (s->assertion_capacity == 0)
      out_of_memory();
    s->assertions = safe_realloc(s->assertions, s->assertion_capacity * sizeof(mcarith_assertion_t));
    return s->assertions + cnt;
  }
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
      pprod_t* pp = var_pp(get_term(solver, p->mono[j].var));
      rba_buffer_add_mono(b, &p->mono[j].coeff, pp);
    }
  }
}

/*
 * Check for integer feasibility
 */
static
fcheck_code_t mcarith_final_check(mcarith_solver_t *solver) {

  context_t ctx;
  const bool qflag = false; // Quantifiers not allowed
  term_table_t* terms = mcarith_solver_terms(solver);
  init_context(&ctx, terms, QF_NRA, CTX_MODE_ONECHECK, CTX_ARCH_MCSAT, qflag);

  mcsat_solver_t* mcsat = mcsat_new(&ctx);

  term_t* assertions = safe_malloc(sizeof(term_t) * solver->assertion_count);
  literal_t* literals = safe_malloc(sizeof(literal_t) * solver->assertion_count + 1);
  size_t literal_count = 0;
  mcarith_check_var_size(solver);
  for (size_t i = 0; i < solver->assertion_count; ++i) {
    mcarith_assertion_t* a = solver->assertions + i;

    rba_buffer_t b;
    term_t p;
    switch (a->type) {
    case VAR_EQ:
      p = arith_bineq_atom(terms, get_term(solver, a->def.eq.lhs), get_term(solver, a->def.eq.rhs));
      break;
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

  int32_t r = mcsat_assert_formulas(mcsat, solver->assertion_count, assertions);  
  fcheck_code_t result; 
  if (r == TRIVIALLY_UNSAT) {
    record_theory_conflict(solver->simplex.core, literals);
    result = FCHECK_CONTINUE;
  } else if (r == CTX_NO_ERROR) {
    result = FCHECK_SAT;
    mcsat_solve(mcsat, 0, 0, 0, 0);
    switch (mcsat_status(mcsat)) {
    case STATUS_UNKNOWN:
      safe_free(literals);
      result = FCHECK_UNKNOWN;
      break;
    case STATUS_SAT:
      safe_free(literals);
      result = FCHECK_SAT;
      break;
    case STATUS_UNSAT:
      // TODO:
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
      safe_free(literals);
      longjmp(*solver->simplex.env, INTERNAL_ERROR);
      break;
    }
  } else {
    safe_free(literals);
    longjmp(*solver->simplex.env, INTERNAL_ERROR);
  }

  mcsat_destruct(mcsat);
  safe_free(mcsat);
  delete_context(&ctx);
  return result;
}

/*
 * Increase dlevel in simplex and eqprop
 */
void mcarith_increase_decision_level(mcarith_solver_t *solver) {
  simplex_increase_decision_level(&solver->simplex);
  assert(0); //FIXME  
}


/*
 * Full backtrack
 */
void mcarith_backtrack(mcarith_solver_t *solver, uint32_t back_level) {
#if TRACE
  printf("---> Mcarith: backtracking to level %"PRIu32"\n", back_level);
#endif
  assert(0); //FIXME  
}

/*
 * Start a new base level
 */
void mcarith_push(mcarith_solver_t *solver) {
  simplex_push(&solver->simplex);
  mcarith_push_undo_record(&solver->undo_stack, solver->assertion_count);
}

/*
 * Return to the previous base level
 */
void mcarith_pop(mcarith_solver_t *solver) {
  // Reset assertions
  mcarith_undo_record_t* r = mcarith_pop_undo_record(&solver->undo_stack);
  for (uint32_t i = r->n_assertions; i != solver->assertion_count; ++i) {
    free_mcarith_assertion(solver->assertions + i);
  }
  solver->assertion_count = r->n_assertions;
  // Pop simplex state
  simplex_pop(&solver->simplex);
}

/*
 * Reset to the empty solver
 */
void mcarith_reset(mcarith_solver_t *solver) {
  assert(0); //FIXME  
  //mcsat_reset(solver->mcsat);
}

/*
 * Clear: nothing to clear.
 */
void mcarith_clear(mcarith_solver_t *solver) {
  assert(0); //FIXME  
  //mcsat_clear(solver->mcsat);
}

static th_ctrl_interface_t mcarith_control = {
  .start_internalization = (start_intern_fun_t) mcarith_start_internalization,
  .start_search = (start_fun_t) mcarith_start_search,
  .propagate = (propagate_fun_t) mcarith_propagate,
  .final_check = (final_check_fun_t) mcarith_final_check,
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
  assert(0); // This function should not be called.
}

/*
 * Return l or (not l)
 * - a = atom attached to l = mcarith atom index packed in a void* pointer
 */
literal_t mcarith_select_polarity(mcarith_solver_t *solver, void *a, literal_t l) {
  assert(0); //FIXME  
  return l; // Do nothing
}

static th_smt_interface_t mcarith_smt = {
  .assert_atom = (assert_fun_t) mcarith_assert_atom,
  .expand_explanation = (expand_expl_fun_t) mcarith_expand_explanation,
  .select_polarity = (select_pol_fun_t) mcarith_select_polarity,
  .delete_atom = NULL,
  .end_atom_deletion = NULL,
};

/*
 * Create a theory variable equal to p
 * - arith_map maps variables of p to corresponding theory variables
 *   in the solver
 */
thvar_t mcarith_create_poly(mcarith_solver_t *solver, polynomial_t *p, thvar_t *map) {
  assert(0); //FIXME  
  return 0; // FIXME
}

/*
 * Create the atom x == 0
 * - this attach the atom to the smt_core
 */
literal_t mcarith_create_eq_atom(mcarith_solver_t *solver, thvar_t x) {
  assert(0); //FIXME  
  return 0; // FIXME
}

/*
 * Create the atom x >= 0
 * - this attach the atom to the smt_core
 */
literal_t mcarith_create_ge_atom(mcarith_solver_t *solver, thvar_t x) {
  assert(0); //FIXME  
  return 0; // FIXME
}

/*
 * Create the atom p == 0
 * - apply the renaming defined by map
 */
literal_t mcarith_create_poly_eq_atom(mcarith_solver_t *solver, polynomial_t *p, thvar_t *map) {
  assert(0); //FIXME  
  return 0; // FIXME
}

/*
 * Create the atom p >= 0 and return the corresponding literal
 * - replace the variables of p as defined by map
 */
literal_t mcarith_create_poly_ge_atom(mcarith_solver_t *solver, polynomial_t *p, thvar_t *map) {
  assert(0); //FIXME  
  return 0; // FIXME
}

/*
 * Assert a top-level equality constraint (either x == 0 or x != 0)
 * - tt indicates whether the constraint or its negation must be asserted
 *   tt == true  --> assert x == 0
 *   tt == false --> assert x != 0
 */
void mcarith_assert_eq_axiom(mcarith_solver_t *solver, thvar_t x, bool tt) {
  simplex_assert_eq_axiom(&solver->simplex, x, tt);

  // Record assertion for sending to mcarith solver.
  mcarith_assertion_t* assert = alloc_top_assertion(solver);
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
void mcarith_assert_ge_axiom(mcarith_solver_t *solver, thvar_t x, bool tt){
  simplex_assert_ge_axiom(&solver->simplex, x, tt);

  mcarith_assertion_t* assert = alloc_top_assertion(solver);
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
void mcarith_assert_poly_eq_axiom(mcarith_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt) {
  assert(p->nterms > 0);

  simplex_assert_poly_eq_axiom(&solver->simplex, p, map, tt);

  mcarith_assertion_t* assert = alloc_top_assertion(solver);
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
void mcarith_assert_poly_ge_axiom(mcarith_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt) {
  assert(p->nterms > 0);

  simplex_assert_poly_ge_axiom(&solver->simplex, p, map, tt);

  mcarith_assertion_t* assert = alloc_top_assertion(solver);
  assert->type = POLY_GE0;
  assert->def.poly = alloc_polynomial_from_map(p, map, solver->simplex.vtbl.nvars);
  assert->tt = tt;
  assert->lit = null_literal;
}

/*
 * If tt == true --> assert (x - y == 0)
 * If tt == false --> assert (x - y != 0)
 */
void mcarith_assert_vareq_axiom(mcarith_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  simplex_assert_vareq_axiom(&solver->simplex, x, y, tt);

  mcarith_assertion_t* assert = alloc_top_assertion(solver);

  assert->type = VAR_EQ;
  assert->def.eq.lhs = x;
  assert->def.eq.rhs = y;
  assert->tt = tt;
  assert->lit = null_literal;
}

/*
 * Assert (c ==> x == y)
 */
void mcarith_assert_cond_vareq_axiom(mcarith_solver_t *solver, literal_t c, thvar_t x, thvar_t y) {
  assert(0); //FIXME  
  //FIXME
}

/*
 * Assert (c[0] \/ ... \/ c[n-1] \/ x == y)
 */
void mcarith_assert_clause_vareq_axiom(mcarith_solver_t *solver, uint32_t n, literal_t *c, thvar_t x, thvar_t y) {
  assert(0); //FIXME  
  //FIXME
}

/*
 * Get the type of variable x
 */
bool mcarith_var_is_integer(mcarith_solver_t *solver, thvar_t x) {
  return arith_var_is_int(&solver->simplex.vtbl, x);
}



/*
 * Attach egraph term t to a variable v
 * - v must not have an eterm attached already
 */
static void mcarith_attach_eterm(mcarith_solver_t *solver, thvar_t v, eterm_t t) {
  simplex_attach_eterm(&solver->simplex, v, t);
}

/*
 * Get the egraph term t attached to v
 * - return null_eterm if v has no eterm attached
 */
static eterm_t mcarith_eterm_of_var(mcarith_solver_t *solver, thvar_t v) {
  return simplex_eterm_of_var(&solver->simplex, v);
}

#pragma region Models

/*
 * Model construction
 */
void mcarith_build_model(mcarith_solver_t *solver) {
  // FIXME
  assert(0);
  printf("mcarith_build_model\n");
}

/*
 * Free the model
 */
void mcarith_free_model(mcarith_solver_t *solver) {
  //FIXME
  printf("mcarith_free_model\n");
}

/*
 * This tries to return the value associated with the variable x in the model.
 * If x has a value, then this returns true and sets v.  If not, then it returns
 * false.
 */
bool mcarith_value_in_model(mcarith_solver_t *solver, thvar_t x, rational_t *v) {
  printf("mcarith_value_in_model\n");
  return false; // FIXME
}

#pragma endregion Models

/******************************
 *  INTERFACE TO THE CONTEXT  *
 *****************************/

static arith_interface_t mcarith_context = {
  .create_var = (create_arith_var_fun_t) simplex_create_var,
  .create_const = (create_arith_const_fun_t) simplex_create_const,
  .create_poly = (create_arith_poly_fun_t) mcarith_create_poly,
  .create_pprod = (create_arith_pprod_fun_t) mcarith_create_pprod,

  .create_eq_atom = (create_arith_atom_fun_t) mcarith_create_eq_atom,
  .create_ge_atom = (create_arith_atom_fun_t) mcarith_create_ge_atom,
  .create_poly_eq_atom = (create_arith_patom_fun_t) mcarith_create_poly_eq_atom,
  .create_poly_ge_atom = (create_arith_patom_fun_t) mcarith_create_poly_ge_atom,
  .create_vareq_atom = (create_arith_vareq_atom_fun_t) simplex_create_vareq_atom,

  .assert_eq_axiom = (assert_arith_axiom_fun_t) mcarith_assert_eq_axiom,
  .assert_ge_axiom = (assert_arith_axiom_fun_t) mcarith_assert_ge_axiom,
  .assert_poly_eq_axiom = (assert_arith_paxiom_fun_t) mcarith_assert_poly_eq_axiom,
  .assert_poly_ge_axiom = (assert_arith_paxiom_fun_t) mcarith_assert_poly_ge_axiom,
  .assert_vareq_axiom = (assert_arith_vareq_axiom_fun_t) mcarith_assert_vareq_axiom,
  .assert_cond_vareq_axiom = (assert_arith_cond_vareq_axiom_fun_t) mcarith_assert_cond_vareq_axiom,
  .assert_clause_vareq_axiom = (assert_arith_clause_vareq_axiom_fun_t) mcarith_assert_clause_vareq_axiom,

  .attach_eterm = (attach_eterm_fun_t) mcarith_attach_eterm,
  .eterm_of_var = (eterm_of_var_fun_t) mcarith_eterm_of_var,

  .build_model = (build_model_fun_t) mcarith_build_model,
  .free_model = (free_model_fun_t) mcarith_free_model,
  .value_in_model = (arith_val_in_model_fun_t) mcarith_value_in_model,

  .arith_var_is_int = (arith_var_is_int_fun_t) mcarith_var_is_integer,
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

/*
static th_egraph_interface_t simplex_egraph = {
  (assert_eq_fun_t) simplex_assert_var_eq,
  (assert_diseq_fun_t) simplex_assert_var_diseq,
  (assert_distinct_fun_t) simplex_assert_var_distinct,
  (check_diseq_fun_t) simplex_check_disequality,
  (is_constant_fun_t) simplex_var_is_constant,
  (expand_eq_exp_fun_t) simplex_expand_th_explanation,
  (reconcile_model_fun_t) simplex_reconcile_model,
  (prepare_model_fun_t) simplex_prep_model,
  (equal_in_model_fun_t) simplex_var_equal_in_model,
  (gen_inter_lemma_fun_t) simplex_gen_interface_lemma,
  (release_model_fun_t) simplex_release_model,
  (build_partition_fun_t) simplex_build_model_partition,
  (free_partition_fun_t) simplex_release_model_partition,
  (attach_to_var_fun_t) simplex_attach_eterm,
  (get_eterm_fun_t) simplex_eterm_of_var,
  (select_eq_polarity_fun_t) simplex_select_eq_polarity,
};


static arith_egraph_interface_t simplex_arith_egraph = {
  (make_arith_var_fun_t) simplex_create_var,
  (arith_val_fun_t) simplex_value_in_model,
};


th_egraph_interface_t *simplex_egraph_interface(simplex_solver_t *solver) {
  return &simplex_egraph;
}

arith_egraph_interface_t *simplex_arith_egraph_interface(simplex_solver_t *solver) {
  return &simplex_arith_egraph;
}
*/