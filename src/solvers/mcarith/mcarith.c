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
enum mcarith_var_type { VAR_FREE, VAR_POLY };

struct mcarith_var_s {
  enum mcarith_var_type type;
  union {
    pprod_t* prod;
  } def;
};

typedef struct mcarith_var_s mcarith_var_t;


enum mcarith_assertion_type { VAR_EQ, POLY_EQ, POLY_GE };

struct mcarith_assertion_s {
  // Indicates the type of the assertion.
  enum mcarith_assertion_type type;
  // A polynomial over theory variables.
  union {
    polynomial_t* poly;
    struct { thvar_t lhs; thvar_t rhs } eq;
  } def;
  // tt is true if the poly should be non-negative and false if negative.
  bool tt;
  // Literal associated with assertion (or null_literal if none).
  literal_t lit;
};

typedef struct mcarith_assertion_s mcarith_assertion_t;

struct mcarith_solver_s {
  simplex_solver_t simplex;
  //  const context_t* ctx;

  // Variable definitions

  // Information about theory variables.
  mcarith_var_t* vars;

  // Assertion array
  mcarith_assertion_t* assertions;
  size_t assertion_capacity;
  size_t assertion_count;
};

/*
 * Initialize a mcarith solver
 */
void init_mcarith_solver(mcarith_solver_t **solver, context_t* ctx) {
  const size_t init_assertion_capacity = 64;

  mcarith_solver_t* s = safe_malloc(sizeof(mcarith_solver_t));
  init_simplex_solver(&s->simplex, ctx->core, &ctx->gate_manager, ctx->egraph);
  s->assertions = safe_malloc(init_assertion_capacity * sizeof(mcarith_assertion_t));
  s->assertion_capacity = init_assertion_capacity;
  s->assertion_count = 0;
  s->vars = safe_malloc(sizeof(mcarith_var_t) * s->simplex.vtbl.size);
  *solver = s;
}

void destroy_mcarith_solver(mcarith_solver_t* s) {
  // Free vars
  uint32_t vc = s->simplex.vtbl.nvars;
  for (uint32_t i = 0; i != vc; ++i) {
    switch (s->vars[i].type) {
    case VAR_POLY:
      free_pprod(s->vars[i].def.prod);
      break;
    default:
      break;
    }
  }
  safe_free(s->vars);
  // Free assertions
  safe_free(s->assertions);
  // Free solver
  delete_simplex_solver(&s->simplex);
  // Free solver itself
  safe_free(s);  
}

/*
 * Create a new theory variable
 * - is_int indicates whether the variable should be an integer.
 */
static
thvar_t mcarith_create_var_internal(mcarith_solver_t *solver, bool is_int) {
  uint32_t init_size = solver->simplex.vtbl.size;

  thvar_t v = simplex_create_var(&solver->simplex, is_int);

  uint32_t new_size = solver->simplex.vtbl.size;
  if (new_size > init_size) {
    solver->vars = safe_realloc(solver->vars, sizeof(mcarith_var_t) * new_size);
  }
  assert(v < new_size);
  return v;
}

/*
 * Create a new theory variable
 * - is_int indicates whether the variable should be an integer
 * - also add a matrix column
 */
static
thvar_t mcarith_create_var(mcarith_solver_t *solver, bool is_int) {
  thvar_t v = mcarith_create_var_internal(solver, is_int);
  solver->vars[v].type = VAR_FREE;
  return v;
}

/**
 * Allocate an assertion for storing on array.
 */
static
mcarith_assertion_t* alloc_assertion(mcarith_solver_t* s) {
  size_t cnt = s->assertion_count;
  if (cnt < s->assertion_capacity) {
    ++s->assertion_count;
    return s->assertions + cnt;
  } else {
    assert(cnt == s->assertion_capacity);
    assert(s->assertion_capacity > 0);
    s->assertion_capacity = 2 * s->assertion_capacity;
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
//  simplex_reset_tableau(solver);
//  simplex_restore_matrix(solver);
//  assert(solver->matrix_ready && ! solver->tableau_ready);
}

/*
 * Start search:
 * - simplify the matrix
 * - initialize the tableau
 * - compute the initial assignment
 */
void mcarith_start_search(mcarith_solver_t *solver) {
//  assert(0); //FIXME  

}

/*
 * Process all assertions
 * - this function may be called before start_search
 * - if it's called before start_search, the tableau is not ready
 * return true if no conflict is found.
 */
bool mcarith_propagate(mcarith_solver_t *solver) {
  return true;
}

static 
void init_rba_buffer_from_poly(rba_buffer_t* b, pprod_table_t* pprods,
                               polynomial_t* p,
                               term_t* var_terms, int32_t var_count) {
  init_rba_buffer(b, pprods);
  uint32_t n = p->nterms;
  for (uint32_t j = 0; j < n; ++j) {
    if (j == 0 && p->mono[j].var == const_idx) {
      rba_buffer_add_const(b, &p->mono[j].coeff);
    } else {
      assert(0 <= p->mono[j].var && p->mono[j].var < var_count);
      pprod_t* pp = var_pp(var_terms[p->mono[j].var]);
      rba_buffer_add_mono(b, &p->mono[j].coeff, pp);
    }
  }
}

/*
 * Check for integer feasibility
 */
static
fcheck_code_t mcarith_final_check(mcarith_solver_t *solver) {
  type_table_t types;
  init_type_table(&types, 64);
  type_t itype = int_type(&types);
  type_t rtype = real_type(&types);
  
  // Initialize power product table.
  pprod_table_t pprods;
  init_pprod_table(&pprods, 0); // Use default size  

  // Initialize term table
  term_table_t terms;
  const uint32_t init_termtable_size = 1024;

  // Var table for arithmetic
  arith_vartable_t* vtbl = &solver->simplex.vtbl;

  uint32_t vc = num_arith_vars(vtbl);
  init_term_table(&terms, init_termtable_size, &types, &pprods);

  context_t ctx;
  const bool qflag = false; // Quantifiers not allowed
  init_context(&ctx, &terms, QF_NRA, CTX_MODE_ONECHECK, CTX_ARCH_MCSAT, qflag);

  // Create array for mapping theory variables to initial term.
  term_t* var_terms = safe_malloc(vc * sizeof(term_t));
  // The variable denotes the constant one.
  rational_t one;
  q_set_one(&one);
  var_terms[0] = arith_constant(&terms, &one);
  // Allow variables/terms for later variables.
  for (uint32_t i = 1; i < vc; ++i) {
    bool is_int;
    pp_buffer_t b;

    switch (solver->vars[i].type) {
    case VAR_FREE:
      is_int = arith_var_is_int(vtbl, i);
      var_terms[i] = new_uninterpreted_term(&terms, is_int ? itype : rtype);
      break;
    case VAR_POLY:
      init_pp_buffer_from_pprod_map(&b, solver->vars[i].def.prod, var_terms, i);
      var_terms[i] = pprod_term_from_buffer(&terms, &b);
      break;
    default:
      assert(false);
    }
  }

  mcsat_solver_t* mcsat = mcsat_new(&ctx);

  term_t* assertions = safe_malloc(sizeof(term_t) * solver->assertion_count);
  literal_t* literals = safe_malloc(sizeof(literal_t) * solver->assertion_count + 1);
  size_t literal_count = 0;
  for (size_t i = 0; i < solver->assertion_count; ++i) {
    mcarith_assertion_t* a = solver->assertions + i;


    rba_buffer_t b;
    term_t p;
    switch (a->type) {
    case VAR_EQ:
      p = eq_term(&terms, var_terms[a->def.eq.lhs], var_terms[a->def.eq.rhs]);
      break;
    case POLY_EQ:
      init_rba_buffer_from_poly(&b, &pprods, a->def.poly, var_terms, vc);
      p = arith_eq_atom(&terms, arith_poly(&terms, &b));
      delete_rba_buffer(&b);
      break;
    case POLY_GE:
      init_rba_buffer_from_poly(&b, &pprods, a->def.poly, var_terms, vc);
      p = arith_geq_atom(&terms, arith_poly(&terms, &b));
      delete_rba_buffer(&b);
      break;
    default:
      longjmp(*solver->simplex.env, INTERNAL_ERROR);
    }
    if (a->lit != null_literal) {
      literals[literal_count++] = a->lit;
    }
    assertions[i] = a->tt ? p : not_term(&terms, p);
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
      longjmp(solver->simplex.env, INTERNAL_ERROR);
      break;
    }
  } else {
    safe_free(literals);
    longjmp(solver->simplex.env, INTERNAL_ERROR);
  }

  mcsat_destruct(mcsat);
  safe_free(mcsat);
  delete_context(&ctx);
  delete_term_table(&terms);
  delete_pprod_table(&pprods);
  delete_type_table(&types);
  return result;
}

/*
 * Increase dlevel in simplex and eqprop
 */
void mcarith_increase_decision_level(mcarith_solver_t *solver) {
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
  assert(0); //FIXME  
  //mcsat_push(solver->mcsat);
}

/*
 * Return to the previous base level
 */
void mcarith_pop(mcarith_solver_t *solver) {
  assert(0); //FIXME  
  //mcsat_pop(solver->mcsat);
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
bool mcarith_assert_atom(mcarith_solver_t *solver, void *a, literal_t l) {
  assert(0); //FIXME  
  return true;
}

/*
 * Expand a propagation object into a conjunction of literals
 * - expl is a pointer to a propagation object in solver->arena
 */
void mcarith_expand_explanation(mcarith_solver_t *solver, literal_t l, void *expl, ivector_t *v) {
  assert(false); // This function should not be called.
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
 * Create a new variable that represents constant q
 * - add a matrix column if that's a new variable
 */
thvar_t mcarith_create_const(mcarith_solver_t *solver, rational_t *q) {
  assert(0); //FIXME  
  return 0; // FIXME
}

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
 * Create a power of products.
 */
static
thvar_t mcarith_create_pprod(mcarith_solver_t *solver, pprod_t *p, thvar_t *map) {
  assert(pprod_degree(p) > 1); //FIXME  
  assert(!pp_is_empty(p));
  assert(!pp_is_var(p));

  // Remap variables in powerproduct
  pp_buffer_t b;
  init_pp_buffer(&b, p->len);
  for (uint32_t i = 0; i < p->len; ++i) {
    pp_buffer_set_varexp(&b, map[i], p->prod[i].exp);
  }
  pp_buffer_normalize(&b);

  // Assign power product
  thvar_t v = mcarith_create_var_internal(solver, false);
  solver->vars[v].type = VAR_POLY;
  solver->vars[v].def.prod = pp_buffer_getprod(&b);

  delete_pp_buffer(&b);
  return v;
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
 * Create the atom x - y == 0
 * - x and y are two theory variables
 */
literal_t mcarith_create_vareq_atom(mcarith_solver_t *solver, thvar_t x, thvar_t y) {
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
  assert(0); //FIXME  
  //FIXME
}

/*
 * Assert a top-level inequality (either x >= 0 or x < 0)
 * - tt indicates whether the constraint or its negation must be asserted
 *   tt == true  --> assert x >= 0
 *   tt == false --> assert x < 0
 */
void mcarith_assert_ge_axiom(mcarith_solver_t *solver, thvar_t x, bool tt){
  assert(0); //FIXME  
  //FIXME
}

/*
 * Assert top-level equality or disequality (either p == 0 or p != 0)
 * - map: convert p's variables to mcarith variables
 * - if tt is true  ---> assert p == 0
 * - if tt is false ---> assert p != 0
 */
void mcarith_assert_poly_eq_axiom(mcarith_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt) {
  assert(p->nterms > 0);
  mcarith_assertion_t* assert = alloc_assertion(solver);
  assert->type = POLY_EQ;
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
  mcarith_assertion_t* assert = alloc_assertion(solver);
  assert->type = POLY_GE;
  assert->def.poly = alloc_polynomial_from_map(p, map, solver->simplex.vtbl.nvars);
  assert->tt = tt;
  assert->lit = null_literal;
}

/*
 * If tt == true --> assert (x - y == 0)
 * If tt == false --> assert (x - y != 0)
 */
void mcarith_assert_vareq_axiom(mcarith_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  mcarith_assertion_t* assert = alloc_assertion(solver);
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


extern void simplex_attach_eterm(simplex_solver_t *solver, thvar_t v, eterm_t t);

/*
 * Attach egraph term t to a variable v
 * - v must not have an eterm attached already
 */
static void mcarith_attach_eterm(mcarith_solver_t *solver, thvar_t v, eterm_t t) {
  simplex_attach_eterm(&solver->simplex, v, t);
}

extern eterm_t simplex_eterm_of_var(simplex_solver_t *solver, thvar_t v);

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
  .create_var = (create_arith_var_fun_t) mcarith_create_var,
  .create_const = (create_arith_const_fun_t) mcarith_create_const,
  .create_poly = (create_arith_poly_fun_t) mcarith_create_poly,
  .create_pprod = (create_arith_pprod_fun_t) mcarith_create_pprod,

  .create_eq_atom = (create_arith_atom_fun_t) mcarith_create_eq_atom,
  .create_ge_atom = (create_arith_atom_fun_t) mcarith_create_ge_atom,
  .create_poly_eq_atom = (create_arith_patom_fun_t) mcarith_create_poly_eq_atom,
  .create_poly_ge_atom = (create_arith_patom_fun_t) mcarith_create_poly_ge_atom,
  .create_vareq_atom = (create_arith_vareq_atom_fun_t) mcarith_create_vareq_atom,

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