/*
 * SEARCH AND SOLVING PROCEDURES
 *
 * This module implements the check_context function (and variants).
 * It also implements model construction.
 */

#include <stdbool.h>
#include <assert.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>

#include "context.h"
#include "simplex.h"
#include "fun_solver.h"

// HACK
#include "prng.h"


/*
 * COMPILE-TIME FLAG for deleting learned clauses
 * if USE_REDUCE is non-zero, then reduce_clause_database is used
 * if USE_REDUCE is zero, remove_irrelevant_learned_clauses is used
 */
#define USE_REDUCE  1


/*
 * Externalize USE_REDUCE flag 
 */
#if USE_REDUCE
char *reduce_compile_option = "reduce";
#else
char *reduce_compile_option = "remove";
#endif




/*******************************
 *  DEFAULT SEARCH PARAMETERS  *
 ******************************/

/*
 * Default restart parameters for SMT solving
 * Minisat-like behavior
 */
#define DEFAULT_FAST_RESTART false
#define DEFAULT_C_THRESHOLD  100
#define DEFAULT_D_THRESHOLD  100
#define DEFAULT_C_FACTOR     1.5
#define DEFAULT_D_FACTOR     1.5

/*
 * Restart parameters if option --fast-restarts is set
 */
#define FAST_RESTART_C_THRESHOLD 100
#define FAST_RESTART_D_THRESHOLD 100
#define FAST_RESTART_C_FACTOR    1.1
#define FAST_RESTART_D_FACTOR    1.1

/*
 * Default clause deletion parameters
 */
#define DEFAULT_R_THRESHOLD   1000
#define DEFAULT_R_FRACTION    0.25
#define DEFAULT_R_FACTOR      1.05


/*
 * The default SMT parameters are copied from smt_core.h
 * - VAR_DECAY_FACTOR  = 0.95
 * - VAR_RANDOM_FACTOR = 0.02
 * - CLAUSE_DECAY_FACTOR = 0.999
 * - clause caching is disabled
 */
#define DEFAULT_VAR_DECAY      VAR_DECAY_FACTOR
#define DEFAULT_RANDOMNESS     VAR_RANDOM_FACTOR
#define DEFAULT_CLAUSE_DECAY   CLAUSE_DECAY_FACTOR
#define DEFAULT_CACHE_TCLAUSES false
#define DEFAULT_TCLAUSE_SIZE   0

/*
 * Default branching = the smt_core default
 */
#define DEFAULT_BRANCHING  BRANCHING_DEFAULT

/*
 * The default EGRAPH parameters are defined in egraph_types.h
 * - DEFAULT_MAX_ACKERMANN = 1000
 * - DEFAULT_MAX_BOOLACKERMANN = 600000
 * - DEFAULT_AUX_EQ_QUOTA = 100
 * - the dynamic ackermann heuristic is disabled for both 
 *   boolean and non-boolean terms
 * - DEFAULT_MAX_INTERFACE_EQS = 200
 */
#define DEFAULT_USE_DYN_ACK       false
#define DEFAULT_USE_BOOL_DYN_ACK  false
#define DEFAULT_AUX_EQ_RATIO      0.3


/*
 * Default SIMPLEX parameters defined in simplex_types.h
 * - SIMPLEX_DEFAULT_BLAND_THRESHOLD = 1000
 * - SIMPLEX_DEFAULT_PROP_ROW_SIZE = 30
 * - SIMPLEX_DEFAULT_CHECK_PERIOD = infinity
 * - propagation is disabled by default
 */
#define DEFAULT_SIMPLEX_PROP_FLAG     false


/*
 * Default parameters for the array solver (defined in fun_solver.h
 * - MAX_UPDATE_CONFLICTS = 20
 * - MAX_EXTENSIONALITY = 1
 */


/*
 * All default parameters
 */
static param_t default_settings = {
  DEFAULT_FAST_RESTART,
  DEFAULT_C_THRESHOLD,
  DEFAULT_D_THRESHOLD,
  DEFAULT_C_FACTOR,
  DEFAULT_D_FACTOR,

  DEFAULT_R_THRESHOLD,
  DEFAULT_R_FRACTION,
  DEFAULT_R_FACTOR,

  DEFAULT_VAR_DECAY,
  DEFAULT_RANDOMNESS,
  DEFAULT_BRANCHING,
  DEFAULT_CLAUSE_DECAY,
  DEFAULT_CACHE_TCLAUSES,
  DEFAULT_TCLAUSE_SIZE,


  DEFAULT_USE_DYN_ACK,
  DEFAULT_USE_BOOL_DYN_ACK,
  DEFAULT_MAX_ACKERMANN,
  DEFAULT_MAX_BOOLACKERMANN,
  DEFAULT_AUX_EQ_QUOTA,
  DEFAULT_AUX_EQ_RATIO,
  DEFAULT_MAX_INTERFACE_EQS,

  DEFAULT_SIMPLEX_PROP_FLAG,
  SIMPLEX_DEFAULT_PROP_ROW_SIZE,
  SIMPLEX_DEFAULT_BLAND_THRESHOLD,
  SIMPLEX_DEFAULT_CHECK_PERIOD,

  DEFAULT_MAX_UPDATE_CONFLICTS,
  DEFAULT_MAX_EXTENSIONALITY,
};



/*
 * Initialize params with a copy of default_settings
 */
void init_params_to_defaults(param_t *parameters) {
  *parameters = default_settings;
}





/*
 * MAIN SEARCH FUNCTIONS
 */

/*
 * Bounded search with the default branching heuristic (picosat-like)
 * - search until the conflict bound is reached or until the problem is solved.
 * - reduce_threshold: number of learned clauses above which reduce_clause_database is called
 * - r_factor = increment factor for reduce_threshold
 * - use the default branching heuristic implemented by the core
 */
static void search(smt_core_t *core, uint32_t conflict_bound, uint32_t *reduce_threshold, double r_factor) {
  uint64_t max_conflicts;
  uint32_t r_threshold;
  literal_t l;

  assert(smt_status(core) == STATUS_SEARCHING);
  max_conflicts = num_conflicts(core) + conflict_bound;
  r_threshold = *reduce_threshold;

  smt_process(core);
  while (smt_status(core) == STATUS_SEARCHING && num_conflicts(core) <= max_conflicts) {
    // reduce heuristic
#if USE_REDUCE
    if (num_learned_clauses(core) >= r_threshold) {
      reduce_clause_database(core);
      r_threshold = (uint32_t) (r_threshold * r_factor);
    }
#else
    if (num_conflicts(core) > 0 && num_conflicts(core) % 5000 == 0) {
      remove_irrelevant_learned_clauses(core);
    }
#endif

    // decision
    l = select_unassigned_literal(core);
    if (l == null_literal) {
      // all variables assigned: Call final_check
      smt_final_check(core);
    } else { 
      decide_literal(core, l);
      smt_process(core);
    }
  }

  *reduce_threshold = r_threshold;
}


/*
 * Polarity selection (implements branching heuristics)
 * - filter is given a literal l + core and must return either l or not l
 */
typedef literal_t (*branching_fun_t)(smt_core_t *core, literal_t l);


/*
 * Bounded search with a non-default branching heuristics
 * - search until the conflict bound is reached or until the problem is solved.
 * - reduce_threshold: number of learned clauses above which reduce_clause_database is called
 * - r_factor = increment factor for reduce_threshold
 * - use the branching heuristic implemented by branch
 */
static void special_search(smt_core_t *core, uint32_t conflict_bound, uint32_t *reduce_threshold, 
			   double r_factor, branching_fun_t branch) {
  uint64_t max_conflicts;
  uint32_t r_threshold;
  literal_t l;

  assert(smt_status(core) == STATUS_SEARCHING);
  max_conflicts = num_conflicts(core) + conflict_bound;
  r_threshold = *reduce_threshold;

  smt_process(core);
  while (smt_status(core) == STATUS_SEARCHING && num_conflicts(core) <= max_conflicts) {
#if USE_REDUCE
    // reduce heuristic
    if (num_learned_clauses(core) >= r_threshold) {
      reduce_clause_database(core);
      r_threshold = (uint32_t) (r_threshold * r_factor);
    }
#else
    if (num_conflicts(core) % 5000 == 4999) {
      remove_irrelevant_learned_clauses(core);
    }
#endif

    // decision
    l = select_unassigned_literal(core);
    if (l == null_literal) {
      // all variables assigned: call final check
      smt_final_check(core); 
    } else {
      // apply the branching heuristic
      l = branch(core, l);
      // propagation
      decide_literal(core, l);
      smt_process(core);
    }
  }

  *reduce_threshold = r_threshold;
}





/*
 * SUPPORTED BRANCHING 
 */

/*
 * Simple branching heuristics:
 * - branch to the negative polarity
 * - branch to the positive polarity
 */
static literal_t negative_branch(smt_core_t *core, literal_t l) {
  return l | 1; // force the sign bit to 1
}

static literal_t positive_branch(smt_core_t *core, literal_t l) {
  return l & ~1; // force the sign bit to 0
}


/*
 * For literals with no atom, use the default, otherwise let the theory solver decide
 */
static literal_t theory_branch(smt_core_t *core, literal_t l) {
  if (bvar_has_atom(core, var_of(l))) {
    l =  core->th_smt.select_polarity(core->th_solver, get_bvar_atom(core, var_of(l)), l);
  }
  return l;
}

// variants
static literal_t theory_or_neg_branch(smt_core_t *core, literal_t l) {
  if (bvar_has_atom(core, var_of(l))) {
    return core->th_smt.select_polarity(core->th_solver, get_bvar_atom(core, var_of(l)), l);
  } else {
    return l | 1;
  }
}

static literal_t theory_or_pos_branch(smt_core_t *core, literal_t l) {
  if (bvar_has_atom(core, var_of(l))) {
    return core->th_smt.select_polarity(core->th_solver, get_bvar_atom(core, var_of(l)), l);
  } else {
    return l & ~1;
  }
}



/*
 * Bit-vector branching: for atoms, branch using the default 
 * For literals with no atoms attached, branch randomly
 */
static literal_t bv_branch(smt_core_t *core, literal_t l) {
  if (!bvar_has_atom(core, var_of(l)) && (random_uint32() & 0x400)) {
    l = not(l);
  }
  return l;
}




/*
 * CORE SOLVER
 */

/*
 * Print some statistic data + header if requested (on stdout)
 */
static void show_progress(smt_core_t *core, 
			  uint32_t restart_threshold, uint32_t reduce_threshold, bool show_header) {

  if (show_header) {
    printf("---------------------------------------------------------------------------------------------------\n");
    printf("|     Thresholds    |  Binary   |      Original     |          Learned          |     Decisions   |\n");
    printf("|   Conf.      Del. |  Clauses  |   Clauses   Lits. |   Clauses  Lits. Lits/Cl. |   Total  Random |\n");
    printf("---------------------------------------------------------------------------------------------------\n");
  }

  printf("| %7"PRIu32"  %8"PRIu32" |  %8"PRIu32" | %8"PRIu32" %8"PRIu64" | %8"PRIu32" %8"PRIu64" %7.1f | %8"PRIu64" %6"PRIu64" |\n", 
	 restart_threshold, reduce_threshold, 
	 num_binary_clauses(core), 
	 num_prob_clauses(core), num_prob_literals(core),
	 num_learned_clauses(core), num_learned_literals(core), 
	 ((double) num_learned_literals(core)/num_learned_clauses(core)),
	 core->stats.decisions, core->stats.random_decisions);
  fflush(stdout);
}
			  

/*
 * Full solver:
 * - params: heuristic parameters.
 *   If params is NULL, the default settings are used.
 * - verbose: if true, prints some data after each outer restart
 */
static void solve(smt_core_t *core, param_t *params, bool verbose) {
  uint32_t c_threshold, d_threshold; // Picosat-style
  uint32_t reduce_threshold;
#if 0
  uint32_t n_reductions; // not used anymore?
#endif

  assert(smt_status(core) == STATUS_IDLE);

  c_threshold = params->c_threshold;
  d_threshold = c_threshold; // required by show_progress in slow_restart mode
  if (params->fast_restart) {
    d_threshold = params->d_threshold;
  }

#if 0
  n_reductions = num_reduce_calls(core);
#endif
  reduce_threshold = (uint32_t) (num_prob_clauses(core) * params->r_fraction);
  if (reduce_threshold < params->r_threshold) {
    reduce_threshold = params->r_threshold;
  }

  // initialize then do a propagation + simplification step.
  start_search(core);
  smt_process(core);
  if (verbose) {
    show_progress(core, d_threshold, reduce_threshold, true);
  }

  if (smt_status(core) == STATUS_SEARCHING) {
    // loop
    for (;;) {
      switch (params->branching) {
      case BRANCHING_DEFAULT:
	search(core, c_threshold, &reduce_threshold, params->r_factor);
	break;
      case BRANCHING_NEGATIVE:
	special_search(core, c_threshold, &reduce_threshold, params->r_factor, negative_branch);
	break;
      case BRANCHING_POSITIVE:
	special_search(core, c_threshold, &reduce_threshold, params->r_factor, positive_branch);
	break;
      case BRANCHING_THEORY:
	special_search(core, c_threshold, &reduce_threshold, params->r_factor, theory_branch);
	break;
      case BRANCHING_TH_NEG:
	special_search(core, c_threshold, &reduce_threshold, params->r_factor, theory_or_neg_branch);
	break;
      case BRANCHING_TH_POS:
	special_search(core, c_threshold, &reduce_threshold, params->r_factor, theory_or_pos_branch);
	break;
      case BRANCHING_BV:
	special_search(core, c_threshold, &reduce_threshold, params->r_factor, bv_branch);
	break;
      }

      if (smt_status(core) != STATUS_SEARCHING) break;

      smt_restart(core);

      // inner restart: increase c_threshold
      c_threshold = (uint32_t) (c_threshold * params->c_factor);

      if (c_threshold >= d_threshold) {
	d_threshold = c_threshold; // Minisat-style
	if (params->fast_restart) {
	  // outer restart: reset c_threshold and increase d_threshold
	  c_threshold = params->c_threshold;
	  d_threshold = (uint32_t) (d_threshold * params->d_factor);
	}

#if 0
	if (n_reductions < num_reduce_calls(core)) {
	  // Not good in slow_start mode.
	  // This leads to too many calls to reduce_clause_database
	  n_reductions = num_reduce_calls(core);
	  reduce_threshold = (uint32_t) (reduce_threshold * params->r_factor);
	}
#endif

	if (verbose) {
	  show_progress(core, d_threshold, reduce_threshold, false);
	}
      }
    }
  }

  if (verbose) {
    printf("---------------------------------------------------------------------------------------------------\n\n");
    fflush(stdout);
  }
}





/*
 * Initialize search parameters then call solve
 * - if ctx->status is not IDLE, return the status.
 */ 
smt_status_t check_context(context_t *ctx, param_t *params, bool verbose) {
  smt_status_t stat;
  smt_core_t *core;
  egraph_t *egraph;
  simplex_solver_t *simplex;
  fun_solver_t *fsolver;
  uint32_t quota;

  core = ctx->core;
  egraph = ctx->egraph;

  stat = smt_status(core);
  if (stat == STATUS_IDLE) {
    /*
     * Clean state: search can proceed
     * TODO: report an error if stat is not IDLE
     */
    if (params == NULL) {
      params = &default_settings;
    }

    /*
     * Set core parameters
     */
    set_randomness(core, params->randomness);
    set_var_decay_factor(core, params->var_decay);
    set_clause_decay_factor(core, params->clause_decay);
    if (params->cache_tclauses) {
      enable_theory_cache(core, params->tclause_size);      
    } else {
      disable_theory_cache(core);
    }

    /*
     * Set egraph paramters
     */
    if (egraph != NULL) {
      if (params->use_dyn_ack) {
	egraph_enable_dyn_ackermann(egraph, params->max_ackermann);
      } else {
	egraph_disable_dyn_ackermann(egraph);
      }
      if (params->use_bool_dyn_ack) {
	egraph_enable_dyn_boolackermann(egraph, params->max_boolackermann);
      } else {
	egraph_disable_dyn_boolackermann(egraph);
      }
      quota = egraph_num_terms(egraph) * params->aux_eq_ratio;
      if (quota < params->aux_eq_quota) {
	quota = params->aux_eq_quota;
      }
      egraph_set_aux_eq_quota(egraph, quota);
      egraph_set_max_interface_eqs(egraph, params->max_interface_eqs);
    }

    /*
     * Set simplex parameters
     */
    if (context_has_simplex_solver(ctx)) {
      simplex = ctx->arith_solver;
      if (params->use_simplex_prop) {
	simplex_enable_propagation(simplex);
	simplex_set_prop_threshold(simplex, params->max_prop_row_size);
      }
      simplex_set_bland_threshold(simplex, params->bland_threshold);
      simplex_set_integer_check_period(simplex, params->integer_check_period);
    }


    /*
     * Set array solver parameters
     */
    if (context_has_fun_solver(ctx)) {
      fsolver = ctx->fun_solver;
      fun_solver_set_max_update_conflicts(fsolver, params->max_update_conflicts);
      fun_solver_set_max_extensionality(fsolver, params->max_extensionality);
    }

    solve(core, params, verbose);
    stat = smt_status(core);
  }
 
  return stat;
}





/*
 * MODEL CONSTRUCTION
 */

/*
 * Value of literal l in ctx->core
 */
static value_t bool_value(context_t *ctx, value_table_t *vtbl, literal_t l) {
  value_t v;

  v = null_value; // prevent GCC warning
  switch (literal_value(ctx->core, l)) {
  case VAL_FALSE:
    v = vtbl_mk_false(vtbl);
    break;
  case VAL_UNDEF:
    v = vtbl_mk_unknown(vtbl);
    break;
  case VAL_TRUE:
    v = vtbl_mk_true(vtbl);
    break;
  }
  return v;
}


/*
 * Value of arithmetic variable x in ctx->arith_solver
 */
static value_t arith_value(context_t *ctx, value_table_t *vtbl, thvar_t x) {
  rational_t *a;
  value_t v;

  assert(context_has_arith_solver(ctx));

  a = &ctx->aux;
  if (ctx->arith->value_in_model(ctx->arith_solver, x, a)) {
    v = vtbl_mk_rational(vtbl, a);
  } else {
    v = vtbl_mk_unknown(vtbl);
  }

  return v;
}


/*
 * Value of bitvector variable x in ctx->bv_solver
 */
static value_t bv_value(context_t *ctx, value_table_t *vtbl, thvar_t x) {
  bvconstant_t *b;
  value_t v;

  assert(context_has_bv_solver(ctx));

  b = &ctx->bv_buffer;
  if (ctx->bv->value_in_model(ctx->bv_solver, x, b)) {
    v = vtbl_mk_bv_from_constant(vtbl, b);
  } else {
    v = vtbl_mk_unknown(vtbl);
  }

  return v;
}


/*
 * Get a value for term t in the solvers or egraph
 * - attach the mapping from t to that value in model
 * - if we don't have a concrete object for t but t is 
 *   mapped to a term u and the flag keep_subst is true, 
 *   then we store the mapping [t --> u] in the model's 
 *   alias map. 
 */
static void build_term_value(context_t *ctx, model_t *model, term_t t, bool keep_subst) {
  value_table_t *vtbl;
  term_t u;
  icode_t x;
  type_t tau;
  value_t v;

  x = code_of_term(&ctx->trans, t); // x = internalization code for t
  if (! code_is_valid(x)) { 
    // t may have been eliminated via variable elimination
    // so try substitution
    u = context_find_term_subst(ctx, t);
    if (u == NULL_TERM) {
      // no substituon for t
      return;
    }

    // substitution found: [t --> u]
    // see if we can map u to a concrete value
    x = code_of_term(&ctx->trans, u);
    if (! code_is_valid(x)) {
      if (keep_subst) {
      // keep the substitution [t --> u] in the model
	model_add_substitution(model, t, u);
      }
      return;
    }
  }

  assert(code_is_valid(x));

  /*
   * map t to the concrete object attached for x
   */
  vtbl = model_get_vtbl(model);
  if (code_is_eterm(x)) {
    /*
     * t is mapped to a term in the egraph or to true_occ/false_occ
     */
    if (x == occ2code(false_occ)) {
      v = vtbl_mk_false(vtbl);
    } else if (x == occ2code(true_occ)) {
      v = vtbl_mk_true(vtbl);
    } else {
      assert(context_has_egraph(ctx));
      v = egraph_get_value(ctx->egraph, vtbl, code2occ(x));
    }
      
  } else {
    /*
     * t is mapped to a literal or a theory variable
     */
    tau = term_type(ctx->terms, t);
    switch (type_kind(ctx->types, tau)) {
    case BOOL_TYPE:
      v = bool_value(ctx, vtbl, code2literal(x));
      break;
      
    case INT_TYPE:
    case REAL_TYPE:
      v = arith_value(ctx, vtbl, code2var(x));
      break;

    case BITVECTOR_TYPE:
      v = bv_value(ctx, vtbl, code2var(x));
      break;


    case UNUSED_TYPE:
    case SCALAR_TYPE:
    case UNINTERPRETED_TYPE:
    case TUPLE_TYPE:
    case FUNCTION_TYPE: 
    default:
      /*
       * This should never happen: 
       * scalar, uninterpreted, tuple, function terms
       * are mapped to egraph terms.
       */
      assert(false); 
      v = vtbl_mk_unknown(vtbl); // prevent GCC warning
      break;
    }
  }

  if (! object_is_unknown(vtbl, v)) {
    model_map_term(model, t, v);
  }

}




/*
 * Build a model for the current context
 * - the context status must be SAT (or UNKNOWN)
 * - if keep_subst is true, we store the term substitution 
 *   defined by ctx->pseudo_subst into the model
 */
model_t *context_build_model(context_t *ctx, bool keep_subst) {
  term_table_t *terms;
  model_t *model;
  uint32_t i, n;

  assert(smt_status(ctx->core) == STATUS_SAT || smt_status(ctx->core) == STATUS_UNKNOWN);
  
  /*
   * First build assignments in the satellite solvers
   * and get the val_in_model functions for the egraph
   */
  if (context_has_arith_solver(ctx)) {
    ctx->arith->build_model(ctx->arith_solver);
  }
  if (context_has_bv_solver(ctx)) {
    ctx->bv->build_model(ctx->bv_solver);
  }

  // allocate the model
  terms = ctx->terms;
  model = new_model(terms, keep_subst);

  /*
   * Construct the egraph model
   */
  if (context_has_egraph(ctx)) {
    egraph_build_model(ctx->egraph, model_get_vtbl(model));
  }

  // scan the internalization table
  n = number_of_terms(&ctx->trans);
  for (i=0; i<n; i++) {
    if (term_kind(terms, i) == UNINTERPRETED_TERM) {
      build_term_value(ctx, model, i, keep_subst);
    }
  }

  /*
   * Cleanup
   */
  if (context_has_arith_solver(ctx)) {
    ctx->arith->free_model(ctx->arith_solver);
  }
  if (context_has_bv_solver(ctx)) {
    ctx->bv->free_model(ctx->bv_solver);
  }
  if (context_has_egraph(ctx)) {
    egraph_free_model(ctx->egraph);
  }
  

  return model;
}



