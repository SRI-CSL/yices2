#include "l2o.h"
#include "l2o_internal.h"

#include "mcsat/bool/bool_plugin.h"


//
// Term cost fx
//

/** evaluates an individual term */
static
double l2o_cost_fx_term_eval(l2o_cost_fx_t *fx, const l2o_search_state_t *state) {
  l2o_cost_fx_term_t *fx_t = (l2o_cost_fx_term_t*) fx;
  delete_double_hmap(&fx_t->eval_map);
  if (fx_t->eval_cache.nelems > 0) {
    l2o_evaluator_construct_cache(fx->l2o, &fx_t->eval_map, state, &fx_t->eval_cache);
  } else {
    l2o_evaluator_construct(fx->l2o, &fx_t->eval_map, state);
  }
  return l2o_evaluate_term_approx(fx->l2o, &fx_t->eval_map, fx_t->term);
}

static
void l2o_cost_fx_term_update_cache(l2o_cost_fx_t *fx) {
  l2o_cost_fx_term_t *fx_t = (l2o_cost_fx_term_t*) fx;
  double_hmap_swap(&fx_t->eval_cache, &fx_t->eval_map);
}

void l2o_cost_fx_term_construct(l2o_t *l2o, l2o_cost_fx_term_t *fx, term_t t) {
  fx->fx.l2o = l2o;
  fx->fx.eval = l2o_cost_fx_term_eval;
  fx->fx.update_cache = l2o_cost_fx_term_update_cache;
  fx->term = t;
  init_double_hmap(&fx->eval_map, 0);
  init_double_hmap(&fx->eval_cache, 0);
}

void l2o_cost_fx_term_destruct(l2o_cost_fx_term_t *fx) {
  delete_double_hmap(&fx->eval_map);
  delete_double_hmap(&fx->eval_cache);
}


//
// CNF cost fx
//

#define L2O_COST_FX_INITIAL_CAPACITY 100

/** counts the number of unsatisfied clauses in the given state. */
static
double l2o_cost_fx_cnf_eval(l2o_cost_fx_t *fx, const l2o_search_state_t *state) {
  l2o_cost_fx_cnf_t *cnf = (l2o_cost_fx_cnf_t*) fx;
  (void)cnf;
  // TODO implement
  return 0;
}

static
void l2o_cost_fx_cnf_update_cache(l2o_cost_fx_t *fx) {
  l2o_cost_fx_cnf_t *fxc = (l2o_cost_fx_cnf_t*) fx;
  double_hmap_swap(&fxc->eval_cache, &fxc->eval_map);
}

void l2o_cost_fx_cnf_construct(l2o_t *l2o, l2o_cost_fx_cnf_t *fx) {
  assert(l2o->bool_plugin);
  fx->fx.l2o = l2o;
  fx->fx.eval = l2o_cost_fx_cnf_eval;
  fx->fx.update_cache = l2o_cost_fx_cnf_update_cache;

  init_double_hmap(&fx->eval_map, 0);
  init_double_hmap(&fx->eval_cache, 0);

  fx->capacity = L2O_COST_FX_INITIAL_CAPACITY;
  fx->lit = (term_t*) safe_malloc(sizeof(term_t)*fx->capacity);
  init_ivector(&fx->clause_ids, 0);
  int_lset_construct(&fx->var2clause);

  // terminate the list with an enpty clause
  ivector_push(&fx->clause_ids, 0);
  fx->lit[0] = NULL_TERM;
}

void l2o_cost_fx_cnf_destruct(l2o_cost_fx_cnf_t *fx) {
  safe_free(fx->lit);
  delete_ivector(&fx->clause_ids);
  int_lset_destruct(&fx->var2clause);
  delete_double_hmap(&fx->eval_map);
  delete_double_hmap(&fx->eval_cache);
}

static
uint32_t l2o_cost_fx_add_clause(l2o_cost_fx_cnf_t *fx, const ivector_t *clause) {
  assert(clause->size > 0);
  assert(fx->clause_ids.size > 0);
  uint32_t last_clause_id = ivector_last(&fx->clause_ids);
  assert(fx->lit[last_clause_id] == NULL_TERM);
  uint32_t required = last_clause_id + 1 + clause->size + 1;

  // ensure space
  if (required >= fx->capacity) {
    fx->capacity *= 2;
    fx->lit = (term_t*) safe_realloc(fx->lit, sizeof(term_t)*fx->capacity);
  }
  assert(required < fx->capacity);

  // add clause
  int i = 0;
  for (; i < clause->size; ++i) {
    fx->lit[last_clause_id + i] = clause->data[i];
  }
  fx->lit[last_clause_id + i] = NULL_TERM;

  // append an empty clause
  uint32_t new_last_clause_id = last_clause_id + i + 1;
  fx->lit[new_last_clause_id] = NULL_TERM;
  ivector_push(&fx->clause_ids, new_last_clause_id);

  return last_clause_id;
}

// TODO check for duplicate clauses
uint32_t l2o_cost_fx_cnf_add(l2o_cost_fx_cnf_t *fx, variable_t v) {
  plugin_t *bool_plugin = fx->fx.l2o->bool_plugin;
  assert(bool_plugin);

  uint32_t i;

  ivector_t clause_refs, terms;
  init_ivector(&clause_refs, 0);
  init_ivector(&terms, 0);
  if (bool_plugin_get_clauses_of_variable(bool_plugin, v, &clause_refs)) {
    // non-unit clause
    for (i = 0; i < clause_refs.size; ++i) {
      clause_ref_t ref = clause_refs.data[i];
      bool_plugin_query_clause(bool_plugin, ref, &terms);
      l2o_cost_fx_add_clause(fx, &terms);
      ivector_reset(&terms);
    }
  } else {
    // unit clause
    bool_plugin_query_unit_clause(bool_plugin, v, &terms);
    l2o_cost_fx_add_clause(fx, &terms);
    i = 1;
  }
  delete_ivector(&clause_refs);
  delete_ivector(&terms);
  return i;
}

void l2o_cost_fx_print(const l2o_cost_fx_cnf_t *fx, FILE *out) {
  int i = 0;

  fprintf(out, "Cost function with %d clauses:\n  (", fx->clause_ids.size - 1);
  while (1) {
    if (fx->lit[i] == NULL_TERM) {
      if (fx->lit[i + 1] == NULL_TERM) break;
      fprintf(out, ")\n  (");
    } else {
      term_print_to_file(out, fx->fx.l2o->terms, fx->lit[i]);
      //fprintf(out, "%d", fx->lit[i]);
      if (fx->lit[i + 1] != NULL_TERM) fprintf(out, ", ");
    }
    ++ i;
  }
  fprintf(out, ")\n");
}
