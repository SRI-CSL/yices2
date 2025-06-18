#include "l2o.h"
#include "l2o_internal.h"

#include <math.h>

//
// Term cost fx
//

/** evaluates an individual term */
static
double l2o_cost_fx_term_eval(l2o_cost_fx_t *fx, const l2o_search_state_t *state) {
  l2o_cost_fx_term_t *fx_t = (l2o_cost_fx_term_t*) fx;
  l2o_evaluator_set_state(&fx->evaluator, state);
  return l2o_evaluator_run_term(&fx->evaluator, fx_t->term);
}

static
void l2o_cost_fx_term_update_cache(l2o_cost_fx_t *fx) {
  l2o_evaluator_update_cache(&fx->evaluator);
}

static
void l2o_cost_fx_term_get_free_vars(const l2o_cost_fx_t *fx, ivector_t *v) {
  l2o_t *l2o = fx->l2o;
  l2o_cost_fx_term_t *fx_t = (l2o_cost_fx_term_t*) fx;

  ivector_reset(v);
  int_hmmap_find_all(&l2o->var_member, unsigned_term(fx_t->term), v);
  ivector_remove_duplicates(v);
}

static
void l2o_cost_fx_term_destruct(l2o_cost_fx_t *fx) {
  l2o_evaluator_destruct(&fx->evaluator);
}

void l2o_cost_fx_term_construct(l2o_t *l2o, l2o_cost_fx_term_t *fx, term_t t) {
  fx->fx.l2o = l2o;
  fx->fx.eval = l2o_cost_fx_term_eval;
  fx->fx.update_cache = l2o_cost_fx_term_update_cache;
  fx->fx.get_free_vars = l2o_cost_fx_term_get_free_vars;
  fx->fx.destruct = l2o_cost_fx_term_destruct;
  fx->term = t;
  l2o_evaluator_construct(l2o, &fx->fx.evaluator);
}


//
// CNF cost fx
//

#define L2O_COST_FX_INITIAL_CAPACITY 100

static
bool is_clause_sat(l2o_evaluator_t *e, term_t *lit) {
  uint32_t i;

  // don't allow empty clauses
  assert(lit[0] != NULL_TERM);

  // first run: check if a term is cached
  i = 0;
  while(lit[i] != NULL_TERM) {
    double val = l2o_evaluator_get_value_if_exists(e, lit[i]);
    assert(val == 0.0 || val == 1.0 || val == INFINITY);
    if (val == 1.0) {
      return true;
    }
    ++ i;
  }

  // second run: evaluate the terms
  i = 0;
  while(lit[i] != NULL_TERM) {
    double val = l2o_evaluator_run_term(e, lit[i]);
    assert(val == 0.0 || val == 1.0);
    if (val == 1.0) {
      return true;
    }
    ++ i;
  }

  return false;
}

/** counts the number of unsatisfied clauses in the given state. */
static
double l2o_cost_fx_cnf_eval(l2o_cost_fx_t *fx, const l2o_search_state_t *state) {
  l2o_cost_fx_cnf_t *fx_cnf = (l2o_cost_fx_cnf_t*) fx;
  l2o_evaluator_set_state(&fx->evaluator, state);
  double cost = 0;
  uint32_t idx = 0;
  for (uint32_t i = 0; i < fx_cnf->clause_ids.size; ++i) {
    idx = fx_cnf->clause_ids.data[i];
    assert(idx == 0 || fx_cnf->lit[idx-1] == NULL_TERM);
    if (fx_cnf->lit[idx] == NULL_TERM) break;
    if (!is_clause_sat(&fx->evaluator, fx_cnf->lit + idx)) {
      cost += 1.0;
    }
  }
  assert(fx_cnf->lit[idx] == NULL_TERM);
  
  return cost;
}

static
void l2o_cost_fx_cnf_update_cache(l2o_cost_fx_t *fx) {
  l2o_evaluator_update_cache(&fx->evaluator);
}

static
void l2o_cost_fx_cnf_get_free_vars(const l2o_cost_fx_t *fx, ivector_t *v) {
  l2o_cost_fx_cnf_t *fx_cnf = (l2o_cost_fx_cnf_t*)fx;
  l2o_t *l2o = fx->l2o;

  ivector_t free_vars;
  init_ivector(&free_vars, 0);

  for(uint32_t p = 0; true; ++ p) {
    assert(p + 1 < fx_cnf->capacity);
    if (fx_cnf->lit[p] == NULL_TERM && fx_cnf->lit[p+1] == NULL_TERM) break;
    if (fx_cnf->lit[p] == NULL_TERM) continue;
    term_t t = unsigned_term(fx_cnf->lit[p]);
    assert(int_hmmap_contains_key(&l2o->var_member, t));
    int_hmmap_find_all(&l2o->var_member, t, &free_vars);
  }

  ivector_remove_duplicates(&free_vars);
  ivector_append(v, &free_vars);
  delete_ivector(&free_vars);
}

static
void l2o_cost_fx_cnf_destruct(l2o_cost_fx_t *fx) {
  l2o_cost_fx_cnf_t *fx_cnf = (l2o_cost_fx_cnf_t*) fx;
  safe_free(fx_cnf->lit);
  delete_ivector(&fx_cnf->clause_ids);
  int_lset_destruct(&fx_cnf->var2clause);
  l2o_evaluator_destruct(&fx->evaluator);
}


void l2o_cost_fx_cnf_construct(l2o_t *l2o, l2o_cost_fx_cnf_t *fx) {
  assert(l2o->bool_plugin);
  fx->fx.l2o = l2o;
  fx->fx.eval = l2o_cost_fx_cnf_eval;
  fx->fx.update_cache = l2o_cost_fx_cnf_update_cache;
  fx->fx.get_free_vars = l2o_cost_fx_cnf_get_free_vars;
  fx->fx.destruct = l2o_cost_fx_cnf_destruct;
  l2o_evaluator_construct(l2o, &fx->fx.evaluator);

  fx->capacity = L2O_COST_FX_INITIAL_CAPACITY;
  fx->lit = (term_t*) safe_malloc(sizeof(term_t)*fx->capacity);
  init_ivector(&fx->clause_ids, 0);
  int_lset_construct(&fx->var2clause);

  // terminate the list with an enpty clause
  ivector_push(&fx->clause_ids, 0);
  fx->lit[0] = NULL_TERM;
}

uint32_t l2o_cost_fx_cnf_add_clause(l2o_cost_fx_cnf_t *fx, const ivector_t *clause) {
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
    term_t lit = clause->data[i];
    fx->lit[last_clause_id + i] = lit;
  }
  fx->lit[last_clause_id + i] = NULL_TERM;

  // append an empty clause
  uint32_t new_last_clause_id = last_clause_id + i + 1;
  fx->lit[new_last_clause_id] = NULL_TERM;
  ivector_push(&fx->clause_ids, new_last_clause_id);

  return last_clause_id;
}

void l2o_cost_fx_cnf_print(const l2o_cost_fx_cnf_t *fx, FILE *out) {
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
