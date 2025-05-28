#include "l2o.h"
#include "l2o_internal.h"

#include "mcsat/bool/bool_plugin.h"

#define L2O_COST_FX_INITIAL_CAPACITY 100

void l2o_cost_fx_construct(l2o_t *l2o, l2o_cost_fx_t *fx) {
  assert(l2o->bool_plugin);
  fx->l2o = l2o;
  fx->capacity = L2O_COST_FX_INITIAL_CAPACITY;
  fx->lit = (term_t*) safe_malloc(sizeof(term_t)*fx->capacity);
  init_ivector(&fx->clause_ids, 0);
  int_lset_construct(&fx->var2clause);

  // terminate the list with an enpty clause
  ivector_push(&fx->clause_ids, 0);
  fx->lit[0] = NULL_TERM;
}

void l2o_cost_fx_destruct(l2o_cost_fx_t *fx) {
  safe_free(fx->lit);
  delete_ivector(&fx->clause_ids);
  int_lset_destruct(&fx->var2clause);
}

static
uint32_t l2o_cost_fx_add_clause(l2o_cost_fx_t *fx, const ivector_t *clause) {
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
uint32_t l2o_cost_fx_add(l2o_cost_fx_t *fx, variable_t v) {
  assert(fx->l2o->bool_plugin);
  uint32_t i;

  ivector_t clause_refs, terms;
  init_ivector(&clause_refs, 0);
  init_ivector(&terms, 0);
  if (bool_plugin_get_clauses_of_variable(fx->l2o->bool_plugin, v, &clause_refs)) {
    // non-unit clause
    for (i = 0; i < clause_refs.size; ++i) {
      clause_ref_t ref = clause_refs.data[i];
      bool_plugin_query_clause(fx->l2o->bool_plugin, ref, &terms);
      l2o_cost_fx_add_clause(fx, &terms);
      ivector_reset(&terms);
    }
  } else {
    // unit clause
    bool_plugin_query_unit_clause(fx->l2o->bool_plugin, v, &terms);
    l2o_cost_fx_add_clause(fx, &terms);
    i = 1;
  }
  delete_ivector(&clause_refs);
  delete_ivector(&terms);
  return i;
}

/** counts the number of unsatisfied clauses in the given state. */
uint32_t l2o_cost_fx_eval(const l2o_cost_fx_t *fx, const l2o_search_state_t *state) {
  return 0;
}

void l2o_cost_fx_print(const l2o_cost_fx_t *fx, FILE *out) {
  int i = 0;

  fprintf(out, "Cost function with %d clauses:\n  (", fx->clause_ids.size - 1);
  while (1) {
    if (fx->lit[i] == NULL_TERM) {
      if (fx->lit[i + 1] == NULL_TERM) break;
      fprintf(out, ")\n  (");
    } else {
      term_print_to_file(out, fx->l2o->terms, fx->lit[i]);
      //fprintf(out, "%d", fx->lit[i]);
      if (fx->lit[i + 1] != NULL_TERM) fprintf(out, ", ");
    }
    ++ i;
  }
  fprintf(out, ")\n");
}
