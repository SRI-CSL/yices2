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

#include <stdbool.h>

#include <poly/polynomial_context.h>

#include "mcsat/ff/ff_feasible_set_db.h"
#include "utils/int_vectors.h"
#include "utils/ptr_hash_map.h"
#include "mcsat/tracing.h"
#include "mcsat/variable_db.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/utils/value_version_set.h"

// TODO long term: create a feasibility set in libpoly that handles int lp_value wrt. int_ring directly

/**
 * This stores all possible values for one variable with all updates.
 * Inverted is used first, as soon as a non-values_inverted set is added, values is used.
 * All elements of values and values_inverted are lp_integer mod K.
 */
typedef struct {
  /** all elements, but those (filled first) */
  value_version_set_t *values_inverted;
  /** the elements (filled second) */
  value_version_set_t *values;
  /** Reasons for the updates, length of each reason is determined by reasons_sizes.
   * If reason size is one then constraint, otherwise disjunction */
  ivector_t reasons;
  /** Sizes of the reasons. Length is sum of timestamps of both sets. */
  ivector_t reasons_sizes;
} feasibility_int_set_t;

struct ff_feasible_set_db_struct {
  /** One set for each variable [variable_t -> feasibility_int_set_t] */
  ptr_hmap_t sets;

  /** Variables that were updated, so we can backtrack */
  ivector_t updates;

  /** Size of the updates array, so that we can backtrack */
  uint32_t updates_size;

  /** All variables that were fixed */
  ivector_t fixed_variables;

  /** Size of the fixed variables array, for backtracking */
  uint32_t fixed_variable_size;

  /** Index into the fixed variables */
  uint32_t fixed_variables_i;

  /** Scope for push/pop */
  scope_holder_t scope;

  /** Lp context */
  lp_int_ring_t *K;

  /** BV context */
  plugin_context_t* ctx;
};


static
feasibility_int_set_t* feasibility_int_set_new(void) {
  feasibility_int_set_t *set = safe_malloc(sizeof(feasibility_int_set_t));
  set->values_inverted = value_version_set_new(VALUE_SET_UNION);
  set->values = value_version_set_new(VALUE_SET_INTERSECTION);
  init_ivector(&set->reasons, 0);
  init_ivector(&set->reasons_sizes, 0);
  return set;
}

static
void feasibility_int_set_delete(feasibility_int_set_t *set) {
  value_version_set_delete(set->values_inverted);
  value_version_set_delete(set->values);
  delete_ivector(&set->reasons);
  delete_ivector(&set->reasons_sizes);
  safe_free(set);
}

static
void feasibility_int_set_pop(feasibility_int_set_t *set, size_t cnt) {
  uint32_t
    ts_values = value_version_set_get_timestamp(set->values),
    ts_inverted = value_version_set_get_timestamp(set->values_inverted);

  (void)ts_inverted;
  assert(ts_values + ts_inverted == set->reasons_sizes.size);

  if (cnt > 0) {
    value_version_set_pop(set->values, cnt);
  }
  if (cnt > ts_values) {
    value_version_set_pop(set->values_inverted, cnt - ts_values);
  }

  for (size_t i = 0; i < cnt; ++i) {
    int32_t sz = ivector_pop2(&set->reasons_sizes);
    assert(set->reasons.size >= sz);
    for (int32_t j = 0; j < sz; ++j) {
      ivector_pop(&set->reasons);
    }
  }
}

static inline
uint32_t feasibility_int_set_get_ts(const feasibility_int_set_t *set) {
  uint32_t ts = set->reasons_sizes.size;
  assert(ts == value_version_set_get_timestamp(set->values) + value_version_set_get_timestamp(set->values_inverted));
  return ts;
}

/** returns true if the set contains any info */
static inline
bool feasibility_int_set_has_info(const feasibility_int_set_t *set) {
  return feasibility_int_set_get_ts(set) > 0;
}

static inline
bool feasibility_int_set_is_inverted(const feasibility_int_set_t *set) {
  bool rslt = feasibility_int_set_get_ts(set) <= value_version_set_get_timestamp(set->values_inverted);
  assert(rslt == (value_version_set_count(set->values) == UINT32_MAX));
  return rslt;
}

static
bool feasibility_int_set_is_value_valid(const feasibility_int_set_t *set, const lp_value_t *value) {
  bool valid = false;
  mcsat_value_t value_mcsat;
  mcsat_value_construct_lp_value(&value_mcsat, value);
  if (feasibility_int_set_is_inverted(set)) {
    valid = !value_version_set_contains(set->values_inverted, &value_mcsat);
  } else {
    valid = value_version_set_contains(set->values, &value_mcsat);
  }
  mcsat_value_destruct(&value_mcsat);
  return valid;
}

/** returns an estimated count. 0 and 1 are guaranteed to be correct. */
static
uint32_t feasibility_int_set_count_approx(const feasibility_int_set_t *set, const lp_int_ring_t *K) {
  if (!feasibility_int_set_is_inverted(set)) {
    // exact value returned
    return value_version_set_count(set->values);
  } else {
    int cmp;
    // approximate value (0, 1, or 2)
    uint32_t set_cnt = value_version_set_count(set->values_inverted);
    cmp = lp_integer_cmp_int(lp_Z, &K->M, set_cnt);
    assert(cmp >= 0);
    if (cmp == 0) return 0;
    // all but one are accounted for
    cmp = lp_integer_cmp_int(lp_Z, &K->M, set_cnt + 1);
    if (cmp == 0) return 1;
    // more than 1 element are in the set
    return 2;
  }
}

/** prints the set at the timestamp if the timestamp exists */
static
void feasibility_int_set_print_at(const feasibility_int_set_t *set, uint32_t timestamp, bool print_reasons, FILE *out) {
  uint32_t reasons_size = set->reasons_sizes.data[timestamp-1];
  if (reasons_size == 0) {
    return;
  }

  uint32_t ts_invert = value_version_set_get_timestamp(set->values_inverted);
  if (ts_invert >= timestamp) {
    fprintf(out, "\tF - ");
    value_version_set_print_at(set->values_inverted, timestamp, out);
  } else {
    fprintf(out, "\t");
    value_version_set_print_at(set->values, timestamp - ts_invert, out);
  }

  // TODO
  (void)print_reasons;
//  if (reasons_size > 1) {
//    fprintf(out, "\t\tDue to lemma\n");
//  } else {
//    fprintf(out, "\t\tDue to ");
//    // ???
//  }
}

static
bool value_version_set_contains_inverted(void *set, const mcsat_value_t *val) {
  return !value_version_set_contains((value_version_set_t*)set, val);
}

// returns false if there was no change to the set and an empty ts was generated
static
bool feasibility_int_set_update(ff_feasible_set_db_t* db, feasibility_int_set_t *set, lp_value_t* new_set, size_t new_set_size, bool inverted, variable_t* reasons, size_t reasons_count) {
  bool modified;

  // create mcsat_values to be used in the set
  mcsat_value_t *tmp = safe_malloc(new_set_size * sizeof(mcsat_value_t));
  for (int i = 0; i < new_set_size; ++i) {
    mcsat_value_construct_lp_value(&tmp[i], &new_set[i]);
  }

  if (feasibility_int_set_is_inverted(set)) {
    if (inverted) {
      // just add them to the excluded
      modified = value_version_set_push(set->values_inverted, tmp, new_set_size);
    } else {
      // the set is switched to non-inverted, add all that are not in values_inverted
      assert(value_version_set_get_timestamp(set->values) == 0);
      // returns false if the result is empty
      value_version_set_push_filter(set->values, tmp, new_set_size, set->values_inverted, value_version_set_contains_inverted);
      int cmp = lp_integer_cmp_int(lp_Z, &db->K->M, value_version_set_count(set->values) + value_version_set_count(set->values_inverted));
      assert(cmp >= 0);
      modified = cmp != 0;
    }
  } else {
    if (inverted) {
      // push those that are NOT in new_set
      modified = value_version_set_push_intersect_inverted(set->values, tmp, new_set_size);
    } else {
      // push all of new_set
      modified = value_version_set_push(set->values, tmp, new_set_size);
    }
  }

  // cleanup
  for (int i = 0; i < new_set_size; ++i) {
    mcsat_value_destruct(&tmp[i]);
  }
  safe_free(tmp);

  if (modified) {
    // add the reasons
    for (int i = 0; i < reasons_count; ++i) {
      ivector_push(&set->reasons, reasons[i]);
    }
    ivector_push(&set->reasons_sizes, reasons_count);
  } else {
    // add empty entry
    ivector_push(&set->reasons_sizes, 0);
  }

  return modified;
}

/** Create a new database */
ff_feasible_set_db_t* ff_feasible_set_db_new(plugin_context_t* ctx, lp_data_t *lp_data) {
  ff_feasible_set_db_t* db = safe_malloc(sizeof(ff_feasible_set_db_t));

  init_ptr_hmap(&db->sets, 0);

  init_ivector(&db->updates, 0);
  init_ivector(&db->fixed_variables, 0);

  db->updates_size = 0;
  db->fixed_variable_size = 0;
  db->fixed_variables_i = 0;

  scope_holder_construct(&db->scope);

  lp_int_ring_t *K = lp_data->lp_ctx->K;
  assert(K != lp_Z);
  db->K = K;
  lp_int_ring_attach(db->K);

  db->ctx = ctx;

  return db;
}

/** Delete the database */
void ff_feasible_set_db_delete(ff_feasible_set_db_t* db) {
  // Delete the sets
  ptr_hmap_t *hmap = &db->sets;
  for (ptr_hmap_pair_t *p = ptr_hmap_first_record(hmap);
       p != NULL;
       p = ptr_hmap_next_record(hmap, p)) {
    assert(p->val != NULL);
    feasibility_int_set_delete(p->val);
  }
  delete_ptr_hmap(hmap);

  // Delete the other stuff
  delete_ivector(&db->updates);
  delete_ivector(&db->fixed_variables);
  scope_holder_destruct(&db->scope);

  lp_int_ring_detach(db->K);

  // Free the memory
  safe_free(db);
}

/** Print the feasible sets of given variable */
void ff_feasible_set_db_print_var(ff_feasible_set_db_t* db, variable_t var, FILE* out) {
  fprintf(out, "Feasible sets of ");
  variable_db_print_variable(db->ctx->var_db, var, out);
  fprintf(out, " :\n");
  ptr_hmap_pair_t *found = ptr_hmap_find(&db->sets, var);
  if (found != NULL) {
    feasibility_int_set_t *set = found->val;
    for (uint32_t i = feasibility_int_set_get_ts(set); i > 0; --i) {
      fprintf(out, "\t");
      feasibility_int_set_print_at(set, i, true, out);
      fprintf(out, "\n");
    }
  } else {
    fprintf(out, "\tvariable %d not found in db\n", var);
  }
}

/** Print the feasible set database */
void ff_feasible_set_db_print(ff_feasible_set_db_t* db, FILE* out) {
  for (ptr_hmap_pair_t* it = ptr_hmap_first_record(&db->sets);
  it != NULL;
  it = ptr_hmap_next_record(&db->sets, it)) {
    variable_t var = it->key;
    feasibility_int_set_t *set = it->val;

    fprintf(out, "Feasible sets of ");
    variable_db_print_variable(db->ctx->var_db, var, out);
    fprintf(out, " :\n");
    if (trail_has_value(db->ctx->trail, var)) {
      fprintf(out, "\tassigned to: ");
      const mcsat_value_t* var_value = trail_get_value(db->ctx->trail, var);
      mcsat_value_print(var_value, out);
      fprintf(out, "\n");
    }
    for (uint32_t i = feasibility_int_set_get_ts(set); i > 0; --i) {
      fprintf(out, "\t");
      feasibility_int_set_print_at(set, i, false, out);
      fprintf(out, "\n");
    }
  }
}

static inline
ff_feasible_set_status_t cnt_to_status(size_t cnt) {
  if (cnt == 0) {
    return FF_FEASIBLE_SET_EMPTY;
  } else if (cnt == 1) {
    return FF_FEASIBLE_SET_UNIQUE;
  } else {
    return FF_FEASIBLE_SET_MANY;
  }
}

ff_feasible_set_status_t ff_feasible_set_db_update(ff_feasible_set_db_t* db, variable_t x, lp_value_t* new_set, size_t new_set_size, bool inverted, variable_t* reasons, size_t reasons_count) {
  if (ctx_trace_enabled(db->ctx, "ff::feasible_set_db")) {
    fprintf(ctx_trace_out(db->ctx), "ff_feasible_set_db_update\n");
    ff_feasible_set_db_print(db, ctx_trace_out(db->ctx));
  }

  assert(db->updates_size == db->updates.size);

  // check if the variable already exists
  ptr_hmap_pair_t *found = ptr_hmap_get(&db->sets, x);
  if (found->val == NULL) {
    // this is a new one
    found->val = feasibility_int_set_new();
  }
  feasibility_int_set_t *set = found->val;

  // it's already empty
  if (feasibility_int_set_count_approx(set, db->K) == 0) {
    return FF_FEASIBLE_SET_EMPTY;
  }

  // add to updates list
  ivector_push(&db->updates, x);
  db->updates_size++;
  assert(db->updates_size == db->updates.size);

  // modify the set
  bool modified = feasibility_int_set_update(db, set, new_set, new_set_size, inverted, reasons, reasons_count);
  size_t cnt = feasibility_int_set_count_approx(set, db->K);
  if (!modified) {
    return cnt_to_status(cnt);
  }

  if (cnt == 0) {
    return FF_FEASIBLE_SET_EMPTY;
  } else if (cnt == 1) {
    // If fixed, put into the fixed array
    ivector_push(&db->fixed_variables, x);
    db->fixed_variable_size ++;
  }
  return cnt_to_status(cnt);
}

bool ff_feasible_set_db_pick_value(const ff_feasible_set_db_t* db, variable_t x, lp_value_t *value) {
  ptr_hmap_pair_t *p = ptr_hmap_find(&db->sets, x);
  if (p == NULL) {
    return false;
  }

  feasibility_int_set_t *set = p->val;
  if (!feasibility_int_set_is_inverted(set)) {
    const mcsat_value_t *val = value_version_set_any(set->values);
    if (val == NULL) {
      return false;
    }
    assert(val->type == VALUE_LIBPOLY);
    lp_value_t tmp;
    lp_value_construct_copy(&tmp, &val->lp_value);
    lp_value_swap(&tmp, value);
    lp_value_destruct(&tmp);
    return true;
  } else {
    assert(db->K != lp_Z);

    mcsat_value_t tmp;
    lp_integer_t zero;
    lp_integer_construct(&zero);
    mcsat_value_construct_lp_value_direct(&tmp, LP_VALUE_INTEGER, &zero);
    lp_integer_destruct(&zero);
    lp_integer_t *tmp_int = &tmp.lp_value.value.z;
    assert(lp_integer_is_zero(db->K, tmp_int));
    bool found = false;
    do {
      if (!value_version_set_contains(set->values_inverted, &tmp)) {
        lp_value_swap(&tmp.lp_value, value);
        found = true;
        break;
      }
      lp_integer_inc(db->K, tmp_int);
    } while (!lp_integer_is_zero(db->K, tmp_int));
    mcsat_value_destruct(&tmp);
    return found;
  }
}

void ff_feasible_set_db_get_conflict_reasons(const ff_feasible_set_db_t* db, variable_t x, ivector_t* reasons_out, ivector_t* lemma_reasons) {
  // TODO implement me
}

bool ff_feasible_set_db_is_value_valid(const ff_feasible_set_db_t *db, variable_t x, const lp_value_t *value) {
  ptr_hmap_pair_t *found = ptr_hmap_find(&db->sets, x);
  return found == NULL || feasibility_int_set_is_value_valid(found->val, value);
}

bool ff_feasible_set_db_has_info(const ff_feasible_set_db_t* db, variable_t x) {
  ptr_hmap_pair_t *found = ptr_hmap_find(&db->sets, x);
  return found != NULL && feasibility_int_set_has_info(found->val);
}

void ff_feasible_set_db_push(ff_feasible_set_db_t *db) {
  scope_holder_push(&db->scope,
     &db->updates_size,
     &db->fixed_variable_size,
     &db->fixed_variables_i,
     NULL
  );
}

void ff_feasible_set_db_pop(ff_feasible_set_db_t* db) {
  if (ctx_trace_enabled(db->ctx, "ff::ff_feasible_set_db")) {
    fprintf(ctx_trace_out(db->ctx), "ff_feasible_set_db_pop");
    ff_feasible_set_db_print(db, ctx_trace_out(db->ctx));
  }

  int_hmap_t pop_cnt;
  int_hmap_pair_t *p;

  scope_holder_pop(&db->scope,
     &db->updates_size,
     &db->fixed_variable_size,
     &db->fixed_variables_i,
     NULL
  );

  // Undo fixed variables
  ivector_shrink(&db->fixed_variables, db->fixed_variable_size);

  init_int_hmap(&pop_cnt, 0);
  // Undo updates
  while (db->updates.size > db->updates_size) {
    // The variable that was updated
    variable_t x = ivector_pop2(&db->updates);
    p = int_hmap_get(&pop_cnt, x);
    p->val = p->val == -1 ? 1 : p->val + 1;
  }
  for (p = int_hmap_first_record(&pop_cnt);
       p != NULL;
       p = int_hmap_next_record(&pop_cnt, p)) {
    ptr_hmap_pair_t *find = ptr_hmap_find(&db->sets, p->key);
    assert(p->val > 0);
    assert(find != NULL);
    assert(find->key == p->key);
    feasibility_int_set_pop(find->val, p->val);
  }
  delete_int_hmap(&pop_cnt);

  if (ctx_trace_enabled(db->ctx, "ff::ff_feasible_set_db")) {
    ff_feasible_set_db_print(db, ctx_trace_out(db->ctx));
  }
}

void ff_feasible_set_db_gc_mark(ff_feasible_set_db_t* db, gc_info_t* gc_vars) {
  assert(db->ctx->trail->decision_level == db->ctx->trail->decision_level_base);

  if (gc_vars->level == 0) {
    // We keep all the reasons (start from 1, 0 is not used)
    ptr_hmap_t *hmap = &db->sets;
    for (ptr_hmap_pair_t *p = ptr_hmap_first_record(hmap);
         p != NULL;
         p = ptr_hmap_next_record(hmap, p)) {
      assert(p->val != NULL);
      feasibility_int_set_t *set = p->val;
      for (int i = 0; i < set->reasons.size; ++i) {
        gc_info_mark(gc_vars, set->reasons.data[i]);
      }
    }
  }
}

variable_t ff_feasible_set_db_get_fixed(ff_feasible_set_db_t* db) {
  for (; db->fixed_variables_i < db->fixed_variables.size; ++ db->fixed_variables_i) {
    variable_t var = db->fixed_variables.data[db->fixed_variables_i];
    if (!trail_has_value(db->ctx->trail, var)) {
      return var;
    }
  }
  return variable_null;
}
