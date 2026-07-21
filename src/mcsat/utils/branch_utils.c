/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "mcsat/utils/branch_utils.h"

static
bool mcsat_branch_bool_term_value(const plugin_context_t* ctx, term_t t, bool* value) {
  variable_t v;
  const mcsat_value_t* val;

  if (t == NULL_TERM) {
    return false;
  }
  if (t == true_term) {
    *value = true;
    return true;
  }
  if (t == false_term) {
    *value = false;
    return true;
  }

  v = variable_db_get_variable_if_exists(ctx->var_db, unsigned_term(t));
  if (v == variable_null || !trail_has_value(ctx->trail, v)) {
    return false;
  }

  val = trail_get_value(ctx->trail, v);
  if (val->type != VALUE_BOOLEAN) {
    return false;
  }

  *value = val->b;
  if (is_neg_term(t)) {
    *value = !*value;
  }
  return true;
}

bool mcsat_branch_bool_term_is_true(const plugin_context_t* ctx, term_t t) {
  bool value;

  return mcsat_branch_bool_term_value(ctx, t, &value) && value;
}

bool mcsat_branch_bool_term_is_false(const plugin_context_t* ctx, term_t t) {
  bool value;

  return mcsat_branch_bool_term_value(ctx, t, &value) && !value;
}

bool mcsat_branch_type_is_equality_sensitive(plugin_context_t* ctx, type_t tau) {
  return ctx->type_is_equality_sensitive == NULL ||
    ctx->type_is_equality_sensitive(ctx, tau);
}

bool mcsat_branch_equality_sensitivity_is_frozen(plugin_context_t* ctx) {
  return ctx->equality_sensitivity_is_frozen == NULL ||
    ctx->equality_sensitivity_is_frozen(ctx);
}
