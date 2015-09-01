/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef MCSAT_LITERAL_H_
#define MCSAT_LITERAL_H_

#include "mcsat/mcsat_types.h"
#include "mcsat/bool/bool_plugin_types.h"

#include "mcsat/variable_db.h"
#include "mcsat/trail.h"
#include "mcsat/value.h"
#include "mcsat/plugin.h"

#define mcsat_literal_null 0

/** Negate the literal */
static inline
mcsat_literal_t literal_negate(mcsat_literal_t l) {
  return -l;
}

/** Is the literal negated */
static inline
bool literal_is_negated(mcsat_literal_t l) {
  return l < 0;
}

/** Return the literal variable */
static inline
variable_t literal_get_variable(mcsat_literal_t l) {
  return l > 0 ? l : -l;
}

/** Return the literal variable */
static inline
variable_t literal_get_variable_from_index(uint32_t l_index) {
  return l_index >> 1;
}

/** Create a literal */
static inline
mcsat_literal_t literal_construct(variable_t var, bool negated) {
  return negated ? -var : var;
}

/** Return the index of the literal: (var | negated) */
static inline
uint32_t literal_index(mcsat_literal_t l) {
  return (literal_get_variable(l) << 1) | literal_is_negated(l);
}

/** Returns the maximal index a literal with the given variable can have */
static inline
uint32_t linter_index_max(variable_t var) {
  return (var << 1) | 1;
}

/** Return true if the literal has a value in the trail */
static inline
bool literal_has_value(mcsat_literal_t l, const mcsat_trail_t* trail) {
  return trail_has_value(trail, literal_get_variable(l));
}

/** Create a literal that that is true in the trail */
static inline
mcsat_literal_t literal_construct_from_trail(variable_t x, const mcsat_trail_t* trail) {
  assert(trail_has_value(trail, x));
  return literal_construct(x, !trail_get_value(trail, x)->b);
}

/** Return tre level of the literal (must have value != NONE) */
static inline
uint32_t literal_get_level(mcsat_literal_t l, const mcsat_trail_t* trail) {
  assert(trail_has_value(trail, literal_get_variable(l)));
  return trail_get_level(trail, literal_get_variable(l));
}

/** Return true if the literal has a value in the trail at base level */
static inline
bool literal_has_value_at_base(mcsat_literal_t l, const mcsat_trail_t* trail) {
  return trail_has_value_at_base(trail, literal_get_variable(l));
}

/** Return the value of the literal (must have value != NONE) */
static inline
bool literal_get_value(mcsat_literal_t l, const mcsat_trail_t* trail) {
  variable_t l_var;
  bool l_var_value;

  l_var = literal_get_variable(l);
  assert(trail_has_value(trail, l_var));
  l_var_value = trail_get_value(trail, l_var)->b;
  if (literal_is_negated(l)) {
    return !l_var_value;
  } else {
    return l_var_value;
  }
}

/** Return true if the literal is assigned to false */
static inline
bool literal_is_false(mcsat_literal_t l, const mcsat_trail_t* trail) {
  return literal_has_value(l, trail) && !literal_get_value(l, trail);
}

/** Return true if the literal is assigned to true */
static inline
bool literal_is_true(mcsat_literal_t l, const mcsat_trail_t* trail) {
  return literal_has_value(l, trail) && literal_get_value(l, trail);
}

/** Set the value of the literal */
static inline
void literal_set_value(mcsat_literal_t l, trail_token_t* token) {
  variable_t l_var;
  bool l_negated;

  l_var = literal_get_variable(l);
  l_negated = literal_is_negated(l);

  if (l_negated) {
    token->add(token, l_var, &mcsat_value_false);
  } else {
    token->add(token, l_var, &mcsat_value_true);
  }
}

#endif /* MCSAT_LITERAL_H_ */
