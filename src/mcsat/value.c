/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/value.h"

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/hash_functions.h"

const mcsat_value_t mcsat_value_none = { VALUE_NONE, { true } };
const mcsat_value_t mcsat_value_true = { VALUE_BOOLEAN, { true } };
const mcsat_value_t mcsat_value_false = { VALUE_BOOLEAN, { false } };

void mcsat_value_construct_default(mcsat_value_t* value) {
  value->type = VALUE_NONE;
}

void mcsat_value_construct_bool(mcsat_value_t* value, bool b) {
  value->type = VALUE_BOOLEAN;
  value->b = b;
}

void mcsat_value_construct_rational(mcsat_value_t* value, const rational_t* q) {
  value->type = VALUE_RATIONAL;
  q_init(&value->q);
  q_set(&value->q, q);
}

void mcsat_value_construct_lp_value(mcsat_value_t* value, const lp_value_t* lp_value) {
  value->type = VALUE_LIBPOLY;
  lp_value_construct_copy(&value->lp_value, lp_value);
}

void mcsat_value_construct_copy(mcsat_value_t* value, const mcsat_value_t* from) {
  value->type = from->type;
  switch (value->type) {
  case VALUE_NONE:
    break;
  case VALUE_BOOLEAN:
    value->b = from->b;
    break;
  case VALUE_RATIONAL:
    q_init(&value->q);
    q_set(&value->q, &from->q);
    break;
  case VALUE_LIBPOLY:
    lp_value_construct_copy(&value->lp_value, &from->lp_value);
    break;
  default:
    assert(false);
  }
}

void mcsat_value_destruct(mcsat_value_t* value) {
  switch (value->type) {
  case VALUE_NONE:
    break;
  case VALUE_BOOLEAN:
    break;
  case VALUE_RATIONAL:
    q_clear(&value->q);
    break;
  case VALUE_LIBPOLY:
    lp_value_destruct(&value->lp_value);
    break;
  default:
    assert(false);
  }
}

void mcsat_value_assign(mcsat_value_t* value, const mcsat_value_t* from) {
  if (value != from) {
    mcsat_value_destruct(value);
    mcsat_value_construct_copy(value, from);
  }
}

void mcsat_value_print(const mcsat_value_t* value, FILE* out) {
  switch (value->type) {
  case VALUE_NONE:
    fprintf(out, "<NONE>");
    break;
  case VALUE_BOOLEAN:
    if (value->b) {
      fprintf(out, "true");
    } else {
      fprintf(out, "false");
    }
    break;
  case VALUE_RATIONAL:
    q_print(out, (rational_t*) &value->q);
    break;
  case VALUE_LIBPOLY:
    lp_value_print(&value->lp_value, out);
    break;
  default:
    assert(false);
  }
}

bool mcsat_value_eq(const mcsat_value_t* v1, const mcsat_value_t* v2) {
  assert(v1->type == v2->type);
  switch (v1->type) {
  case VALUE_BOOLEAN:
    return v1->b == v2->b;
  case VALUE_RATIONAL:
    assert(v2->type == VALUE_RATIONAL);
    return q_cmp(&v1->q, &v2->q) == 0;
  case VALUE_LIBPOLY:
    return lp_value_cmp(&v1->lp_value, &v2->lp_value) == 0;
  default:
    assert(false);
    return false;
  }
}

uint32_t mcsat_value_hash(const mcsat_value_t* v) {
  switch (v->type) {
  case VALUE_BOOLEAN:
    return v->b;
  case VALUE_RATIONAL:
  {
    uint32_t num, den;
    q_hash_decompose(&v->q, &num, &den);
    return jenkins_hash_pair(num, den, 0xf9e34ab9);
  }
  case VALUE_LIBPOLY:
    return lp_value_hash(&v->lp_value);
  default:
    assert(false);
    return 0;
  }
}

value_t mcsat_value_to_value(mcsat_value_t* mcsat_value, type_table_t *types, type_t type, value_table_t* vtbl) {
  value_t value = null_value;
  switch (mcsat_value->type) {
  case VALUE_BOOLEAN:
    value = vtbl_mk_bool(vtbl, mcsat_value->b);
    break;
  case VALUE_RATIONAL:
    if (type_kind(types, type) == UNINTERPRETED_TYPE) {
      int32_t id;
      bool ok = q_get32(&mcsat_value->q, &id);
      (void) ok; // unused in release build
      assert(ok);
      value = vtbl_mk_const(vtbl, type, id, NULL);
    } else {
      value = vtbl_mk_rational(vtbl, &mcsat_value->q);
    }
    break;
  case VALUE_LIBPOLY:
    if (lp_value_is_rational(&mcsat_value->lp_value)) {
      lp_rational_t lp_q;
      lp_rational_construct(&lp_q);
      lp_value_get_rational(&mcsat_value->lp_value, &lp_q);
      rational_t q;
      q_init(&q);
      q_set_mpq(&q, &lp_q);
      value = vtbl_mk_rational(vtbl, &q);
      q_clear(&q);
      lp_rational_destruct(&lp_q);
    } else {
      value = vtbl_mk_algebraic(vtbl, &mcsat_value->lp_value.value.a);
    }
    break;
  default:
    assert(false);
  }
  return value;
}
