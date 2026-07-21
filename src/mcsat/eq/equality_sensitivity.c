/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "mcsat/eq/equality_sensitivity.h"

#include "terms/term_explorer.h"

#include "utils/memalloc.h"

void equality_sensitivity_construct(equality_sensitivity_t* eqsens,
                                    type_table_t* types,
                                    term_table_t* terms) {
  eqsens->types = types;
  eqsens->terms = terms;
  init_ivector(&eqsens->obligation_roots, 0);
  init_ivector(&eqsens->assumption_roots, 0);
  init_int_hset(&eqsens->types_sensitive, 0);
  init_ivector(&eqsens->type_worklist, 0);
  init_ivector(&eqsens->term_worklist, 0);
  init_int_hset(&eqsens->scanned_terms, 0);
  init_ivector(&eqsens->term_children, 0);
  eqsens->generation = 0;
  eqsens->frozen = false;
  eqsens->dirty = false;
  eqsens->record_registration_roots = true;
  eqsens->registration_roots_are_assumptions = false;
}

void equality_sensitivity_destruct(equality_sensitivity_t* eqsens) {
  delete_ivector(&eqsens->obligation_roots);
  delete_ivector(&eqsens->assumption_roots);
  delete_int_hset(&eqsens->types_sensitive);
  delete_ivector(&eqsens->type_worklist);
  delete_ivector(&eqsens->term_worklist);
  delete_int_hset(&eqsens->scanned_terms);
  delete_ivector(&eqsens->term_children);
}

static void equality_sensitivity_note_dirty(equality_sensitivity_t* eqsens) {
  if (!eqsens->dirty) {
    eqsens->dirty = true;
    eqsens->generation ++;
  }
}

static bool equality_sensitivity_add_type(equality_sensitivity_t* eqsens, type_t tau) {
  if (tau == NULL_TYPE) {
    return false;
  }

  tau = max_super_type(eqsens->types, tau);
  if (int_hset_add(&eqsens->types_sensitive, tau)) {
    ivector_push(&eqsens->type_worklist, tau);
    return true;
  }
  return false;
}

static void equality_sensitivity_add_function_dependencies(equality_sensitivity_t* eqsens,
                                                           type_t tau) {
  type_table_t* types = eqsens->types;
  uint32_t i, n;

  assert(type_kind(types, tau) == FUNCTION_TYPE);

  n = function_type_arity(types, tau);
  for (i = 0; i < n; ++ i) {
    equality_sensitivity_add_type(eqsens, function_type_domain(types, tau, i));
  }
  equality_sensitivity_add_type(eqsens, function_type_range(types, tau));
}

static void equality_sensitivity_close_type_worklist(equality_sensitivity_t* eqsens) {
  type_table_t* types = eqsens->types;

  while (eqsens->type_worklist.size > 0) {
    type_t tau = ivector_pop2(&eqsens->type_worklist);

    switch (type_kind(types, tau)) {
    case TUPLE_TYPE: {
      uint32_t i, n;
      n = tuple_type_arity(types, tau);
      for (i = 0; i < n; ++ i) {
        equality_sensitivity_add_type(eqsens, tuple_type_component(types, tau, i));
      }
      break;
    }

    case FUNCTION_TYPE:
      equality_sensitivity_add_function_dependencies(eqsens, tau);
      break;

    default:
      break;
    }
  }
}

static void equality_sensitivity_push_child(equality_sensitivity_t* eqsens,
                                            term_t child) {
  if (child == NULL_TERM) {
    return;
  }

  child = unsigned_term(child);
  if (child != true_term && child != false_term) {
    assert(good_term(eqsens->terms, child));
    ivector_push(&eqsens->term_worklist, child);
  }
}

static void equality_sensitivity_push_term_children(equality_sensitivity_t* eqsens,
                                                    term_t t) {
  term_table_t* terms = eqsens->terms;
  uint32_t i, n;

  if (term_is_composite(terms, t)) {
    ivector_reset(&eqsens->term_children);
    get_term_children(terms, t, &eqsens->term_children);
    n = eqsens->term_children.size;
    for (i = 0; i < n; ++ i) {
      equality_sensitivity_push_child(eqsens, eqsens->term_children.data[i]);
    }
  } else if (term_is_projection(terms, t)) {
    equality_sensitivity_push_child(eqsens, proj_term_arg(terms, t));
  } else if (term_is_sum(terms, t)) {
    term_t child;
    mpq_t q;

    mpq_init(q);
    n = term_num_children(terms, t);
    for (i = 0; i < n; ++ i) {
      sum_term_component(terms, t, i, q, &child);
      equality_sensitivity_push_child(eqsens, child);
    }
    mpq_clear(q);
  } else if (term_is_bvsum(terms, t)) {
    term_t child;
    int32_t* coeff;

    coeff = safe_malloc(term_bitsize(terms, t) * sizeof(int32_t));
    n = term_num_children(terms, t);
    for (i = 0; i < n; ++ i) {
      bvsum_term_component(terms, t, i, coeff, &child);
      equality_sensitivity_push_child(eqsens, child);
    }
    safe_free(coeff);
  } else if (term_kind(terms, t) == ARITH_FF_POLY) {
    polynomial_t* p;

    p = finitefield_poly_term_desc(terms, t);
    n = p->nterms;
    for (i = 0; i < n; ++ i) {
      equality_sensitivity_push_child(eqsens, p->mono[i].var == const_idx ? NULL_TERM : p->mono[i].var);
    }
  } else if (term_is_product(terms, t)) {
    term_t child;
    uint32_t exp;

    n = term_num_children(terms, t);
    for (i = 0; i < n; ++ i) {
      product_term_component(terms, t, i, &child, &exp);
      equality_sensitivity_push_child(eqsens, child);
    }
  }
}

static void equality_sensitivity_scan_term(equality_sensitivity_t* eqsens,
                                           term_t root) {
  term_table_t* terms = eqsens->terms;

  if (root == NULL_TERM) {
    return;
  }

  root = unsigned_term(root);
  if (root == true_term || root == false_term) {
    return;
  }

  ivector_push(&eqsens->term_worklist, root);
  while (eqsens->term_worklist.size > 0) {
    term_t t = unsigned_term(ivector_pop2(&eqsens->term_worklist));
    term_kind_t kind;
    type_t tau;

    if (t == true_term || t == false_term ||
        !int_hset_add(&eqsens->scanned_terms, t)) {
      continue;
    }

    kind = term_kind(terms, t);
    tau = term_type(terms, t);

    if (type_kind(eqsens->types, tau) == FUNCTION_TYPE) {
      equality_sensitivity_add_function_dependencies(eqsens, tau);
    }

    if (term_constructor(terms, t) == YICES_EQ_TERM && term_num_children(terms, t) > 0) {
      equality_sensitivity_add_type(eqsens, term_type(terms, term_child(terms, t, 0)));
    } else if (kind == DISTINCT_TERM) {
      if (term_num_children(terms, t) > 0) {
        equality_sensitivity_add_type(eqsens, term_type(terms, term_child(terms, t, 0)));
      }
    }

    equality_sensitivity_push_term_children(eqsens, t);
    equality_sensitivity_close_type_worklist(eqsens);
  }
}

static void equality_sensitivity_recompute(equality_sensitivity_t* eqsens) {
  uint32_t i;

  int_hset_reset(&eqsens->types_sensitive);
  int_hset_reset(&eqsens->scanned_terms);
  ivector_reset(&eqsens->type_worklist);
  ivector_reset(&eqsens->term_worklist);
  ivector_reset(&eqsens->term_children);

  for (i = 0; i < eqsens->obligation_roots.size; ++ i) {
    equality_sensitivity_scan_term(eqsens, eqsens->obligation_roots.data[i]);
  }
  for (i = 0; i < eqsens->assumption_roots.size; ++ i) {
    equality_sensitivity_scan_term(eqsens, eqsens->assumption_roots.data[i]);
  }
  equality_sensitivity_close_type_worklist(eqsens);
}

bool equality_sensitivity_type_is_sensitive(equality_sensitivity_t* eqsens,
                                            type_t tau) {
  if (tau == NULL_TYPE) {
    return false;
  }
  tau = max_super_type(eqsens->types, tau);
  return int_hset_member(&eqsens->types_sensitive, tau);
}

#ifndef NDEBUG
void equality_sensitivity_assert_generated_equality_is_sensitive(equality_sensitivity_t* eqsens,
                                                                 term_t t) {
  term_table_t* terms;
  term_kind_t kind;
  type_t tau;
  uint32_t i;

  if (!eqsens->frozen) {
    return;
  }

  t = unsigned_term(t);
  if (t == true_term || t == false_term) {
    return;
  }

  terms = eqsens->terms;
  kind = term_kind(terms, t);
  switch (kind) {
  case EQ_TERM: {
    composite_term_t* eq = eq_term_desc(terms, t);
    tau = super_type(eqsens->types, term_type(terms, eq->arg[0]), term_type(terms, eq->arg[1]));
    assert(tau != NULL_TYPE);
    assert(equality_sensitivity_type_is_sensitive(eqsens, tau) &&
           "post-freeze generated equality on non-sensitive type");
    break;
  }

  case DISTINCT_TERM: {
    composite_term_t* distinct = distinct_term_desc(terms, t);
    for (i = 0; i < distinct->arity; ++ i) {
      tau = term_type(terms, distinct->arg[i]);
      assert(equality_sensitivity_type_is_sensitive(eqsens, tau) &&
             "post-freeze generated distinct on non-sensitive type");
    }
    break;
  }

  default:
    break;
  }
}
#endif

void equality_sensitivity_note_obligation_root(equality_sensitivity_t* eqsens,
                                               term_t t) {
  if (t == NULL_TERM) {
    return;
  }

  t = unsigned_term(t);
  if (t == true_term || t == false_term) {
    return;
  }

  ivector_push(&eqsens->obligation_roots, t);
  equality_sensitivity_note_dirty(eqsens);
}

void equality_sensitivity_note_assumption_root(equality_sensitivity_t* eqsens,
                                               term_t t) {
  if (t == NULL_TERM) {
    return;
  }

  t = unsigned_term(t);
  if (t == true_term || t == false_term) {
    return;
  }

  ivector_push(&eqsens->assumption_roots, t);
  equality_sensitivity_note_dirty(eqsens);
}

void equality_sensitivity_note_registered_term(equality_sensitivity_t* eqsens,
                                               term_t t) {
  if (eqsens->record_registration_roots) {
    if (eqsens->frozen) {
      /*
       * The pre-search freeze is the boundary for assertion/assumption roots.
       * Terms generated during search are internal obligations; they may be
       * registered with plugins, but they must not enlarge the root set for
       * the already-frozen equality-sensitivity generation.
       */
      return;
    }
    if (eqsens->registration_roots_are_assumptions) {
      equality_sensitivity_note_assumption_root(eqsens, t);
    } else {
      equality_sensitivity_note_obligation_root(eqsens, t);
    }
  }
}

uint32_t equality_sensitivity_obligation_root_count(const equality_sensitivity_t* eqsens) {
  return eqsens->obligation_roots.size;
}

term_t equality_sensitivity_obligation_root(const equality_sensitivity_t* eqsens,
                                            uint32_t i) {
  assert(i < eqsens->obligation_roots.size);
  return eqsens->obligation_roots.data[i];
}

uint32_t equality_sensitivity_assumption_root_count(const equality_sensitivity_t* eqsens) {
  return eqsens->assumption_roots.size;
}

term_t equality_sensitivity_assumption_root(const equality_sensitivity_t* eqsens,
                                            uint32_t i) {
  assert(i < eqsens->assumption_roots.size);
  return eqsens->assumption_roots.data[i];
}

void equality_sensitivity_restore_obligation_roots(equality_sensitivity_t* eqsens,
                                                   uint32_t n) {
  assert(n <= eqsens->obligation_roots.size);
  ivector_shrink(&eqsens->obligation_roots, n);
  equality_sensitivity_note_dirty(eqsens);
  equality_sensitivity_unfreeze(eqsens);
}

void equality_sensitivity_clear_assumption_roots(equality_sensitivity_t* eqsens) {
  if (eqsens->assumption_roots.size > 0) {
    ivector_reset(&eqsens->assumption_roots);
    equality_sensitivity_note_dirty(eqsens);
  }
}

void equality_sensitivity_unfreeze(equality_sensitivity_t* eqsens) {
  eqsens->frozen = false;
}

void equality_sensitivity_freeze(equality_sensitivity_t* eqsens) {
  equality_sensitivity_recompute(eqsens);
  eqsens->frozen = true;
  eqsens->dirty = false;
}

uint32_t equality_sensitivity_generation(const equality_sensitivity_t* eqsens) {
  return eqsens->generation;
}

bool equality_sensitivity_is_frozen(const equality_sensitivity_t* eqsens) {
  return eqsens->frozen;
}

bool equality_sensitivity_set_registration_roots_are_assumptions(equality_sensitivity_t* eqsens,
                                                                 bool value) {
  bool old;

  old = eqsens->registration_roots_are_assumptions;
  eqsens->registration_roots_are_assumptions = value;
  return old;
}

bool equality_sensitivity_set_record_registration_roots(equality_sensitivity_t* eqsens,
                                                        bool value) {
  bool old;

  old = eqsens->record_registration_roots;
  eqsens->record_registration_roots = value;
  return old;
}
