#include "substitution.h"

#include "mcsat/tracing.h"

#include <stdbool.h>

void substitution_construct(substitution_t* subst, term_manager_t* tm, tracer_t* tracer) {
  init_int_hmap(&subst->substitution_fwd, 0);
  init_int_hmap(&subst->substitution_bck, 0);
  subst->tm = tm;
  subst->tracer = tracer;
}

void substitution_destruct(substitution_t* subst) {
  delete_int_hmap(&subst->substitution_fwd);
  delete_int_hmap(&subst->substitution_bck);
}

/**
 * Construct a composite term.
 *
 * The main application of substitution is in the context of conflict
 * resolution. Once of the constraints there is to make sure that if we
 * substitute x -> t in a constraint C(x) this constraint doesn't shift
 * theories.
 *
 * Theory shifting example:
 * - x + ite(b1 or b2, bv1, bv0) > 0, with substitution x -> 0
 *   -> might result in just (b1 or b2): BV constraint -> Boolean constraint
 *
 */
static inline
term_t mk_composite(term_manager_t* tm, term_kind_t kind, uint32_t n, term_t* c) {

  term_t result = NULL_TERM;

  switch (kind) {
  case EQ_TERM:            // equality
    assert(n == 2);
    result = mk_eq(tm, c[0], c[1]);
    break;
  case OR_TERM:            // n-ary OR
    assert(n > 1);
    result = mk_or(tm, n, c);
    break;
  case XOR_TERM:           // n-ary XOR
    result = mk_xor(tm, n, c);
    break;
  case BV_ARRAY:
    assert(n >= 1);
    result = mk_bvarray(tm, n, c);
    break;
  case BV_DIV:
    assert(n == 2);
    result = mk_bvdiv(tm, c[0], c[1]);
    break;
  case BV_REM:
    assert(n == 2);
    result = mk_bvrem(tm, c[0], c[1]);
    break;
  case BV_SDIV:
    assert(n == 2);
    result = mk_bvsdiv(tm, c[0], c[1]);
    break;
  case BV_SREM:
    assert(n == 2);
    result = mk_bvsrem(tm, c[0], c[1]);
    break;
  case BV_SMOD:
    assert(n == 2);
    result = mk_bvsmod(tm, c[0], c[1]);
    break;
  case BV_SHL:
    assert(n == 2);
    result = mk_bvshl(tm, c[0], c[1]);
    break;
  case BV_LSHR:
    assert(n == 2);
    result = mk_bvlshr(tm, c[0], c[1]);
    break;
  case BV_ASHR:
    assert(n == 2);
    result = mk_bvashr(tm, c[0], c[1]);
    break;
  case BV_EQ_ATOM:
    assert(n == 2);
    result = mk_bveq(tm, c[0], c[1]);
    break;
  case BV_GE_ATOM:
    assert(n == 2);
    result = mk_bvge(tm, c[0], c[1]);
    break;
  case BV_SGE_ATOM:
    assert(n == 2);
    result = mk_bvsge(tm, c[0], c[1]);
    break;
  case ITE_TERM: {
    assert(n == 3);
    type_t tau = term_type(tm->terms, c[1]);
    result = mk_ite(tm, c[0], c[1], c[2], tau);
  }
  break;
  default:
    assert(false);
  }

  return result;
}

static
term_t substitution_run_core(substitution_t* subst, term_t t, int_hmap_t* cache, const int_hmap_t* frontier) {

  uint32_t i, n;
  int_hmap_pair_t* find = NULL;

  // Term stuff
  term_manager_t* tm = subst->tm;
  term_table_t* terms = tm->terms;

  if (trace_enabled(subst->tracer, "mcsat::subst")) {
    FILE* out = trace_out(subst->tracer);
    fprintf(out, "substitution in:\n");
    trace_term_ln(subst->tracer, terms, t);
  }

  // Check if already done
  find = int_hmap_find(cache, t);
  if (find != NULL) {
    return find->val;
  }

  // Start
  ivector_t substitution_stack;
  init_ivector(&substitution_stack, 0);
  ivector_push(&substitution_stack, t);

  // Run the substitutions
  while (substitution_stack.size) {
    // Current term
    term_t current = ivector_last(&substitution_stack);

    if (trace_enabled(subst->tracer, "mcsat::subst")) {
      FILE* out = trace_out(subst->tracer);
      fprintf(out, "processing ");
      trace_term_ln(subst->tracer, terms, current);
    }

    // Check if done already
    find = int_hmap_find(cache, current);
    if (find != NULL) {
      ivector_pop(&substitution_stack);
      continue;
    }

    // Deal with negation
    if (is_neg_term(current)) {
      term_t child = unsigned_term(current);
      find = int_hmap_find(cache, child);
      if (find == NULL) {
        // Not yet done
        ivector_push(&substitution_stack, child);
        continue;
      } else {
        // Done, just set it
        ivector_pop(&substitution_stack);
        term_t current_subst = opposite_term(find->val);
        int_hmap_add(cache, current, current_subst);
        continue;
      }
    }

    // We go deeper only if the frontier is not blocked
    if (current != t && frontier != NULL) {
      find = int_hmap_find((int_hmap_t*) frontier, current);
      if (find != NULL) {
        // Keep this term as is
        int_hmap_add(cache, current, current);
        continue;
      }
    }

    // Current term kind
    term_kind_t current_kind = term_kind(terms, current);
    // The result substitution (will be NULL if not done yet)
    term_t current_subst = NULL_TERM;

    // Process each term kind
    switch(current_kind) {

    // Constants are noop
    case CONSTANT_TERM:    // constant of uninterpreted/scalar/boolean types
    case BV64_CONSTANT:    // compact bitvector constant (64 bits at most)
    case BV_CONSTANT:      // generic bitvector constant (more than 64 bits)
      current_subst = current;
      break;

    // If a variable hasn't been done already, it stays
    case UNINTERPRETED_TERM:  // variables not
      current_subst = current;
      break;

    // Composite terms
    case EQ_TERM:            // equality
    case ITE_TERM:
    case ITE_SPECIAL:
    case OR_TERM:            // n-ary OR
    case XOR_TERM:           // n-ary XOR
    case BV_ARRAY:
    case BV_DIV:
    case BV_REM:
    case BV_SDIV:
    case BV_SREM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
    {
      composite_term_t* desc = composite_term_desc(terms, current);
      n = desc->arity;

      bool children_done = true; // All children substituted
      bool children_same = true; // All children substitution same (no need to make new term)
      bool children_const = true; // All substitution children constant (compute)

      ivector_t children;
      init_ivector(&children, n);
      for (i = 0; i < n; ++ i) {
        term_t child = desc->arg[i];
        find = int_hmap_find(cache, child);
        if (find == NULL) {
          children_done = false;
          ivector_push(&substitution_stack, child);
        } else if (find->val != child) {
          children_same = false;
        }
        if (children_done) {
          ivector_push(&children, find->val);
          children_const = children_const && is_const_term(terms, find->val);
        }
      }

      // Make the substitution (or not if noop)
      if (children_done) {
        if (children_same) {
          current_subst = current;
        } else {
          current_subst = mk_composite(tm, current_kind, n, children.data);
          if (trace_enabled(subst->tracer, "mcsat::subst::check")) {
            FILE* out = trace_out(subst->tracer);
            // Check that the Boolean terms stay within the same plugin
            if (is_boolean_term(terms, current) && !is_constant_term(terms, current_subst)) {
              term_kind_t current_subst_kind = term_kind(terms, current_subst);
              if (current_kind != current_subst_kind) {
                fprintf(out, "kind change:\n");
                trace_term_ln(subst->tracer, terms, current);
                trace_term_ln(subst->tracer, terms, current_subst);
                assert(false);
              }
            }
            // Check that constant terms result in constant terms
            if (children_const && !is_constant_term(terms, current_subst)) {
              trace_term_ln(subst->tracer, terms, current_subst);
              assert(false);
            }

          }
        }
      }

      delete_ivector(&children);
      break;
    }

    case ARITH_GE_ATOM: {
      term_t arg = arith_ge_arg(terms, current);
      find = int_hmap_find(cache, arg);
      if (find == NULL) {
        ivector_push(&substitution_stack, arg);
      } else {
        if (find->val == arg) {
          current_subst = current;
        } else {
          current_subst = arith_geq_atom(terms, find->val);
        }
      }
      break;
    }

    case ARITH_EQ_ATOM: {
      term_t arg = arith_eq_arg(terms, current);
      find = int_hmap_find(cache, arg);
      if (find == NULL) {
        ivector_push(&substitution_stack, arg);
      } else {
        if (find->val == arg) {
          current_subst = current;
        } else {
          current_subst = arith_eq_atom(terms, find->val);
        }
      }
      break;
    }

    case ARITH_POLY:
    {
      polynomial_t* p = poly_term_desc(terms, current);
      n = p->nterms;

      bool children_done = true;
      bool children_same = true;

      ivector_t children;
      init_ivector(&children, n);
      for (i = 0; i < n; ++ i) {
        term_t x = p->mono[i].var;
        if (x != const_idx) {
          find = int_hmap_find(cache, x);
          if (find == NULL) {
            children_done = false;
            ivector_push(&substitution_stack, x);
          } else if (find->val != x) {
            children_same = false;
          }
          if (children_done) { ivector_push(&children, find->val); }
        } else {
          if (children_done) { ivector_push(&children, const_idx); }
        }
      }

      if (children_done) {
        if (children_same) {
          current_subst = current;
        } else {
          current_subst = mk_arith_poly(tm, p, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    case BIT_TERM: // bit-select current = child[i]
    {
      uint32_t index = bit_term_index(terms, current);
      term_t arg = bit_term_arg(terms, current);
      find = int_hmap_find(cache, arg);
      if (find == NULL) {
        ivector_push(&substitution_stack, arg);
      } else {
        if (find->val == arg) {
          current_subst = current;
        } else {
          current_subst = bit_term(terms, index, find->val);
        }
      }
      break;
    }

    case BV_POLY:  // polynomial with generic bitvector coefficients
    {
      bvpoly_t* p = bvpoly_term_desc(terms, current);
      n = p->nterms;

      bool children_done = true;
      bool children_same = true;

      ivector_t children;
      init_ivector(&children, n);
      for (i = 0; i < n; ++ i) {
        term_t x = p->mono[i].var;
        if (x != const_idx) {
          find = int_hmap_find(cache, x);
          if (find == NULL) {
            children_done = false;
            ivector_push(&substitution_stack, x);
          } else if (find->val != x) {
            children_same = false;
          }
          if (children_done) { ivector_push(&children, find->val); }
        } else {
          if (children_done) { ivector_push(&children, const_idx); }
        }
      }

      if (children_done) {
        if (children_same) {
          current_subst = current;
        } else {
          current_subst = mk_bvarith_poly(tm, p, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }
    case BV64_POLY: // polynomial with 64bit coefficients
    {
      bvpoly64_t* p = bvpoly64_term_desc(terms, current);
      n = p->nterms;

      bool children_done = true;
      bool children_same = true;

      ivector_t children;
      init_ivector(&children, n);
      for (i = 0; i < n; ++ i) {
        term_t x = p->mono[i].var;
        if (x != const_idx) {
          find = int_hmap_find(cache, x);
          if (find == NULL) {
            children_done = false;
            ivector_push(&substitution_stack, x);
          } else if (find->val != x) {
            children_same = false;
          }
          if (children_done) { ivector_push(&children, find->val); }
        } else {
          if (children_done) { ivector_push(&children, const_idx); }
        }
      }

      if (children_done) {
        if (children_same) {
          current_subst = current;
        } else {
          current_subst = mk_bvarith64_poly(tm, p, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    case POWER_PRODUCT:    // power products: (t1^d1 * ... * t_n^d_n)
    {
      pprod_t* pp = pprod_term_desc(terms, current);
      n = pp->len;

      bool children_done = true;
      bool children_same = true;

      ivector_t children;
      init_ivector(&children, n);
      for (i = 0; i < n; ++ i) {
        term_t x = pp->prod[i].var;
        find = int_hmap_find(cache, x);
        if (find == NULL) {
          children_done = false;
          ivector_push(&substitution_stack, x);
        } else if (find->val != x) {
          children_same = false;
        }
        if (children_done) { ivector_push(&children, find->val); }
      }

      if (children_done) {
        if (children_same) {
          current_subst = current;
        } else {
          // NOTE: it doens't change pp, it just uses it as a frame
          current_subst = mk_pprod(tm, pp, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    default:
      // UNSUPPORTED TERM/THEORY
      assert(false);
      break;
    }

    // If done with substitution, record and pop
    if (current_subst != NULL_TERM) {
      int_hmap_add(cache, current, current_subst);
      ivector_pop(&substitution_stack);
    }
  }

  // Return the result
  find = int_hmap_find(cache, t);
  assert(find != NULL);

  // Delete the stack
  delete_ivector(&substitution_stack);

  if (trace_enabled(subst->tracer, "mcsat::subst")) {
    FILE* out = trace_out(subst->tracer);
    fprintf(out, "substitution result:\n");
    trace_term_ln(subst->tracer, terms, t);
    trace_term_ln(subst->tracer, terms, find->val);
  }

  return find->val;
}

term_t substitution_run_fwd(substitution_t* subst, term_t t, const int_hmap_t* frontier) {
  // Run the substitution
  return substitution_run_core(subst, t, &subst->substitution_fwd, frontier);
}

term_t substitution_run_bck(substitution_t* subst, term_t t, const int_hmap_t* frontier) {
  // Run the substitution backwards
  return substitution_run_core(subst, t, &subst->substitution_bck, frontier);
}

bool substitution_has_term(const substitution_t* subst, term_t term) {
  return int_hmap_find((int_hmap_t*) &subst->substitution_fwd, term) != NULL;
}

void substitution_add(substitution_t* subst, term_t t, term_t t_subst) {

  if (trace_enabled(subst->tracer, "mcsat::subst")) {
    FILE* out = trace_out(subst->tracer);
    fprintf(out, "adding substition:\n");
    fprintf(out, "t = "); trace_term_ln(subst->tracer, subst->tm->terms, t);
    fprintf(out, "t_out = "); trace_term_ln(subst->tracer, subst->tm->terms, t_subst);
  }

  int_hmap_pair_t* find = int_hmap_get(&subst->substitution_fwd, t);
  assert(find->val == -1);
  find->val = t_subst;
  find = int_hmap_get(&subst->substitution_bck, t_subst);
  assert(find->val == -1);
  find->val = t;
}


