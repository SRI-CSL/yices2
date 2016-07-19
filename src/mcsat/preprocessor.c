/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "mcsat/preprocessor.h"
#include "mcsat/tracing.h"

#include "terms/term_explorer.h"

#include "context/context_types.h"

void preprocessor_construct(preprocessor_t* pre, term_table_t* terms, jmp_buf* handler) {
  pre->terms = terms;
  init_term_manager(&pre->tm, terms);
  init_int_hmap(&pre->preprocess_map, 0);
  init_int_hmap(&pre->purification_map, 0);
  pre->tracer = NULL;
  pre->exception = handler;
}

void preprocessor_set_tracer(preprocessor_t* pre, tracer_t* tracer) {
  pre->tracer = tracer;
}

void preprocessor_destruct(preprocessor_t* pre) {
  delete_int_hmap(&pre->purification_map);
  delete_int_hmap(&pre->preprocess_map);
  delete_term_manager(&pre->tm);
}

static
term_t preprocessor_get(preprocessor_t* pre, term_t t) {
  int_hmap_pair_t* find = int_hmap_find(&pre->preprocess_map, t);
  if (find == NULL) {
    return NULL_TERM;
  } else {
    return find->val;
  }
}

static
void preprocessor_set(preprocessor_t* pre, term_t t, term_t t_pre) {
  assert(preprocessor_get(pre, t) == NULL_TERM);
  int_hmap_add(&pre->preprocess_map, t, t_pre);
}

static
composite_term_t* get_composite(term_table_t* terms, term_kind_t kind, term_t t) {
  assert(term_is_composite(terms, t));
  assert(term_kind(terms, t) == kind);
  assert(is_pos_term(t));

  switch (kind) {
  case ITE_TERM:           // if-then-else
  case ITE_SPECIAL:        // special if-then-else term (NEW: EXPERIMENTAL)
    return ite_term_desc(terms, t);
  case EQ_TERM:            // equality
    return eq_term_desc(terms, t);
  case OR_TERM:            // n-ary OR
    return or_term_desc(terms, t);
  case XOR_TERM:           // n-ary XOR
    return xor_term_desc(terms, t);
  case ARITH_BINEQ_ATOM:   // equality: (t1 == t2)  (between two arithmetic terms)
    return arith_bineq_atom_desc(terms, t);
  case APP_TERM:           // application of an uninterpreted function
    return app_term_desc(terms, t);
  case ARITH_RDIV:          // division: (/ x y)
    return arith_rdiv_term_desc(terms, t);
  case ARITH_IDIV:          // division: (div x y) as defined in SMT-LIB 2
    return arith_idiv_term_desc(terms, t);
  case ARITH_MOD:          // remainder: (mod x y) is y - x * (div x y)
    return arith_mod_term_desc(terms, t);
  case DISTINCT_TERM:
    return distinct_term_desc(terms, t);
  default:
    assert(false);
    return NULL;
  }
}

static
term_t mk_composite(preprocessor_t* pre, term_kind_t kind, uint32_t n, term_t* children) {
  term_manager_t* tm = &pre->tm;
  term_table_t* terms = pre->terms;

  switch (kind) {
  case ITE_TERM:           // if-then-else
  case ITE_SPECIAL:        // special if-then-else term (NEW: EXPERIMENTAL)
  {
    assert(n == 3);
    term_t type = super_type(pre->terms->types, term_type(terms, children[1]), term_type(terms, children[1]));
    return mk_ite(tm, children[0], children[1], children[2], type);
  }
  case EQ_TERM:            // equality
    assert(n == 2);
    return mk_eq(tm, children[0], children[1]);
  case OR_TERM:            // n-ary OR
    assert(n > 1);
    return mk_or(tm, n, children);
  case XOR_TERM:           // n-ary XOR
    return mk_xor(tm, n, children);
  case ARITH_BINEQ_ATOM:   // equality: (t1 == t2)  (between two arithmetic terms)
    assert(n == 2);
    return mk_arith_eq(tm, children[0], children[1]);
  case APP_TERM:           // application of an uninterpreted function
    assert(n > 1);
    return mk_application(tm, children[0], n-1, children + 1);
  case ARITH_RDIV:
    assert(n == 2);
    return mk_arith_rdiv(tm, children[0], children[1]);
  case ARITH_IDIV:          // division: (div x y) as defined in SMT-LIB 2
    assert(n == 2);
    return mk_arith_idiv(tm, children[0], children[1]);
  case ARITH_MOD:          // remainder: (mod x y) is y - x * (div x y)
    assert(n == 2);
    return mk_arith_mod(tm, children[0], children[1]);
  default:
    assert(false);
    return NULL_TERM;
  }
}

/**
 * Returns true if we should purify t as an argument of a function.
 * Any new equalities are added to output.
 */
static inline
term_t preprocessor_purify(preprocessor_t* pre, term_t t, ivector_t* out) {
  term_table_t* terms = pre->terms;
  // We don't purify variables
  term_kind_t t_kind = term_kind(terms, t);
  switch (t_kind) {
  case UNINTERPRETED_TERM:
    // Variables are already pure
    return t;
  case APP_TERM:
    // Uninterpreted functions are also already purified
    return t;
  default:
    break;
  }

  // Everything else gets purified. Check if in the cache
  int_hmap_pair_t* find = int_hmap_find(&pre->purification_map, t);
  if (find != NULL) {
    return find->val;
  } else {
    // Make the variable
    type_t t_type = term_type(terms, t);
    term_t x = new_uninterpreted_term(terms, t_type);
    // Remember for later
    int_hmap_add(&pre->purification_map, t, x);
    // Add equality to output
    term_t eq = mk_eq(&pre->tm, x, t);
    ivector_push(out, eq);

    if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
      trace_printf(pre->tracer, "adding lemma = ");
      trace_term_ln(pre->tracer, terms, eq);
    }

    // Return the purified version
    return x;
  }
}

term_t preprocessor_apply(preprocessor_t* pre, term_t t, ivector_t* out) {

  term_table_t* terms = pre->terms;
  term_manager_t* tm = &pre->tm;

  uint32_t i, j, n;

  // Check if already preprocessed;
  term_t t_pre = preprocessor_get(pre, t);
  if (t_pre != NULL_TERM) {
    return t_pre;
  }

  // Start
  ivector_t pre_stack;
  init_ivector(&pre_stack, 0);
  ivector_push(&pre_stack, t);

  // Preprocess
  while (pre_stack.size) {
    // Current term
    term_t current = ivector_last(&pre_stack);

    if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
      trace_printf(pre->tracer, "current = ");
      trace_term_ln(pre->tracer, terms, current);
    }

    // If preprocessed already, done
    term_t current_pre = preprocessor_get(pre, current);
    if (current_pre != NULL_TERM) {
      ivector_pop(&pre_stack);
      continue;
    }

    // Negation
    if (is_neg_term(current)) {
      term_t child = unsigned_term(current);
      term_t child_pre = preprocessor_get(pre, child);
      if (child_pre == NULL_TERM) {
        ivector_push(&pre_stack, child);
        continue;
      } else {
        ivector_pop(&pre_stack);
        current_pre = opposite_term(child_pre);
        preprocessor_set(pre, current, current_pre);
        continue;
      }
    }

    // Check for supported types
    type_kind_t type = term_type_kind(terms, current);
    switch (type) {
    case BOOL_TYPE:
    case INT_TYPE:
    case REAL_TYPE:
    case UNINTERPRETED_TYPE:
    case FUNCTION_TYPE:
      break;
    default:
      longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
    }

    // Kind of term
    term_kind_t current_kind = term_kind(terms, current);

    switch(current_kind) {
    case CONSTANT_TERM:    // constant of uninterpreted/scalar/boolean types
    case ARITH_CONSTANT:   // rational constant
    case UNINTERPRETED_TERM:  // (i.e., global variables, can't be bound).
      current_pre = current;
      break;

    case ARITH_EQ_ATOM:      // atom t == 0
    {
      term_t child = arith_eq_arg(terms, current);
      term_t child_pre = preprocessor_get(pre, child);
      if (child_pre != NULL_TERM) {
        current_pre = arith_eq_atom(terms, child_pre);
      } else {
        ivector_push(&pre_stack, child);
      }
      break;
    }

    case ARITH_GE_ATOM:      // atom t >= 0
    {
      term_t child = arith_ge_arg(terms, current);
      term_t child_pre = preprocessor_get(pre, child);
      if (child_pre != NULL_TERM) {
        current_pre = arith_geq_atom(terms, child_pre);
      } else {
        ivector_push(&pre_stack, child);
      }
      break;
    }

    case ITE_TERM:           // if-then-else
    case ITE_SPECIAL:        // special if-then-else term (NEW: EXPERIMENTAL)
    case EQ_TERM:            // equality
    case OR_TERM:            // n-ary OR
    case XOR_TERM:           // n-ary XOR
    case ARITH_BINEQ_ATOM:   // equality: (t1 == t2)  (between two arithmetic terms)
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);
      bool children_done = true;
      bool children_same = true;

      n = desc->arity;

      // Arrays not supported yet
      if (current_kind == EQ_TERM && term_type_kind(terms, desc->arg[0]) == FUNCTION_TYPE) {
        longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      }

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t child = desc->arg[i];
        term_t child_pre = preprocessor_get(pre, child);

        if (child_pre == NULL_TERM) {
          children_done = false;
          ivector_push(&pre_stack, child);
        } else if (child_pre != child) {
          children_same = false;
        }

        if (children_done) { ivector_push(&children, child_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          current_pre = mk_composite(pre, current_kind, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }


    case POWER_PRODUCT:    // power products: (t1^d1 * ... * t_n^d_n)
    {
      pprod_t* pp = pprod_term_desc(terms, current);
      bool children_done = true;
      bool children_same = true;

      n = pp->len;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t x = pp->prod[i].var;
        term_t x_pre = preprocessor_get(pre, x);

        if (x_pre == NULL_TERM) {
          children_done = false;
          ivector_push(&pre_stack, x);
        } else if (x_pre != x) {
          children_same = false;
        }

        if (children_done) { ivector_push(&children, x_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          // NOTE: it doens't change pp, it just uses it as a frame
          current_pre = mk_arith_pprod(tm, pp, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    case ARITH_POLY:       // polynomial with rational coefficients
    {
      polynomial_t* p = poly_term_desc(terms, current);

      bool children_done = true;
      bool children_same = true;

      n = p->nterms;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t x = p->mono[i].var;
        term_t x_pre = (x == const_idx ? const_idx : preprocessor_get(pre, x));

        if (x_pre != const_idx) {
          if (x_pre == NULL_TERM) {
            children_done = false;
            ivector_push(&pre_stack, x);
          } else if (x_pre != x) {
            children_same = false;
          }
        }

        if (children_done) { ivector_push(&children, x_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          current_pre = mk_arith_poly(tm, p, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    // FOLLOWING ARE UNINTEPRETED, SO WE PURIFY THE ARGUMENTS

    case APP_TERM:           // application of an uninterpreted function
    case ARITH_RDIV:         // regular division (/ x y)
    case ARITH_IDIV:         // division: (div x y) as defined in SMT-LIB 2
    case ARITH_MOD:          // remainder: (mod x y) is y - x * (div x y)
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);
      bool children_done = true;
      bool children_same = true;

      n = desc->arity;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t child = desc->arg[i];
        term_t child_pre = preprocessor_get(pre, child);

        if (child_pre == NULL_TERM) {
          children_done = false;
          ivector_push(&pre_stack, child);
        } else {
          // Purify if needed
          child_pre = preprocessor_purify(pre, child_pre, out);
          // If interpreted terms, we need to purify non-variables
          if (child_pre != child) { children_same = false; }
        }

        if (children_done) { ivector_push(&children, child_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          current_pre = mk_composite(pre, current_kind, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    case ARITH_FLOOR:        // floor: purify, but its interpreted
    {
      term_t child = arith_floor_arg(terms, current);
      term_t child_pre = preprocessor_get(pre, child);

      if (child_pre != NULL_TERM) {
        child_pre = preprocessor_purify(pre, child_pre, out);
        if (child_pre != child) {
          current_pre = arith_floor(terms, child_pre);
        } else {
          current_pre = current;
        }
      } else {
        ivector_push(&pre_stack, child);
      }

      break;
    }

    case ARITH_CEIL:        // floor: purify, but its interpreted
    {
      term_t child = arith_ceil_arg(terms, current);
      term_t child_pre = preprocessor_get(pre, child);

      if (child_pre != NULL_TERM) {
        child_pre = preprocessor_purify(pre, child_pre, out);
        if (child_pre != child) {
          current_pre = arith_floor(terms, child_pre);
        } else {
          current_pre = current;
        }
      } else {
        ivector_push(&pre_stack, child);
      }

      break;
    }

    case DISTINCT_TERM:
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);
      bool children_done = true;

      n = desc->arity;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t child = desc->arg[i];
        term_t child_pre = preprocessor_get(pre, child);

        if (child_pre == NULL_TERM) {
          children_done = false;
          ivector_push(&pre_stack, child);
        }

        if (children_done) { ivector_push(&children, child_pre); }
      }

      if (children_done) {
        ivector_t distinct;
        init_ivector(&distinct, 0);

        for (i = 0; i < n; ++ i) {
          for (j = i + 1; j < n; ++ j) {
            term_t neq = mk_eq(&pre->tm, children.data[i], children.data[j]);
            neq = opposite_term(neq);
            ivector_push(&distinct, neq);
          }
        }
        current_pre = mk_and(&pre->tm, distinct.size, distinct.data);

        delete_ivector(&distinct);
      }

      delete_ivector(&children);

      break;
    }


      break;

    default:
      // UNSUPPORTED TERM/THEORY
      longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      break;
    }

    if (current_pre != NULL_TERM) {
      preprocessor_set(pre, current, current_pre);
      ivector_pop(&pre_stack);
      if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
        trace_printf(pre->tracer, "current_pre = ");
        trace_term_ln(pre->tracer, terms, current_pre);
      }
    }

  }

  // Return the result
  t_pre = preprocessor_get(pre, t);
  if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
    trace_printf(pre->tracer, "t_pre = ");
    trace_term_ln(pre->tracer, terms, t_pre);
  }

  delete_ivector(&pre_stack);

  assert(t_pre != NULL_TERM);
  return t_pre;
}

void preprocessor_set_exception_handler(preprocessor_t* pre, jmp_buf* handler) {
  pre->exception = handler;
}
