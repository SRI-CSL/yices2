/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/bool/cnf.h"

#include "mcsat/tracing.h"

void cnf_construct(cnf_t* cnf, plugin_context_t* ctx, clause_db_t* clause_db) {
  cnf->clause_db = clause_db;
  cnf->ctx = ctx;
  cnf->variable = variable_null;
  int_lset_construct(&cnf->converted);
}

void cnf_destruct(cnf_t* cnf) {
  int_lset_destruct(&cnf->converted);
}

static
bool cnf_is_converted(const cnf_t* cnf, variable_t var) {
  return int_lset_has_list(&cnf->converted, var);
}

static
void cnf_begin(cnf_t* cnf, variable_t var) {
  assert(!cnf_is_converted(cnf, var));
  cnf->variable = var;
}

static
void cnf_end(cnf_t* cnf) {
  cnf->variable = variable_null;
}

static
void cnf_remove(cnf_t* cnf, variable_t var) {
  int_lset_remove(&cnf->converted, var);
}

static
void cnf_add_clause(cnf_t* cnf, const mcsat_literal_t* lits, uint32_t lits_size, ivector_t* clauses_out, mcsat_clause_tag_t tag) {
  uint32_t i, keep;
  clause_ref_t clause_ref;
  mcsat_literal_t* lits_copy;

  lits_copy = NULL;

  if (ctx_trace_enabled(cnf->ctx, "bool::cnf")) {
    ctx_trace_printf(cnf->ctx, "cnf_add_clause:");
    literals_print(lits, lits_size, cnf->ctx->var_db, ctx_trace_out(cnf->ctx));
    ctx_trace_printf(cnf->ctx, "\n");
  }

  // Make a copy of the literals
  lits_copy = safe_malloc(sizeof(mcsat_literal_t) * lits_size);
  for (i = 0, keep = 0; i < lits_size; ++ i) {
    if (literal_has_value(lits[i], cnf->ctx->trail)) {
      if (literal_get_value(lits[i], cnf->ctx->trail)) {
        // true literal, true clause
        goto finish;
      } else {
        // false literal, just skip it
      }
    }
    lits_copy[keep ++] = lits[i];
  }
  lits_size = keep;

  if (ctx_trace_enabled(cnf->ctx, "bool::cnf")) {
    ctx_trace_printf(cnf->ctx, "cnf_add_clause: after simpl: ");
    literals_print(lits_copy, lits_size, cnf->ctx->var_db, ctx_trace_out(cnf->ctx));
    ctx_trace_printf(cnf->ctx, "\n");
  }

  // Add the clause
  clause_ref = clause_db_new_clause(cnf->clause_db, lits_copy, lits_size, tag);
  ivector_push(clauses_out, clause_ref);
  assert(clause_db_is_clause(cnf->clause_db, clause_ref, true));

  // If defining a variable, remember it
  assert(cnf->variable == variable_null || tag.type == CLAUSE_DEFINITION);
  if (cnf->variable != variable_null) {
    assert(tag.var == cnf->variable);
    int_lset_add(&cnf->converted, cnf->variable, clause_ref);
  }

finish:
  safe_free(lits_copy);
}

static
void cnf_convert_or(cnf_t* cnf, term_t or, ivector_t* or_clauses) {
  uint32_t i;
  composite_term_t* or_composite;
  mcsat_literal_t* or_literals;
  mcsat_clause_tag_t or_tag;

  assert(term_kind(cnf->ctx->terms, or) == OR_TERM);

  // Get the or description
  or_composite = composite_term_desc(cnf->ctx->terms, or);
  or_tag.type = CLAUSE_DEFINITION;
  or_tag.var = variable_db_get_variable(cnf->ctx->var_db, or);

  // Make some space
  or_literals = safe_malloc(sizeof(mcsat_literal_t) * (or_composite->arity + 1));

  or_literals[0] = literal_construct(or_tag.var, true);
  for (i = 0; i < or_composite->arity; ++ i) {
    or_literals[i + 1] = cnf_convert(cnf, or_composite->arg[i], or_clauses);
  }

  cnf_begin(cnf, or_tag.var);

  // a => (or t1 ... tn)
  // (or !a t1 ... tn)
  cnf_add_clause(cnf, or_literals, or_composite->arity + 1, or_clauses, or_tag);

  // a <= (or t1 ... tn)
  // (a or !t1) ... (a or !tn)
  or_literals[0] = literal_construct(or_tag.var, false);
  for (i = 0; i < or_composite->arity; ++ i) {
    or_literals[1] = literal_negate(or_literals[i + 1]);
    cnf_add_clause(cnf, or_literals, 2, or_clauses, or_tag);
  }

  cnf_end(cnf);

  // Free the children
  safe_free(or_literals);
}

static
void cnf_convert_xor(cnf_t* cnf, term_t xor, ivector_t* t_clauses) {
  // XORs should only be binary and rewritten to (not (= ))
  assert(false);
}

static
void cnf_convert_eq(cnf_t* cnf, term_t eq, ivector_t* eq_clauses) {
  composite_term_t* eq_composite;
  mcsat_literal_t eq_literals[3];
  mcsat_clause_tag_t eq_tag;
  mcsat_literal_t a, b;

  // Get the eq description
  assert(term_kind(cnf->ctx->terms, eq) == EQ_TERM);
  eq_composite = composite_term_desc(cnf->ctx->terms, eq);
  assert(eq_composite->arity == 2);

  eq_tag.type = CLAUSE_DEFINITION;
  eq_tag.var = variable_db_get_variable(cnf->ctx->var_db, eq);

  // Convert the children
  a = cnf_convert(cnf, eq_composite->arg[0], eq_clauses);
  b = cnf_convert(cnf, eq_composite->arg[1], eq_clauses);

  cnf_begin(cnf, eq_tag.var);

  // eq => (!a | b) & (a | !b)
  // (!eq | !a | b) & (!eq | a | !b)
  eq_literals[0] = literal_construct(eq_tag.var, true);

  eq_literals[1] = literal_negate(a);
  eq_literals[2] = b;
  cnf_add_clause(cnf, eq_literals, 3, eq_clauses, eq_tag);

  eq_literals[1] = a;
  eq_literals[2] = literal_negate(b);
  cnf_add_clause(cnf, eq_literals, 3, eq_clauses, eq_tag);

  // !eq => (a | b) & (!a | !b)
  // (eq | a | b) & (eq | !a | !b)
  eq_literals[0] = literal_construct(eq_tag.var, false);

  eq_literals[1] = a;
  eq_literals[2] = b;
  cnf_add_clause(cnf, eq_literals, 3, eq_clauses, eq_tag);

  eq_literals[1] = literal_negate(a);
  eq_literals[2] = literal_negate(b);
  cnf_add_clause(cnf, eq_literals, 3, eq_clauses, eq_tag);

  cnf_end(cnf);
}

static
void cnf_convert_ite(cnf_t* cnf, term_t ite, ivector_t* ite_clauses) {
  composite_term_t* ite_composite;
  mcsat_literal_t ite_literals[3];
  mcsat_clause_tag_t ite_tag;
  mcsat_literal_t cond, b_true, b_false;

  // Get the ite description
  assert(term_kind(cnf->ctx->terms, ite) == ITE_TERM);
  ite_composite = composite_term_desc(cnf->ctx->terms, ite);
  assert(ite_composite->arity == 3);

  ite_tag.type = CLAUSE_DEFINITION;
  ite_tag.var = variable_db_get_variable(cnf->ctx->var_db, ite);

  // Convert the children
  cond = cnf_convert(cnf, ite_composite->arg[0], ite_clauses);
  b_true= cnf_convert(cnf, ite_composite->arg[1], ite_clauses);
  b_false = cnf_convert(cnf, ite_composite->arg[2], ite_clauses);

  cnf_begin(cnf, ite_tag.var);

  // ite => (ite cond b_true b_false)
  // ite => (b_true | b_false) & (cond => b_true) & (!cond => b_false)
  // ite => (b_true | b_false) & (!cond | b_true) & (cond | b_false)
  // (!ite | b_true | b_false) & (!ite | !cond | b_true) & (!ite | cond | b_false)
  ite_literals[0] = literal_construct(ite_tag.var, true);

  ite_literals[1] = b_true;
  ite_literals[2] = b_false;
  cnf_add_clause(cnf, ite_literals, 3, ite_clauses, ite_tag);

  ite_literals[1] = literal_negate(cond);
  ite_literals[2] = b_true;
  cnf_add_clause(cnf, ite_literals, 3, ite_clauses, ite_tag);

  ite_literals[1] = cond;
  ite_literals[2] = b_false;
  cnf_add_clause(cnf, ite_literals, 3, ite_clauses, ite_tag);

  // !ite => !(ite cond b_true b_false)
  // !ite => (!b_true | !b_false) & (cond => !b_true) & (!cond -> !b_false)
  // !ite => (!b_true | !b_false) & (!cond | !b_true) & (cond | !b_false)
  // (ite | !b_true | !b_false) & (ite | !cond | !b_true) & (ite | cond | !b_false)

  ite_literals[0] = literal_construct(ite_tag.var, false);

  ite_literals[1] = literal_negate(b_true);
  ite_literals[2] = literal_negate(b_false);
  cnf_add_clause(cnf, ite_literals, 3, ite_clauses, ite_tag);

  ite_literals[1] = literal_negate(cond);
  ite_literals[2] = literal_negate(b_true);
  cnf_add_clause(cnf, ite_literals, 3, ite_clauses, ite_tag);

  ite_literals[1] = cond;
  ite_literals[2] = literal_negate(b_false);
  cnf_add_clause(cnf, ite_literals, 3, ite_clauses, ite_tag);

  cnf_end(cnf);
}

mcsat_literal_t cnf_convert(cnf_t* cnf, term_t t, ivector_t* t_clauses) {
  bool t_negated;
  term_kind_t t_kind;
  mcsat_literal_t t_lit;
  variable_t t_lit_var;

  assert(is_boolean_term(cnf->ctx->terms, t));

  // Only convert positive ones
  t_negated = is_neg_term(t);
  t = unsigned_term(t);

  // The variable
  t_lit_var = variable_db_get_variable(cnf->ctx->var_db, t);
  t_lit = literal_construct(t_lit_var, t_negated);

  // Check if converted already
  if (!cnf_is_converted(cnf, t_lit_var)) {
    // Convert based on the kind
    t_kind = term_kind(cnf->ctx->terms, t);
    switch (t_kind) {
    case OR_TERM:
      cnf_convert_or(cnf, t, t_clauses);
      break;
    case XOR_TERM:
      cnf_convert_xor(cnf, t, t_clauses);
      break;
    case EQ_TERM: {
      term_t lhs = eq_term_desc(cnf->ctx->terms, t)->arg[0];
      type_kind_t lhs_type = term_type_kind(cnf->ctx->terms, lhs);
      if (lhs_type == BOOL_TYPE) {
        cnf_convert_eq(cnf, t, t_clauses);
      }
      break;
    }
    case ITE_TERM:
      cnf_convert_ite(cnf, t, t_clauses);
      break;
    default:
      // We're fine, just a variable
      break;
    }
  }

  return t_lit;
}

void cnf_convert_lemma(cnf_t* cnf, const ivector_t* lemma, ivector_t* clauses) {
  uint32_t i;
  mcsat_literal_t* or_literals;
  mcsat_clause_tag_t or_tag;

  or_literals = safe_malloc(sizeof(mcsat_literal_t) * lemma->size);

  for (i = 0; i < lemma->size; ++ i) {
    or_literals[i] = cnf_convert(cnf, lemma->data[i], clauses);
  }

  or_tag.type = CLAUSE_LEMMA;
  or_tag.score = 0;
  cnf_add_clause(cnf, or_literals, lemma->size, clauses, or_tag);

  safe_free(or_literals);
}

void cnf_gc_mark(cnf_t* cnf, gc_info_t* gc_clauses, const gc_info_t* gc_vars) {
  static uint32_t i;

  variable_t var;
  clause_ref_t clause_ref;
  int_lset_iterator_t it;

  // If first time at gc, reset the index
  if (gc_vars->level == 0) {
    i = 0;
  }

  // CNF marks only the clauses that are definitions of the variables to keep
  for (; i < gc_vars->marked.size; ++ i) {
    var = gc_vars->marked.data[i];
    if(cnf_is_converted(cnf, var)) {
      int_lset_iterator_construct(&it, &cnf->converted, var);
      while (!int_lset_iterator_done(&it)) {
        clause_ref = *int_lset_iterator_get(&it);
        assert(clause_db_is_clause(cnf->clause_db, clause_ref, true));
        gc_info_mark(gc_clauses, clause_ref);
        int_lset_iterator_next_and_keep(&it);
      }
      int_lset_iterator_destruct(&it);
    }
  }
}

void cnf_gc_sweep(cnf_t* cnf, const gc_info_t* gc_clauses, int_mset_t* vars_undefined) {

  uint32_t i;
  variable_t var;
  ivector_t* vars_to_undef;

  // List of variables that lost a clause of their definition
  // we need to mark them as untranslated
  vars_to_undef = int_mset_get_list(vars_undefined);
  for (i = 0; i < vars_to_undef->size; ++ i) {
    var = vars_to_undef->data[i];
    cnf_remove(cnf, var);
  }

  // Update the converted list
  int_lset_reloc_elements(&cnf->converted, gc_clauses);
}
