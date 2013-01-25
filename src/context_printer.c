/*
 * CONTEXT PRINTER
 */

#include <inttypes.h>
#include <assert.h>

#include "term_printer.h"
#include "internalization_printer.h"
#include "context_printer.h"



/*
 * Print eq as a candidate substitution
 */
static void print_subst_eq(FILE *f, context_t *ctx, term_t e) {
  composite_term_t *eq;
  term_table_t *terms;
  term_t t1, r1;
  term_t t2, r2;
  term_t v, t;

  terms = ctx->terms;
  switch (term_kind(terms, e)) {
  case EQ_TERM:
  case ARITH_BINEQ_ATOM:
  case BV_EQ_ATOM:
    eq = composite_term_desc(terms, e);
    t1 = eq->arg[0];
    t2 = eq->arg[1];
    break;

  default:
    assert(false);
    return;
  }

  r1 = intern_tbl_find_root(&ctx->intern, t1);
  r2 = intern_tbl_find_root(&ctx->intern, t2);
  if (is_neg(e)) {
    r2 = opposite_term(r2);
  }

  if (intern_tbl_root_is_free(&ctx->intern, r1)) {
    v = unsigned_term(r1);
    t = r2 ^ polarity_of(r1);
  } else if (intern_tbl_root_is_free(&ctx->intern, r2)) {
    v = unsigned_term(r2);
    t = r1 ^ polarity_of(r2);
  } else if (term_kind(terms, r1) == UNINTERPRETED_TERM) {
    v = unsigned_term(r1);
    t = r2 ^ polarity_of(r1);
  } else {
    v = unsigned_term(r2);
    t = r1 ^ polarity_of(r2);
  }

  assert(is_pos_term(v) && 
         term_kind(terms, v) == UNINTERPRETED_TERM);

  print_term_desc(f, terms, v);
  fputs(" := ", f);
  print_term_desc(f, terms, t); 
  fputs("\n         by assertion ", f);
  print_term_desc(f, terms, e);
}


/* 
 * Print all substitution candidates
 */
void print_context_subst_eqs(FILE *f, context_t *ctx) {
  uint32_t i, n;
  ivector_t *v;

  v = &ctx->subst_eqs;
  n = v->size;
  for (i=0; i<n; i++) {
    fprintf(f, "subst[%"PRIu32"]: ", i);
    print_subst_eq(f, ctx, v->data[i]);
    fputs("\n\n", f);
  } 
}


/*
 * Print a vector of terms: with name = vector name
 */
static void print_term_vector(FILE *f, term_table_t *tbl, char *name, ivector_t *v) {
  uint32_t i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    fprintf(f, "%s[%"PRIu32"]: ", name, i);
    print_term_desc(f, tbl, v->data[i]);
    fputs("\n\n", f);
  }
}

/*
 * All top_eqs, top_atoms, top_formulas
 */
void print_context_top_eqs(FILE *f, context_t *ctx) {
  print_term_vector(f, ctx->terms, "eq", &ctx->top_eqs);
}

void print_context_top_atoms(FILE *f, context_t *ctx) {
  print_term_vector(f, ctx->terms, "atom", &ctx->top_atoms);
}

void print_context_top_formulas(FILE *f, context_t *ctx) {
  print_term_vector(f, ctx->terms, "formula", &ctx->top_formulas);
}

void print_context_top_interns(FILE *f, context_t *ctx) {
  print_term_vector(f, ctx->terms, "intern", &ctx->top_interns);
}


/*
 * Internalization table: substitution and mapping
 */
void print_context_intern_subst(FILE *f, context_t *ctx) {
  print_intern_substitution(f, &ctx->intern);
}

void print_context_intern_mapping(FILE *f, context_t *ctx) {
  print_intern_mapping(f, &ctx->intern);
}
