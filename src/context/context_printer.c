/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CONTEXT PRINTER
 */

#include <inttypes.h>
#include <assert.h>

#include "io/term_printer.h"
#include "context/internalization_printer.h"
#include "context/context_printer.h"



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





/*
 * PRETTY PRINTER FOR  FLATTENING + VARIABLE ELIMINATION
 */

/*
 * Print the internal substitutions
 */
static void pp_intern_substitutions(yices_pp_t *printer, intern_tbl_t *tbl) {
  term_table_t *terms;
  uint32_t i, n;
  term_t t, r;

  terms = tbl->terms;
  n = tbl->map.top;
  for (i=0; i<n; i++) {
    if (good_term_idx(terms, i) && !intern_tbl_is_root_idx(tbl, i)) {
      t = pos_term(i);
      r = intern_tbl_find_root(tbl, t);
      pp_open_block(printer, PP_OPEN);
      pp_term_name(printer, terms, t);
      pp_string(printer, " := ");
      pp_term_full(printer, terms, r);
      pp_close_block(printer, false);
      flush_yices_pp(printer);
    }
  }
}


/*
 * Pretty print a vector
 */
static void pp_term_array(yices_pp_t *printer, term_table_t *terms, term_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    pp_term_full(printer, terms, a[i]);
    flush_yices_pp(printer);
  }
}

static void pp_term_vector(yices_pp_t *printer, term_table_t *terms, ivector_t *v) {
  pp_term_array(printer, terms, v->data, v->size);
}


/*
 * Pretty print the result of flattening + variable elimination
 */
void pp_context(FILE *f, context_t *ctx) {
  pp_area_t area;
  yices_pp_t printer;
  term_table_t *terms;

  terms = ctx->terms;

  area.width = 120;
  area.height = UINT32_MAX;
  area.offset = 0;
  area.stretch = false;
  area.truncate = false;

  init_yices_pp(&printer, f, &area, PP_VMODE, 0);
  pp_string(&printer, "Substitutions");
  flush_yices_pp(&printer);
  pp_intern_substitutions(&printer, &ctx->intern);

  pp_string(&printer, "Top equalities");
  flush_yices_pp(&printer);
  pp_term_vector(&printer, terms, &ctx->top_eqs);

  pp_string(&printer, "Top atoms");
  flush_yices_pp(&printer);
  pp_term_vector(&printer, terms, &ctx->top_atoms);

  pp_string(&printer, "Top formulas");
  flush_yices_pp(&printer);
  pp_term_vector(&printer, terms, &ctx->top_formulas);

  delete_yices_pp(&printer, true);
}

