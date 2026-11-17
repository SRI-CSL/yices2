/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * PRINT INTERNALIZATION TABLE
 */

#if defined(CYGWIN) || defined(MINGW)
#define EXPORTED __declspec(dllexport)
#define __YICES_DLLSPEC__ EXPORTED
#else
#define EXPORTED __attribute__((visibility("default")))
#endif

#include <assert.h>
#include <inttypes.h>

#include "context/internalization_codes.h"
#include "context/internalization_printer.h"
#include "io/term_printer.h"
#include "io/type_printer.h"
#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/egraph/egraph_printer.h"
#include "yices.h"


/*
 * Internalization code x of type tau
 */
static void print_intern_code(FILE *f, int32_t x, type_table_t *types, type_t tau) {
  if (! code_is_valid(x)) {
    fprintf(f, "code %"PRId32, x);
  } else if (code_is_eterm(x)) {
    print_occurrence(f, code2occ(x));
  } else {
    assert(code_is_var(x));
    if (is_boolean_type(tau)) {
      print_literal(f, code2literal(x));
    } else if (is_integer_type(tau)) {
      fprintf(f, "i!%"PRId32, code2thvar(x));
    } else if (is_real_type(tau)) {
      fprintf(f, "z!%"PRId32, code2thvar(x));
    } else {
      assert(is_bv_type(types, tau));
      fprintf(f, "u!%"PRId32, code2thvar(x));
    }
  }
}


static void print_opposite_code(FILE *f, int32_t x) {
  if (! code_is_valid(x)) {
    fprintf(f, "code %"PRId32, x);
  } else if (code_is_eterm(x)) {
    print_occurrence(f, opposite_occ(code2occ(x)));
  } else {
    assert(code_is_var(x));
    print_literal(f, not(code2literal(x)));
  }
}


/*
 * Print internalization data for term t:
 * - print t's root in the substitution tree
 * - print what's mapped to t if any
 */
void print_term_intern(FILE *f, intern_tbl_t *tbl, term_t t) {
  term_table_t *terms;
  type_table_t *types;
  term_t r;
  type_t tau;
  int32_t code;

  terms = tbl->terms;
  types = tbl->types;

  print_term_name(f, terms, t);
  fputs(" --> ", f);
  if (! intern_tbl_term_present(tbl, t)) {
    fputs(" not internalized\n", f);
  } else {
    r = intern_tbl_find_root(tbl, t);
    if (r == t) {
      fputs(" root term\n", f);
    } else {
      fputs(" root: ", f);
      print_term_name(f, terms, r);
      fputc('\n', f);
    }

    tau = intern_tbl_type_of_root(tbl, r);
    fputs("          type: ", f);
    print_type(f, types, tau);
    fputc('\n', f);

    if (intern_tbl_root_is_mapped(tbl, r)) {
      fputs("          internalized to: ", f);
      code = intern_tbl_map_of_root(tbl, unsigned_term(r));
      if (is_pos_term(r)) {
        print_intern_code(f, code, types, tau);
        fputc('\n', f);
      } else {
        assert(is_boolean_type(tau));
        print_opposite_code(f, code);
        fputc('\n', f);
      }
    } else {
      fputs("          not internalized\n", f);
    }
  }
}


/*
 * Print reverse internalization data for code:
 * - print what's mapped to code if any
 */
void print_intern_reverse(FILE *f, intern_tbl_t *tbl, int32_t code) {
  type_table_t *types;
  term_t r;
  type_t tau;
  int_hmap_pair_t *ip;

  types = tbl->types;
  ip = int_hmap_find(&tbl->reverse_map, code);
  if (ip != NULL) {
    r = ip->val;
    tau = intern_tbl_type_of_root(tbl, r);
    print_intern_code(f, code, types, tau);
    fputs(" -> ", f);
    yices_pp_term(f, r, 120, 1, 0);
  }
}


/*
 * Print the term mapped to occurrence x (if any)
 */
void intern_tbl_print_reverse(intern_tbl_t *tbl, occ_t x) {
  term_t r;
  r = intern_tbl_reverse_map(tbl, x);
  if (r != NULL_TERM) {
//    printf("%s", yices_term_to_string(r, 120, 1, 0));
    yices_pp_term(stdout, r, 120, 1, 0);
  } else {
    print_occurrence(stdout, x);
    printf("\n");
  }
}


/*
 * Print all substitution data in tbl
 */
void print_intern_substitution(FILE *f, intern_tbl_t *tbl) {
  term_table_t *terms;
  uint32_t i, n;
  term_t t, r;

  terms = tbl->terms;
  n = tbl->map.top;     // number of terms in tbl->map
  for (i=0; i<n; i++) {
    if (good_term_idx(terms, i) && !intern_tbl_is_root_idx(tbl, i)) {
      t = pos_term(i);
      r = intern_tbl_find_root(tbl, t);
      print_term_name(f, terms, t);
      fputs(" --> ", f);
      print_term_desc(f, terms, r);
      fputc('\n', f);
    }
  }
  fflush(f);
}


/*
 * Print all mapping data in tbl
 */
void print_intern_mapping(FILE *f, intern_tbl_t *tbl) {
  term_table_t *terms;
  type_table_t *types;
  uint32_t i, n;
  term_t r;
  type_t tau;
  int32_t code;

  terms = tbl->terms;
  types = tbl->types;
  n = tbl->map.top;
  for (i=0; i<n; i++) {
    if (good_term_idx(terms, i) && intern_tbl_is_root_idx(tbl, i)) {
      r = pos_term(i);
      if (intern_tbl_root_is_mapped(tbl, r)) {
        tau = intern_tbl_type_of_root(tbl, r);
        code = intern_tbl_map_of_root(tbl, r);
        fprintf(f, "t!%"PRIu32": ", i);
        print_term_desc(f, terms, r);
        fputs(" mapped to ", f);
        print_intern_code(f, code, types, tau);
        fputs("\n", f);
      }
    }
  }
  fflush(f);
}


/*
 * Variant formatting for substitutions
 */
void print_intern_substitution2(FILE *f, intern_tbl_t *tbl) {
  term_table_t *terms;
  uint32_t i, n;
  term_t t, r;

  terms = tbl->terms;
  n = tbl->map.top;     // number of terms in tbl->map
  for (i=0; i<n; i++) {
    if (good_term_idx(terms, i) && !intern_tbl_is_root_idx(tbl, i)) {
      t = pos_term(i);
      r = intern_tbl_find_root(tbl, t);
      print_term_name(f, terms, t);
      fputs(" --> ", f);
      print_term_full(f, terms, r);
      fputc('\n', f);
    }
  }
  fflush(f);
}


