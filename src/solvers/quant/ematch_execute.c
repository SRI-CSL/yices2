/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * INSTRUCTION/CODE EXECUTER FOR E-MATCHING
 */

#include "solvers/quant/ematch_execute.h"
#include "yices.h"

#define TRACE 0

#if TRACE

#include <stdio.h>

#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/egraph/egraph_printer.h"
#include "context/internalization_codes.h"

#include "io/yices_pp.h"
#include "terms/term_explorer.h"

#endif



/*
 * Initialize code executer
 */
void init_ematch_exec(ematch_exec_t *exec, ematch_compile_t *comp) {
  init_ivector(&exec->reg, 10);
  init_ematch_stack(&exec->bstack);

  exec->comp = comp;
  exec->itbl = comp->itbl;
  exec->terms = comp->terms;
  exec->egraph = NULL;
  exec->intern = NULL;
}

/*
 * Reset code executer
 */
void reset_ematch_exec(ematch_exec_t *exec) {
  ivector_reset(&exec->reg);
  reset_ematch_stack(&exec->bstack);

  exec->comp = NULL;
  exec->itbl = NULL;
  exec->terms = NULL;
  exec->egraph = NULL;
  exec->intern = NULL;
}

/*
 * Delete code executer
 */
void delete_ematch_exec(ematch_exec_t *exec) {
  delete_ivector(&exec->reg);
  delete_ematch_stack(&exec->bstack);

  exec->comp = NULL;
  exec->itbl = NULL;
  exec->terms = NULL;
  exec->egraph = NULL;
  exec->intern = NULL;
}

/**********************
 *   EGRAPH COMMANDS  *
 *********************/

/*
 * Collect all function applications for function f, and push in out vector
 */
static void egraph_get_all_fapps(egraph_t *egraph, eterm_t f, ivector_t *out) {
  composite_t *p;
  uint32_t i, n;
  term_t x;

#if TRACE
  printf("  Finding all fapps for eterm: ");
  print_eterm_id(stdout, f);
  printf("\n");
#endif

  n = egraph->terms.nterms;
  for (i=0; i<n; i++) {
    p = egraph_term_body(egraph, i);
    if (composite_body(p)) {
      if (valid_entry(p) && composite_kind(p) == COMPOSITE_APPLY) {
        x = term_of_occ(composite_child(p, 0));
        if (x == f) {
          ivector_push(out, i);
#if TRACE
          fputs("    (pushing) ", stdout);
          print_eterm_id(stdout, i);
          fputc('\n', stdout);
#endif
        }
      }
    }
  }

}


/********************
 *   CODE EXECUTER  *
 *******************/

/*
 * Set register at idx to term t
 */
static occ_t term2occ(intern_tbl_t *tbl, term_t t) {
  term_t r;
  int32_t code;
  occ_t occ;

  occ = null_occurrence;

  if (! intern_tbl_term_present(tbl, t)) {
//    fputs(" not internalized\n", stdout);
  } else {
    r = intern_tbl_find_root(tbl, t);
    if (r == t) {
//      fputs(" root term\n", stdout);
    } else {
//      fputs(" root: ", stdout);
//      print_term_name(stdout, terms, r);
//      fputc('\n', stdout);
    }

    if (intern_tbl_root_is_mapped(tbl, r)) {
//      fputs("          internalized to: ", stdout);
      code = intern_tbl_map_of_root(tbl, unsigned_term(r));
      if (code_is_valid(code) && code_is_eterm(code)) {
        if (is_pos_term(r)) {
          occ = code2occ(code);
        } else {
          occ = opposite_occ(code2occ(code));
        }
      } else {
//      fputs(" not valid/eterm\n", stdout);
      }
    } else {
//      fputs("          not internalized\n", stdout);
    }
  }

#if TRACE
  printf("    %s <-> ", yices_term_to_string(t, 120, 1, 0));
  print_occurrence(stdout, occ);
  printf("\n");
#endif

  return occ;
}


/*
 * Set register at idx to term t
 */
static occ_t instr_f2occ(ematch_exec_t *exec, ematch_instr_t *instr) {
  occ_t occ;

  occ = instr->occ;
  if (occ == null_occurrence) {
    occ = term2occ(exec->intern, instr->f);
    instr->occ = occ;
  }

  return occ;
}


/*
 * Set register at idx to term t
 */
static void ematch_exec_set_reg(ematch_exec_t *exec, occ_t t, uint32_t idx) {
  ivector_t *reg;
  uint32_t i, n;

  reg = &exec->reg;
  n = reg->size;
  if(idx < n) {
    reg->data[idx] = t;
  } else {
    n = (idx - n + 1);
    for(i=0; i<n; i++) {
      ivector_push(reg, NULL_TERM);
    }
    assert(idx < reg->size);
    reg->data[idx] = t;
  }

#if TRACE
  printf("    setting reg[%d] := ", idx);
  print_occurrence(stdout, t);
  printf("\n");
#endif

}

/*
 * Execute EMATCH_INIT code
 */
static void ematch_exec_init(ematch_exec_t *exec, ematch_instr_t *instr) {
  eterm_t t;
  occ_t focc;
  composite_t *fapp;
  ivector_t *reg;
  int32_t i, j, n;

  reg = &exec->reg;
  i = instr->o;

  assert(i >= 0);
  assert(i < reg->size);

  t = exec->reg.data[i];

  focc = instr_f2occ(exec, instr);
  assert(is_pos_occ(focc));

  fapp = egraph_term_body(exec->egraph, t);
  assert(composite_kind(fapp) == COMPOSITE_APPLY);
  assert(composite_child(fapp, 0) == focc);

  n = composite_arity(fapp);
  for(j=1; j<n; j++) {
    ematch_exec_set_reg(exec, composite_child(fapp, j), j);
  }

  ematch_exec_instr(exec, instr->next);
}

/*
 * Execute EMATCH_BIND code
 */
static void ematch_exec_bind(ematch_exec_t *exec, ematch_instr_t *instr) {
}

/*
 * Execute EMATCH_CHECK code
 */
static void ematch_exec_check(ematch_exec_t *exec, ematch_instr_t *instr) {
}

/*
 * Execute EMATCH_COMPARE code
 */
static void ematch_exec_compare(ematch_exec_t *exec, ematch_instr_t *instr) {
}

/*
 * Execute EMATCH_YIELD code
 */
static void ematch_exec_yield(ematch_exec_t *exec, ematch_instr_t *instr) {
}

/*
 * Execute EMATCH_FILTER code
 */
static void ematch_exec_filter(ematch_exec_t *exec, ematch_instr_t *instr) {
}


/*
 * Execute a code sequence corresponding to idx in instruction table
 */
void ematch_exec_instr(ematch_exec_t *exec, int32_t idx) {
  ematch_instr_t *instr;

  assert(idx >=0 && idx < exec->itbl->ninstr);
  instr = &exec->itbl->data[idx];

#if TRACE
  printf("  executing ");
  ematch_print_instr(stdout, exec->itbl, instr->idx, false);
#endif

  switch(instr->op) {
  case EMATCH_INIT:
    ematch_exec_init(exec, instr);
    break;
  case EMATCH_BIND:
    ematch_exec_bind(exec, instr);
    break;
  case EMATCH_CHECK:
    ematch_exec_check(exec, instr);
    break;
  case EMATCH_COMPARE:
    ematch_exec_compare(exec, instr);
    break;
  case EMATCH_YIELD:
    ematch_exec_yield(exec, instr);
    break;
  case EMATCH_FILTER:
    ematch_exec_filter(exec, instr);
    break;
  default:
    printf("Unsupported ematch instruction instr%d of type: %d\n", idx, instr->op);
    assert(0);
  }
}

/*
 * Execute the code sequence for a pattern
 */
void ematch_exec_pattern(ematch_exec_t *exec, pattern_t *pat) {
  term_table_t *terms;
  term_kind_t kind;
  ivector_t fapps;
  term_t f;
  uint32_t i, n;
  occ_t occ;
  eterm_t ef;

#if TRACE
    printf("\nMatching pattern: ");
    yices_pp_term(stdout, pat->p, 120, 1, 0);
#endif

  terms = exec->terms;
  kind = term_kind(terms, pat->p);
  if (kind == APP_TERM) {
    f = term_child(terms, pat->p, 0);
    occ = term2occ(exec->intern, f);
    if (occ != null_occurrence) {
      ef = term_of_occ(occ);

      init_ivector(&fapps, 4);

      egraph_get_all_fapps(exec->egraph, ef, &fapps);
      n = fapps.size;
      for(i=0; i<n; i++) {
#if TRACE
        printf("  Matching fapp: ");
        print_eterm_id(stdout, fapps.data[i]);
        printf("\n");
#endif
        ematch_exec_set_reg(exec, fapps.data[i], 0);
        ematch_exec_instr(exec, pat->code);
      }
      assert(0);

      delete_ivector(&fapps);
    }
  }
}




