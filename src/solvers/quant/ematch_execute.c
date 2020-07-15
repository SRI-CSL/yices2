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
#include "terms/term_explorer.h"
#include "context/internalization_codes.h"
#include "solvers/egraph/egraph_printer.h"
#include "solvers/egraph/egraph_base_types.h"
#include "yices.h"

#define TRACE 0

#if TRACE

#include <stdio.h>

#include "solvers/cdcl/smt_core_printer.h"

#include "io/yices_pp.h"

#endif



/*
 * Initialize code executer
 */
void init_ematch_exec(ematch_exec_t *exec, ematch_compile_t *comp, instance_table_t *instbl) {
  init_ivector(&exec->reg, 10);
  init_ematch_stack(&exec->bstack);
  init_ivector(&exec->aux_vector, 4);

  exec->comp = comp;
  exec->itbl = comp->itbl;
  exec->terms = comp->terms;
  exec->instbl = instbl;

  exec->egraph = NULL;
  exec->intern = NULL;
  exec->early_exit = true;
  exec->max_fdepth = 10;
  exec->max_vdepth = 4;
}

/*
 * Reset code executer
 */
void reset_ematch_exec(ematch_exec_t *exec) {
  ivector_reset(&exec->reg);
  reset_ematch_stack(&exec->bstack);
  ivector_reset(&exec->aux_vector);

  exec->comp = NULL;
  exec->itbl = NULL;
  exec->terms = NULL;
  exec->instbl = NULL;

  exec->egraph = NULL;
  exec->intern = NULL;
}

/*
 * Delete code executer
 */
void delete_ematch_exec(ematch_exec_t *exec) {
  delete_ivector(&exec->reg);
  delete_ematch_stack(&exec->bstack);
  delete_ivector(&exec->aux_vector);

  exec->comp = NULL;
  exec->itbl = NULL;
  exec->terms = NULL;
  exec->instbl = NULL;

  exec->egraph = NULL;
  exec->intern = NULL;
}


/**********************
 *   EGRAPH COMMANDS  *
 *********************/

/*
 * Collect all function applications for function f, and push in out vector
 */
static void egraph_get_all_fapps(ematch_exec_t *exec, eterm_t f, ivector_t *out) {
  egraph_t *egraph;
  composite_t *p;
  uint32_t i, n;
  eterm_t x;
  occ_t occi;

#if TRACE
  printf("  Finding all fapps for function ");
  print_eterm_id(stdout, f);
  printf("\n");
#endif

  egraph = exec->egraph;
  n = egraph->terms.nterms;
  for (i=0; i<n; i++) {
    p = egraph_term_body(egraph, i);
    if (composite_body(p)) {
      if (valid_entry(p) && composite_kind(p) == COMPOSITE_APPLY) {
        x = term_of_occ(composite_child(p, 0));
        if (x == f) {
          if (composite_depth(egraph, p) < exec->max_fdepth) {
            occi = pos_occ(i);
            ivector_push(out, occi);
#if TRACE
            fputs("    (pushing) ", stdout);
            print_occurrence(stdout, occi);
            printf(" @ depth %d", composite_depth(egraph, p));
            fputc('\n', stdout);
#endif
          }
          else {
#if TRACE
            fputs("    (filtered) ", stdout);
            print_composite(stdout, p);
            printf(" @ depth %d", composite_depth(egraph, p));
            fputc('\n', stdout);
#endif
          }
        }
      }
    }
  }
}

/*
 * Collect function applications for function f in the class of occ, and push in out vector
 */
static void egraph_get_fapps_in_class(ematch_exec_t *exec, eterm_t f, occ_t occ, ivector_t *out) {
  egraph_t *egraph;
  composite_t *p;
  eterm_t ti, x;
  occ_t occi;


#if TRACE
  printf("  Finding all fapps for function ");
  print_eterm_id(stdout, f);
  printf(" in the class of ");
  print_occurrence(stdout, occ);
  printf("\n");
#endif

  egraph = exec->egraph;
  occi = occ;
  do {
    ti = term_of_occ(occi);
    p = egraph_term_body(egraph, ti);
    if (composite_body(p)) {
      if (valid_entry(p) && composite_kind(p) == COMPOSITE_APPLY) {
        x = term_of_occ(composite_child(p, 0));
        if (x == f) {
          if (composite_depth(egraph, p) < exec->max_fdepth) {
            ivector_push(out, occi);
#if TRACE
            fputs("    (pushing) ", stdout);
            print_occurrence(stdout, occi);
            printf(" @ depth %d", composite_depth(egraph, p));
            fputc('\n', stdout);
#endif
          }
          else {
#if TRACE
            fputs("    (filtered) ", stdout);
            print_composite(stdout, p);
            printf(" @ depth %d", composite_depth(egraph, p));
            fputc('\n', stdout);
#endif
          }
        }
      }
    }
    occi = egraph_next(egraph, occi);
    assert(term_of_occ(occi) != term_of_occ(occ) || occi == occ);
  } while (occi != occ);

}

/*
 * Check if a function application for function f occurs in the class of occ
 */
static bool egraph_has_fapps_in_class(egraph_t *egraph, eterm_t f, occ_t occ) {
  composite_t *p;
  eterm_t ti, x;
  occ_t occi;


#if TRACE
  printf("  Checking if an fapp for function ");
  print_eterm_id(stdout, f);
  printf(" present in the class of ");
  print_occurrence(stdout, occ);
  printf("\n");
#endif

  occi = occ;
  do {
    ti = term_of_occ(occi);
    p = egraph_term_body(egraph, ti);
    if (composite_body(p)) {
      if (valid_entry(p) && composite_kind(p) == COMPOSITE_APPLY) {
        x = term_of_occ(composite_child(p, 0));
        if (x == f) {
#if TRACE
          printf("    found!\n");
#endif
          return true;
        }
      }
    }
    occi = egraph_next(egraph, occi);
    assert(term_of_occ(occi) != term_of_occ(occ) || occi == occ);
  } while (occi != occ);

#if TRACE
  printf("    not found!\n");
#endif

  return false;
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
 * Execute EMATCH BACKTRACK
 */
static void ematch_exec_backtrack(ematch_exec_t *exec) {
  ematch_stack_t *bstack;
  int32_t idx;

  bstack = &exec->bstack;
  if (bstack->top != 0) {
    idx = ematch_stack_top(bstack);
    ematch_stack_pop(bstack);
    ematch_exec_instr(exec, idx);
  } else {
    // stop
  }
}

/*
 * Compile EMATCH CHOOSEAPP
 */
static int32_t ematch_compile_chooseapp(ematch_compile_t *comp, int32_t o, int32_t bind, int32_t j) {
  ematch_instr_table_t *itbl;
  int32_t idx;
  ematch_instr_t *instr;

  itbl = comp->itbl;
  idx = ematch_instr_table_alloc(itbl);
  instr = itbl->data + idx;

  instr->op = EMATCH_CHOOSEAPP;
  instr->o = o;
  instr->next = bind;
  instr->j = j;

#if 0
  printf("    (pre) instr%d: choose-app(%d, instr%d, %d)\n", idx, instr->o, instr->next, instr->j);
#endif

  return idx;
}

/*
 * Execute EMATCH_INIT code
 */
static void ematch_exec_init(ematch_exec_t *exec, ematch_instr_t *instr) {
  occ_t occ;
  composite_t *fapp;
  int32_t i, j, n;

  i = instr->o;

  assert(i >= 0);
  assert(i < exec->reg.size);

  occ = exec->reg.data[i];

  assert(is_pos_occ(instr_f2occ(exec, instr)));

  fapp = egraph_term_body(exec->egraph, term_of_occ(occ));
  assert(composite_kind(fapp) == COMPOSITE_APPLY);
  assert(composite_child(fapp, 0) == instr_f2occ(exec, instr));

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
  eterm_t regt, ef;
  occ_t focc;
  int32_t i, j, n;
  ivector_t fapps;
  int32_t chooseapp;

  i = instr->i;
  assert(i >= 0);
  assert(i < exec->reg.size);

  regt = exec->reg.data[i];

  focc = instr_f2occ(exec, instr);
  if (focc == null_occurrence) {
    // do nothing
  } else {
    assert(is_pos_occ(focc));
    ef = term_of_occ(focc);

    init_ivector(&fapps, 4);

    egraph_get_fapps_in_class(exec, ef, regt, &fapps);
    n = fapps.size;

    instr->idata = (int32_t *) safe_malloc(n * sizeof(int32_t));
    instr->nsubs = n;
    for(j=0; j<n; j++) {
  #if TRACE
      printf("    choosing fapps: ");
      print_occurrence(stdout, fapps.data[j]);
      printf("\n");
  #endif
      instr->idata[j] = fapps.data[j];
    }

    delete_ivector(&fapps);

    chooseapp = ematch_compile_chooseapp(exec->comp, instr->o, instr->idx, 1);
    ematch_stack_save(&exec->bstack, chooseapp);
  }

  ematch_exec_backtrack(exec);
}

/*
 * Execute EMATCH_CHOOSEAPP code
 * - instr->next is the corresponding bind
 */
static void ematch_exec_chooseapp(ematch_exec_t *exec, ematch_instr_t *instr) {
  uint32_t i, j, n;
  int32_t idx, chooseapp, offset;
  ematch_instr_t *bind;
  occ_t occ;
  composite_t *fapp;

  offset = instr->o;
  j = instr->j;
  idx = instr->next;
  assert(idx >=0 && idx < exec->itbl->ninstr);
  bind = &exec->itbl->data[idx];

  if (bind->nsubs >= j) {
    occ = bind->idata[j-1];

    assert(is_pos_occ(instr_f2occ(exec, bind)));

    fapp = egraph_term_body(exec->egraph, term_of_occ(occ));
    assert(composite_kind(fapp) == COMPOSITE_APPLY);
    assert(composite_child(fapp, 0) == instr_f2occ(exec, bind));

    n = composite_arity(fapp);
    for(i=1; i<n; i++) {
      ematch_exec_set_reg(exec, composite_child(fapp, i), offset+i-1);
    }

    chooseapp = ematch_compile_chooseapp(exec->comp, offset, idx, j+1);
    ematch_stack_save(&exec->bstack, chooseapp);
    bind = &exec->itbl->data[idx];

    ematch_exec_instr(exec, bind->next);
  } else {
    ematch_exec_backtrack(exec);
  }
}

/*
 * Execute EMATCH_CHECK code
 */
static void ematch_exec_check(ematch_exec_t *exec, ematch_instr_t *instr) {
  occ_t lhs, rhs;
  ivector_t *reg;
  int32_t i;

  reg = &exec->reg;

  i = instr->i;
  assert(i >= 0);
  assert(i < reg->size);
  lhs = reg->data[i];

  rhs = instr_f2occ(exec, instr);
  if (rhs == null_occurrence) {
    ematch_exec_backtrack(exec);
  } else {
    assert(egraph_term_is_atomic(exec->egraph, term_of_occ(rhs)));

    if (egraph_equal_occ(exec->egraph, rhs, lhs)) {
      ematch_exec_instr(exec, instr->next);
    } else {
      ematch_exec_backtrack(exec);
    }
  }
}

/*
 * Execute EMATCH_COMPARE code
 */
static void ematch_exec_compare(ematch_exec_t *exec, ematch_instr_t *instr) {
  occ_t lhs, rhs;
  ivector_t *reg;
  int32_t i, j;

  reg = &exec->reg;

  i = instr->i;
  assert(i >= 0);
  assert(i < reg->size);
  lhs = reg->data[i];

  j = instr->j;
  assert(j >= 0);
  assert(j < reg->size);
  rhs = reg->data[j];

  if (egraph_equal_occ(exec->egraph, lhs, rhs)) {
    ematch_exec_instr(exec, instr->next);
  } else {
    ematch_exec_backtrack(exec);
  }
}

/*
 * Execute EMATCH_YIELD code
 */
static void ematch_exec_yield(ematch_exec_t *exec, ematch_instr_t *instr) {
  instance_table_t *insttbl;
  int32_t i, j, n;
  int32_t idx;
  ivector_t *reg;
  occ_t rhs;
  ivector_t v;
  int32_t maxdepth, cdepth;

  insttbl = exec->instbl;
  reg = &exec->reg;
  n = instr->nsubs;
  maxdepth = DEF_DEPTH;

  init_ivector(&v, n);

  for (j=0; j<n; j++) {
    idx = instr->idata[j];
    assert(idx >= 0);
    assert(idx < reg->size);
    rhs = reg->data[idx];
    ivector_push(&v, rhs);
    cdepth = occ_depth(exec->egraph, rhs);
    maxdepth = (cdepth > maxdepth) ? cdepth : maxdepth;
  }

  i = mk_instance(insttbl, instr->idx, n, instr->vdata, v.data);
  if (maxdepth < exec->max_vdepth) {
    if (exec->filter == NULL || !int_hset_member(exec->filter, i)) {
      ivector_push(&exec->aux_vector, i);
      if(exec->early_exit) {
        reset_ematch_stack(&exec->bstack);
      }

#if TRACE
      instance_t *inst;
      term_t lhs;

      inst = insttbl->data + i;
      assert(inst->nelems == n);

      printf("    match%d: (#%d entries @ depth %d) ", i, n, maxdepth);
      for (j=0; j<n; j++) {
        lhs = instr->vdata[j];
        rhs = inst->vdata[j];
        assert(lhs == rhs);

        idx = instr->idata[j];
        lhs = reg->data[idx];
        rhs = inst->odata[j];
        assert(lhs == rhs);

        printf("%s (%d) -> ", yices_term_to_string(inst->vdata[j], 120, 1, 0), inst->vdata[j]);
        print_occurrence(stdout, inst->odata[j]);
        printf(", ");
      }
      printf("\n");
#endif
    }
  }

  ematch_exec_backtrack(exec);
}

/*
 * Execute EMATCH_FILTER code
 */
static void ematch_exec_filter(ematch_exec_t *exec, ematch_instr_t *instr) {
  eterm_t regt, ef;
  occ_t focc;
  int32_t i;

  i = instr->i;
  assert(i >= 0);
  assert(i < exec->reg.size);

  regt = exec->reg.data[i];

  focc = instr_f2occ(exec, instr);
  if (focc == null_occurrence) {
    ematch_exec_backtrack(exec);
  } else {
    assert(focc != null_occurrence);
    assert(is_pos_occ(focc));
    ef = term_of_occ(focc);

    if (egraph_has_fapps_in_class(exec->egraph, ef, regt)) {
      ematch_exec_instr(exec, instr->next);
    } else {
      ematch_exec_backtrack(exec);
    }
  }
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
  case EMATCH_CHOOSEAPP:
    ematch_exec_chooseapp(exec, instr);
    break;
  default:
    printf("Unsupported ematch instruction instr%d of type: %d\n", idx, instr->op);
    assert(0);
  }
}


/***********************
 *   PATTERN EXECUTER  *
 **********************/

/*
 * Execute the code sequence for a pattern
 * - returns number of matches found
 */
uint32_t ematch_exec_pattern(ematch_exec_t *exec, pattern_t *pat, int_hset_t *filter) {
  uint32_t count;
  term_table_t *terms;
  term_kind_t kind;
  ivector_t fapps;
  term_t f;
  uint32_t i, j, n, m;
  occ_t occ;
  ivector_t *matches;
  ivector_t *aux;

#if TRACE
    printf("  Pattern code:\n");
    ematch_print_instr(stdout, exec->itbl, pat->code, true);
#endif

  exec->filter = filter;
  count = 0;
  terms = exec->terms;
  kind = term_kind(terms, pat->p);
  if (kind == APP_TERM) {
    f = term_child(terms, pat->p, 0);
    occ = term2occ(exec->intern, f);
    if (occ != null_occurrence) {
      matches = &pat->matches;

      ivector_reset(matches);

      init_ivector(&fapps, 4);

      egraph_get_all_fapps(exec, term_of_occ(occ), &fapps);
      n = fapps.size;
      for(i=0; i<n; i++) {
#if TRACE
        occ_t fapp = fapps.data[i];

        printf("  Matching fapp: ");
        print_occurrence(stdout, fapp);
        printf("\n");
#endif
        aux = &exec->aux_vector;
        ivector_reset(aux);
        ematch_exec_set_reg(exec, fapps.data[i], 0);
        assert(exec->bstack.top == 0);

        ematch_exec_instr(exec, pat->code);

        ivector_remove_duplicates(aux);
        m = aux->size;

        if (m != 0) {
#if TRACE
          printf("  Found %d matches from fapp ", m);
          print_occurrence(stdout, fapp);
          printf("\n");
#endif

          count += m;

          for(j=0; j!=m; j++) {
            ivector_push(matches, aux->data[j]);
          }
        }
      }
      delete_ivector(&fapps);
    }
  }

  return count;
}




