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
 * E-MATCHING FOR QUANTIFIERS
 */


#include "solvers/quant/quant_ematching.h"


#define TRACE 0

#if TRACE

#include <stdio.h>

#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/egraph/egraph_printer.h"
#include "utils/index_vectors.h"

#include "yices.h"
#include "io/yices_pp.h"
#include "terms/term_explorer.h"

#endif


/****************
 *   EMATCHING  *
 ***************/

/*
 * Initialize ematching
 */
void init_ematch(ematch_globals_t *em) {
  em->ptbl = NULL;
  em->qtbl = NULL;
  em->ctx = NULL;
  em->egraph = NULL;
  init_ematch_instr_table(&em->itbl);
  init_ematch_compiler(&em->comp, &em->itbl, NULL);
  init_ematch_exec(&em->exec, &em->comp, &em->instbl);
  init_int_hmap(&em->pattern2code, 0);
  init_instance_table(&em->instbl);
}

/*
 * Reset ematching
 */
void reset_ematch(ematch_globals_t *em) {
  em->ptbl = NULL;
  em->qtbl = NULL;
  em->ctx = NULL;
  em->egraph = NULL;
  reset_ematch_instr_table(&em->itbl);
  reset_ematch_compiler(&em->comp);
  reset_ematch_exec(&em->exec);
  int_hmap_reset(&em->pattern2code);
  reset_instance_table(&em->instbl);
}

/*
 * Delete ematching
 */
void delete_ematch(ematch_globals_t *em) {
  em->ptbl = NULL;
  em->qtbl = NULL;
  em->ctx = NULL;
  em->egraph = NULL;
  delete_ematch_instr_table(&em->itbl);
  delete_ematch_compiler(&em->comp);
  delete_ematch_exec(&em->exec);
  delete_int_hmap(&em->pattern2code);
  delete_instance_table(&em->instbl);
}

/*
 * Attach tables
 */
void ematch_attach_tbl(ematch_globals_t *em, term_table_t *terms,
      pattern_table_t *ptbl, quant_table_t *qtbl, context_t *ctx) {
  assert(ptbl != NULL);
  assert(terms != NULL);
  assert(ctx != NULL);

  em->ptbl = ptbl;
  em->qtbl = qtbl;
  em->ctx = ctx;
  em->comp.terms = terms;
  em->exec.terms = terms;
  em->exec.intern = &ctx->intern;
}

/*
 * Attach egraph
 */
void ematch_attach_egraph(ematch_globals_t *em, egraph_t *egraph) {
  assert(egraph != NULL);
  em->egraph = egraph;
  em->exec.egraph = egraph;
}

/*
 * Compile all patterns and fill in the pattern2code map
 */
void ematch_compile_all_patterns(ematch_globals_t *em) {
  ematch_compile_t *comp;
  pattern_table_t *ptbl;
  int_hmap_t *pc;
  pattern_t *pat;
  uint32_t i;
  term_t t;
  int_hmap_pair_t *ip;

  comp =  &em->comp;
  ptbl = em->ptbl;
  pc = &em->pattern2code;
  comp->o = 0;

  for(i=0; i<ptbl->npatterns; i++) {
    pat = &ptbl->data[i];
    t = pat->p;
    ip = int_hmap_get(pc, t);
    if (ip->val < 0) {
      int_hmap_reset(&comp->W[0]);
      int_hmap_reset(&comp->W[1]);
      int_hmap_reset(&comp->W[2]);
      int_hmap_reset(&comp->W[3]);
      int_hmap_reset(&comp->V);
      comp->o = 0;

      ip->val = ematch_compile_pattern(comp, t);
      pat->code = ip->val;
    }
  }
}

/*
 * Execute all patterns
 */
void ematch_execute_all_patterns(ematch_globals_t *em) {
  ematch_exec_t *exec;
  pattern_table_t *ptbl;
  uint32_t i;
  pattern_t *pat;

  exec =  &em->exec;
  ptbl = em->ptbl;

  for(i=0; i<ptbl->npatterns; i++) {
    pat = &ptbl->data[i];
    ematch_exec_pattern(exec, pat, NULL);
  }
}

