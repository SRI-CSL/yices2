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
void init_ematch(ematch_globals_t *em, term_table_t *terms, pattern_table_t *ptbl) {
  em->ptbl = ptbl;
  init_ematch_instr_table(&em->itbl);
  init_ematch_compiler(&em->comp, &em->itbl, terms);
  init_int_hmap(&em->pattern2code, 0);
  init_ivector(&em->reg, 10);
  init_ematch_stack(&em->bstack);
}

/*
 * Reset ematching
 */
void reset_ematch(ematch_globals_t *em) {
  reset_ematch_instr_table(&em->itbl);
  reset_ematch_compiler(&em->comp);
  int_hmap_reset(&em->pattern2code);
  ivector_reset(&em->reg);
  reset_ematch_stack(&em->bstack);
}

/*
 * Delete ematching
 */
void delete_ematch(ematch_globals_t *em) {
  delete_ematch_instr_table(&em->itbl);
  delete_ematch_compiler(&em->comp);
  delete_int_hmap(&em->pattern2code);
  delete_ivector(&em->reg);
  delete_ematch_stack(&em->bstack);
}

/*
 * Compile all patterns and fill in the pattern2code map
 */
void ematch_compile_all_patterns(ematch_globals_t *em) {
  ematch_compile_t *comp;
  int_hmap_t *pc;
  uint32_t i;
  term_t t;
  int_hmap_pair_t *ip;
  pattern_table_t *ptbl;
  pattern_t *pat;

  ptbl = em->ptbl;
  comp =  &em->comp;
  pc = &em->pattern2code;

  for(i=0; i<ptbl->npatterns; i++) {
    pat = &ptbl->data[i];
    t = pat->p;
    ip = int_hmap_get(pc, t);
    if (ip->val < 0) {
      ip->val = ematch_compile_pattern(comp, t);
      pat->code = ip->val;
    }
  }
}
