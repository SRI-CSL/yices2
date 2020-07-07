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

#ifndef __QUANT_EMATCHING_H
#define __QUANT_EMATCHING_H



#include "solvers/quant/quant_cnstr.h"
#include "solvers/quant/ematch_execute.h"

/*
 * E-match globals
 */
typedef struct ematch_globals_s {
  ematch_instr_table_t itbl;   // instruction table
  ematch_compile_t comp;       // pattern compiler
  ematch_exec_t exec;          // code executer
  int_hmap_t pattern2code;     // map from pattern term to index in instruction table
  instance_table_t instbl;     // instance table

  pattern_table_t *ptbl;       // link to pattern table
  quant_table_t *qtbl;         // link to quant cnstr table
  egraph_t *egraph;            // link to egraph
  context_t *ctx;              // link to context
} ematch_globals_t;


/****************
 *   EMATCHING  *
 ***************/

/*
 * Initialize pattern compiler
 */
extern void init_ematch(ematch_globals_t *em);

/*
 * Reset ematching
 */
extern void reset_ematch(ematch_globals_t *em);

/*
 * Delete ematching
 */
extern void delete_ematch(ematch_globals_t *em);


/*
 * Attach tables
 */
extern void ematch_attach_tbl(ematch_globals_t *em, term_table_t *terms,
      pattern_table_t *ptbl, quant_table_t *qtbl, context_t *ctx);

/*
 * Attach egraph
 */
extern void ematch_attach_egraph(ematch_globals_t *em, egraph_t *egraph);


/*
 * Compile all patterns and fill in the pattern2code map
 */
extern void ematch_compile_all_patterns(ematch_globals_t *em);

/*
 * Execute all patterns
 */
extern void ematch_execute_all_patterns(ematch_globals_t *em);


#endif /* __QUANT_EMATCHING_H */
