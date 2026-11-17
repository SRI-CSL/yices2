/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * INSTRUCTION/CODE EXECUTER FOR E-MATCHING
 */

#ifndef __EMATCH_EXECUTE_H
#define __EMATCH_EXECUTE_H

#include "solvers/quant/ematch_compile.h"
#include "solvers/quant/ematch_instr_stack.h"
#include "solvers/quant/ematch_instance.h"
#include "solvers/quant/term_learner.h"



/*
 * E-match code executer
 */
typedef struct ematch_exec_s {
  ivector_t reg;                // register array
  ematch_stack_t bstack;        // instruction stack
  ivector_t aux_vector;         // temporary vector
  ivector_t aux_vector2;        // temporary vector
  int_hmap_t aux_map;           // temporary table

  ematch_compile_t *comp;       // ematch compiler
  ematch_instr_table_t *itbl;   // ematch instruction table
  term_table_t *terms;          // term table
  instance_table_t *instbl;     // instance table

  egraph_t *egraph;             // link to egraph
  intern_tbl_t *intern;         // link to internalization table

  int_hset_t *filter;           // instance indices to filter out (since already learnt)

  uint32_t fdepth;              // function composition depth allowed for the fapps during matching
  uint32_t vdepth;              // function composition depth allowed for the variable matches

  uint32_t max_fdepth;          // max function composition depth allowed for the fapps during matching
  uint32_t max_vdepth;          // max function composition depth allowed for the variable matches
  uint32_t max_fapps;           // max bound on the number of function applications allowed during matching
  uint32_t max_matches;         // max bound on the number of new matches allowed during matching
  uint32_t max_matches_per_yield;   // max bound on the number of new matches allowed during yield

  term_learner_t *term_learner;     // Reinforce learner
  iterate_kind_t *iter_mode;        // iteration mode
} ematch_exec_t;


/*
 * Initialize code executer
 */
extern void init_ematch_exec(ematch_exec_t *exec, ematch_compile_t *comp, instance_table_t *instbl);

/*
 * Reset code executer
 */
extern void reset_ematch_exec(ematch_exec_t *exec);

/*
 * Delete code executer
 */
extern void delete_ematch_exec(ematch_exec_t *exec);

/*
 * Execute a code sequence corresponding to idx in instruction table
 */
extern void ematch_exec_instr(ematch_exec_t *exec, int32_t idx);

/*
 * Execute the code sequence for a pattern
 * - returns number of matches found
 */
extern uint32_t ematch_exec_pattern(ematch_exec_t *exec, pattern_t *pat, int_hset_t *filter, uint32_t nmatches);


#endif /* __EMATCH_EXECUTE_H */
