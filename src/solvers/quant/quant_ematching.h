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



#include "solvers/quant/quant_solver.h"
#include "utils/pair_hash_sets.h"
#include "solvers/quant/quant_pattern.h"

/*
 * E-match opcodes
 */
typedef enum ematch_opcodes_s {
  EMATCH_NOOP,           // [ noop ]
  EMATCH_STOP,           // [ stop ]
  EMATCH_INIT,           // [ init(f, next) ]
  EMATCH_BIND,           // [ bind(i, f, o, next) ]
  EMATCH_CHECK,          // [ check(i, t, next) ]
  EMATCH_COMPARE,        // [ compare(i, j, next) ]
  EMATCH_CHOOSE,         // [ choose(alt, next) ]
  EMATCH_YIELD,          // [ yield(i1, ..., ik) ]
  EMATCH_BACKTRACK,      // [ backtrack ]
  EMATCH_CHOOSEAPP,      // [ choose-app(o, next, s, j) ]
  EMATCH_FILTER,         // [ filter(i, fs, next) ]
} ematch_opcodes_t;

#define NUM_EMATCH_OPCODES (EMATCH_CHOOSEAPP+1)


/*
 * E-match instruction
 */
typedef struct ematch_instr_s {
  ematch_opcodes_t op;

  term_t f;
  term_t t;

  uint32_t i;
  uint32_t j;
  uint32_t o;

  int_pair_t *subs;
  uint32_t nsubs;

  int32_t alt;
  int32_t next;

} ematch_instr_t;


/*
 * E-match instruction table
 */
typedef struct ematch_instr_table_s {
  uint32_t size;
  uint32_t ninstr;
  ematch_instr_t *data;
} ematch_instr_table_t;

#define DEF_EMATCH_INSTR_TABLE_SIZE  20
#define MAX_EMATCH_INSTR_TABLE_SIZE  (UINT32_MAX/8)


/*
 * Stack for ematch instruction:
 * - for every push: keep an ematch_instr
 */
typedef struct ematch_stack_s {
  uint32_t size;
  uint32_t top;
  ematch_instr_t **data;
} ematch_stack_t;

#define DEF_EMATCH_STACK_SIZE 20
#define MAX_EMATCH_STACK_SIZE (UINT32_MAX/sizeof(ematch_instr_t))


/*
 * E-match compile
 */
typedef struct ematch_compile_s {
  int_hmap_t W[4];              // working set: map from register indices to patterns
                                // one each for compare (0), check (1), filter (2), others (3)

  int_hmap_t V;                 // variables: map from variables to register indices
  int32_t o;                    // offset: value of the next available register index

  ematch_instr_table_t *itbl;   // ematch instruction table
  term_table_t *terms;          // term table
} ematch_compile_t;


/*
 * E-match globals
 */
typedef struct ematch_globals_s {
  ematch_instr_table_t itbl;   // instruction table
  ematch_compile_t comp;       // pattern compiler

  int_hmap_t pattern2code;     // map from pattern term to index in instruction table
  ivector_t reg;               // register array
  ematch_stack_t bstack;       // instruction stack

  pattern_table_t *ptbl;       // link to pattern table
} ematch_globals_t;


/*
 * Compile based on working set
 */
int32_t ematch_compile(ematch_compile_t *comp);


/****************
 *   EMATCHING  *
 ***************/


/*
 * Initialize pattern compiler
 */
extern void init_ematch(ematch_globals_t *em, term_table_t *terms, pattern_table_t *ptbl);

/*
 * Reset ematching
 */
extern void reset_ematch(ematch_globals_t *em);

/*
 * Delete ematching
 */
extern void delete_ematch(ematch_globals_t *em);

/*
 * Compile all patterns and fill in the pattern2code map
 */
extern void ematch_compile_all_patterns(ematch_globals_t *em);


#endif /* __QUANT_EMATCHING_H */
