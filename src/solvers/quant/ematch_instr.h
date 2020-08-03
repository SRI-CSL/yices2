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
 * INSTRUCTIONS/CODES FOR E-MATCHING
 */

#ifndef __EMATCH_INSTR_H
#define __EMATCH_INSTR_H

#include "utils/pair_hash_sets.h"
#include "solvers/quant/quant_pattern.h"

/*
 * E-match opcodes
 */
typedef enum ematch_opcodes_s {
  EMATCH_NOOP,           // [ noop ]
  EMATCH_STOP,           // [ stop ]
  EMATCH_INIT,           // [ init(f, o, next) ]
  EMATCH_BIND,           // [ bind(i, f, o, next) ]
  EMATCH_CHECK,          // [ check(i, t, next) ]
  EMATCH_COMPARE,        // [ compare(i, j, next) ]
  EMATCH_CHOOSE,         // [ choose(alt, next) ]
  EMATCH_YIELD,          // [ yield(i1, ..., ik) ]
  EMATCH_BACKTRACK,      // [ backtrack ]
  EMATCH_CHOOSEAPP,      // [ choose-app(o, next, s, j) ]
  EMATCH_FILTER,         // [ filter(i, fs, next) ]
  EMATCH_CONTINUE,       // [ continue(f, o, next) ]
} ematch_opcodes_t;

#define NUM_EMATCH_OPCODES (EMATCH_CONTINUE+1)


/*
 * E-match instruction
 */
typedef struct ematch_instr_s {
  ematch_opcodes_t op;
  int32_t idx;            // index in instruction table

  term_t f;
  occ_t occ;              // occurence, used later during execution

  uint32_t i;
  uint32_t j;
  uint32_t o;

  term_t *vdata;
  int32_t *idata;
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
 * Initialize: default size
 */
extern void init_ematch_instr_table(ematch_instr_table_t *table);

/*
 * Empty the table: delete all ematch_instr objects
 */
extern void reset_ematch_instr_table(ematch_instr_table_t *table);

/*
 * Delete the table
 */
extern void delete_ematch_instr_table(ematch_instr_table_t *table);

/*
 * Allocate a new ematch_instr index i
 * - data[i] is not initialized
 */
extern int32_t ematch_instr_table_alloc(ematch_instr_table_t *table);




#endif /* __EMATCH_INSTR_H */
