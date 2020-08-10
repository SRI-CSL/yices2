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
 * PATTERN COMPILER FOR E-MATCHING
 */

#ifndef __QUANT_EMATCH_COMPILE_H
#define __QUANT_EMATCH_COMPILE_H

#include "solvers/quant/ematch_instr.h"

/*
 * E-match compile
 */
typedef struct ematch_compile_s {
  int_hmap_t W[4];              // working set: map from register indices to patterns
                                // one each for compare (0), check (1), filter (2), others (3)
                                // preference order: compare > check > filter > others

  int_queue_t patterns;         // pattern terms

  int_hmap_t V;                 // variables: map from variables to register indices
  int32_t o;                    // offset: value of the next available register index

  ematch_instr_table_t *itbl;   // ematch instruction table
  term_table_t *terms;          // term table
} ematch_compile_t;


/*
 * Initialize pattern compiler
 */
extern void init_ematch_compiler(ematch_compile_t *comp, ematch_instr_table_t *itbl, term_table_t *terms);

/*
 * Reset pattern compiler
 */
extern void reset_ematch_compiler(ematch_compile_t *comp);

/*
 * Delete pattern compiler
 */
extern void delete_ematch_compiler(ematch_compile_t *comp);

/*
 * Compile pattern to an instruction sequence
 * - returns an index in the instruction table
 */
extern int32_t ematch_compile_pattern(ematch_compile_t *comp, term_t pat);


extern void ematch_print_instr(FILE *f, ematch_instr_table_t *itbl, int32_t idx, bool recursive);


/*
 * Compile based on working set
 */
int32_t ematch_compile(ematch_compile_t *comp);




#endif /* __QUANT_EMATCH_COMPILE_H */
