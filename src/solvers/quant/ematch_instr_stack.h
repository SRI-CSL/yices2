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
 * INSTRUCTION STACK FOR E-MATCHING
 */

#ifndef __EMATCH_INSTR_STACK_H
#define __EMATCH_INSTR_STACK_H


#include "solvers/quant/ematch_instr.h"


/*
 * Stack for ematch instruction:
 * - for every push: keep an ematch_instr
 */
typedef struct ematch_stack_s {
  uint32_t size;
  uint32_t top;
  int32_t *data;
} ematch_stack_t;

#define DEF_EMATCH_STACK_SIZE 20
#define MAX_EMATCH_STACK_SIZE (UINT32_MAX/sizeof(ematch_instr_t))



/*
 * Initialize the stack
 */
extern void init_ematch_stack(ematch_stack_t *stack);

/*
 * Empty the stack
 */
extern void reset_ematch_stack(ematch_stack_t *stack);

/*
 * Delete the stack
 */
extern void delete_ematch_stack(ematch_stack_t *stack);

/*
 * Save data for the current top element:
 */
extern void ematch_stack_save(ematch_stack_t *stack, int32_t idx);

/*
 * Get the top record
 */
extern int32_t ematch_stack_top(ematch_stack_t *stack);

/*
 * Remove the top record
 */
extern void ematch_stack_pop(ematch_stack_t *stack);



#endif /* __EMATCH_INSTR_STACK_H */
