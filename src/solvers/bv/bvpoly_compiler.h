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
 * SUPPORT FOR CONVERTING BIT-VECTOR POLYNOMIALS
 * TO ELEMENTARY EXPRESSIONS.
 */

/*
 * In the bv_vartable, some bitvector variables represent
 * polynomial expressions. These variables are constructed
 * with tags BVTAG_POLY64, BVTAG_POLY, or BVTAG_PPROD.
 *
 * Before bit-blasting, we must convert these expressions
 * to equivalent terms that can be processed by the bit-blaster,
 * that is, terms built using the following operators:
 *   binary add:  (bvadd x y)
 *   binary sub:  (bvsub x y)
 *   binary mul:  (bvmul x y)
 *   negation:    (bvneg x)
 *
 * This module implements this translation process and keeps
 * track of the conversion.
 */

#ifndef __BVPOLY_COMPILER_H
#define __BVPOLY_COMPILER_H


#include <stdint.h>

#include "solvers/bv/bv_vartable.h"
#include "solvers/bv/bvpoly_dag.h"
#include "solvers/bv/merge_table.h"
#include "terms/bvpoly_buffers.h"
#include "utils/int_bv_sets.h"
#include "utils/backtrack_int_hash_map.h"
#include "utils/int_vectors.h"


/*
 * Queue of variable
 * - each element in this queue is a variable index i
 * - the variables are sorted in topological order
 *   (i.e., if i is (BVADD j k) and j is (BVADD ...) then
 *   j occurs before i in the queue).
 *
 * This is stored as in data[0 ... top-1]
 * - size = full size of array data
 */
typedef struct bvc_queue_s {
  thvar_t *data;
  uint32_t top;
  uint32_t size;
} bvc_queue_t;

#define DEF_BVC_QUEUE_SIZE 100
#define MAX_BVC_QUEUE_SIZE (UINT32_MAX/sizeof(thvar_t))


/*
 * Compiler structure:
 * - pointer to the relevant variable and merge tables
 * - a compilation map: maps polynomial ids to elementary expressions
 * - elemexp = all elementary expressions constructed
 *
 * For compilation
 * - dag for compilation/sharing of subexpressions
 * - queue = queue of polynomials to compile
 * - in_queue = set of all elements in the queue
 */
typedef struct bvc_s {
  bv_vartable_t *vtbl;
  mtbl_t *mtbl;
  back_hmap_t cmap;
  bvc_queue_t elemexp;

  // data structures used during compilation
  bvc_dag_t dag;
  bvc_queue_t queue;
  int_bvset_t in_queue;

  // auxiliary buffers
  ivector_t buffer;
  bvpoly_buffer_t pbuffer;
  pp_buffer_t pp_buffer;
} bvc_t;



/*
 * OPERATIONS
 */

/*
 * Initialization:
 * - vtbl = the attached variable table
 * - mtbl = the attached merge table
 * - elemexp is initially empty
 * - cmap has default initial size (cf. int_hash_map)
 */
extern void init_bv_compiler(bvc_t *c, bv_vartable_t *vtbl, mtbl_t *mtbl);

/*
 * Free all memory
 */
extern void delete_bv_compiler(bvc_t *c);

/*
 * Empty the content
 */
extern void reset_bv_compiler(bvc_t *c);

/*
 * Push: prepare a backtrack point
 */
extern void bv_compiler_push(bvc_t *c);

/*
 * Pop: go back to the previous backtrack point
 * - nv = number of variables at that point
 * - all variables with index >= nv are removed from
 *   the compiler queue
 */
extern void bv_compiler_pop(bvc_t *c, uint32_t nv);

/*
 * Set level to n:
 * - this has the same effect as calling push n times
 * - we use this function to make sure the compiler's internal
 *   level is the same as the bv_solver when the compiler i
 *   allocated.
 */
extern void bv_compiler_set_level(bvc_t *c, uint32_t n);


/*
 * Get the variable mapped to x in cmap
 * - return null_thvar (-1) if nothing is mapped to x
 * - x must be a valid variable in c->vtbl
 */
extern thvar_t bvvar_compiles_to(bvc_t *c, thvar_t x);


/*
 * Add variable x to the compilation queue
 * - x must be a valid variable in c->vtbl
 * - x's definition must be a polynomial (i.e., x must have
 *   tag BVTAG_POLY, BVTAG_POLY64, or BVTAG_PPROD).
 */
extern void bv_compiler_push_var(bvc_t *c, thvar_t x);


/*
 * Process the compilation queue. All variables pushed into the queue
 * are compiled to elementary expression, then the queue is emptied.
 * - after this call, use 'bvvar_compiles_to' to find out what a
 *   variable is compiled to.
 */
extern void bv_compiler_process_queue(bvc_t *c);




#endif /* __BVPOLY_COMPILER_H */
