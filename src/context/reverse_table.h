/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2018 SRI International.
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
 * DATA STRUCTURES TO MAP SOLVER/CONTEXT OBJECTS BACK TO TERMS
 */

/*
 * An internalization table keeps track of mapping from terms
 * to literals, arithmetic or bitvector variables, or Egraph terms.
 * It also stores variable substitution.
 *
 * A reverse table keeps the reverse mapping: from solver objects to
 * term. It also store equalities between terms.
 */

#ifndef __REVERSE_TABLE_H
#define __REVERSE_TABLE_H

#include <stdint.h>

#include "context/internalization_table.h"
#include "terms/terms.h"
#include "utils/resize_arrays.h"
#include "utils/vector_hash_map.h"


/*
 * We use four arrays to reverse the internalization
 * - bool_map:   boolean variables to terms
 * - arith_map:  arithmetic variables to terms
 * - bv_map:     bitvector variables to terms
 * - egraph_map: egraph terms to Yices terms
 *
 * A term t that occurs in the egraph map may also occur
 * in one of the other three (i.e., t is internalized to some
 * egraph term g and thvar[g] is some theory variable x).
 *
 * We also build term partitions to deal with uninterpreted terms
 * that get eliminated during preprocessing. We keep the partition
 * into a vector hash map table: if root(x) = r and root(y) = r
 * then x and y are stored in a vector of key r.
 */
typedef struct reverse_table_s {
  resize_array_t bool_map;
  resize_array_t arith_map;
  resize_array_t bv_map;
  resize_array_t egraph_map;
  vector_hmap_t partition;
} reverse_table_t;






#endif /* __REVERSE_TABLE_H */
