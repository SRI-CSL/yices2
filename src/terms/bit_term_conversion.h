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
 * CONVERSION BETWEEN BIT AND TERM REPRESENTATIONS
 */

/*
 * 'bits' are an intermediate representation used for simplifying
 * bit-vector expressions. A bit is a nodes in an XOR/OR/NOT DAG
 * (implemented in bit_expr).
 *
 * When bitvectors are stored as terms in a term table, the bits must
 * be converted to boolean terms.
 */

#ifndef __BIT_TERM_CONVERSION_H
#define __BIT_TERM_CONVERSION_H

#include "terms/bit_expr.h"
#include "terms/terms.h"
#include "utils/int_vectors.h"


/*
 * Convert boolean term t to a bit expression
 * - t must be a valid boolean term in table 'terms'
 * - nodes = table where the bit expression is
 *   constructed
 * - n = bound on recursive depth
 *
 * Side effect: if conversion for t is x, and x is not mapped to anything yet,
 * then map[x] is set to t in the node table.
 */
extern bit_t convert_term_to_bit(term_table_t *terms, node_table_t *nodes, term_t t, uint32_t n);



#if 0

// OBSOLETE

/*
 * Convert bit expression b to a boolean term
 * - b must be a valid bit expression in table 'nodes'
 * - new terms are created in table 'terms'
 *
 * The subgraph rooted at b is explored and all nodes reachable from b
 * are converted to boolean terms. No simplification or flattening is
 * applied.
 *
 * Side effect: the mapping is stored in nodes->map.
 */
extern term_t convert_bit_to_term(term_table_t *terms, node_table_t *nodes, bit_t b);

#endif


#endif /* __BIT_TERM_CONVERSION_H */
