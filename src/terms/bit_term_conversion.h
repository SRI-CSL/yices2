/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
