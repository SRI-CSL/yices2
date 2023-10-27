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

#include <assert.h>

#include "terms/bit_term_conversion.h"


/*
 * Convert a boolean term t to a bit expression
 * - t must be a valid boolean term in the term table
 * - n = recursion depth
 *
 * Side effect: if conversion for t is x, and x is not mapped to anything yet,
 * then map[x] is set to (pos_term(index_of(t)) in the node table.
 */
bit_t convert_term_to_bit(term_table_t *table, node_table_t *nodes, term_t t, uint32_t n) {
  select_term_t *s;
  composite_term_t *d;
  bit_t x, b1, b2;
  int32_t i;

  assert(good_term(table, t) && is_boolean_term(table, t));

  i = index_of(t);
  switch (kind_for_idx(table, i)) {
  case CONSTANT_TERM:
    assert(i == bool_const);
    x = true_bit;
    break;

  case BIT_TERM:
    s = select_for_idx(table, i);
    x = node_table_alloc_select(nodes, s->idx, s->arg);
    break;

  case OR_TERM:
    d = composite_for_idx(table, i);
    if (n > 0 && d->arity == 2) {
      b1 = convert_term_to_bit(table, nodes, d->arg[0], n-1);
      b2 = convert_term_to_bit(table, nodes, d->arg[1], n-1);
      x = bit_or2(nodes, b1, b2);
    } else {
      x = node_table_alloc_var(nodes, pos_term(i));
    }
    break;

  case XOR_TERM:
    d = composite_for_idx(table, i);
    if (n > 0 && d->arity == 2) {
      b1 = convert_term_to_bit(table, nodes, d->arg[0], n-1);
      b2 = convert_term_to_bit(table, nodes, d->arg[1], n-1);
      x = bit_xor2(nodes, b1, b2);
    } else {
      x = node_table_alloc_var(nodes, pos_term(i));
    }
    break;

  default:
    x = node_table_alloc_var(nodes, pos_term(i));
    break;
  }

  /*
   * save the mapping x --> pos_term(i) in the node table
   * if x is positive, node_of_bit(x) := pos_term(i)
   * if x is negative, node_of_bit(x) := neg_term(i)
   */
  if (map_of_node(nodes, node_of_bit(x)) == -1) {
    set_map_of_node(nodes, node_of_bit(x), mk_term(i, bit_is_pos(x)));

    assert((bit_is_pos(x) && map_of_node(nodes, node_of_bit(x)) == pos_term(i)) ||
	   (bit_is_neg(x) && map_of_node(nodes, node_of_bit(x)) == neg_term(i)));
  }

  // flip x's polarity if t has negative polarity
  x ^= polarity_of(t);

  return x;
}


#if 0

// THIS IS OBSOLETE. THE CONVERSION FROM BIT TO TERMS IS NOW IMPLEMENTED
// IN term_manager.c.


/*
 * REVERSE CONVERSION: BIT TO TERMS
 */

/*
 * Recursive function: return the term mapped to node x
 * - compute it if needed then store the result in nodes->map[x]
 */
static term_t map_node_to_term(term_table_t *terms, node_table_t *nodes, node_t x);

/*
 * Get the term mapped to bit b. If node_of(b) is mapped to t then
 * - if b has positive polarity, map_of(b) = t
 * - if b has negative polarity, map_of(b) = not t
 */
static inline term_t map_bit_to_term(term_table_t *terms, node_table_t *nodes, bit_t b) {
  return map_node_to_term(terms, nodes, node_of_bit(b)) ^ polarity_of(b);
}


/*
 * Given two bits b1 = c[0] and b2 = c[1], convert (or b1 b2) to a term
 */
static term_t make_or2(term_table_t *terms, node_table_t *nodes, bit_t *c) {
  term_t aux[2];

  aux[0] = map_bit_to_term(terms, nodes, c[0]);
  aux[1] = map_bit_to_term(terms, nodes, c[1]);

  assert(is_boolean_term(terms, aux[0]) && is_boolean_term(terms, aux[1]));
  return or_term(terms, 2, aux);
}


/*
 * Same thing for (xor c[0] c[1])
 */
static term_t make_xor2(term_table_t *terms, node_table_t *nodes, bit_t *c) {
  term_t aux[2];

  aux[0] = map_bit_to_term(terms, nodes, c[0]);
  aux[1] = map_bit_to_term(terms, nodes, c[1]);

  assert(is_boolean_term(terms, aux[0]) && is_boolean_term(terms, aux[1]));
  return xor_term(terms, 2, aux);
}



/*
 * Recursive function: return the term mapped to node x
 * - compute it if needed then store the result in nodes->map[x]
 */
static term_t map_node_to_term(term_table_t *terms, node_table_t *nodes, node_t x) {
  term_t t;

  t = map_of_node(nodes, x);
  if (t < 0) {
    assert(t == -1);

    switch (node_kind(nodes, x)) {
    case CONSTANT_NODE:
      // x is true
      t = true_term;
      break;

    case VARIABLE_NODE:
      // x is (var t) for a boolean term t
      t = var_of_node(nodes, t);
      break;

    case SELECT_NODE:
      // x is (select i u) for a bitvector term u
      t = bit_term(terms, index_of_select_node(nodes, x), var_of_select_node(nodes, x));
      break;

    case OR_NODE:
      t = make_or2(terms, nodes, children_of_node(nodes, x));
      break;

    case XOR_NODE:
      t = make_xor2(terms, nodes, children_of_node(nodes, x));
      break;

    default:
      assert(false);
      abort();
      break;
    }

    assert(is_boolean_term(terms, t));
    set_map_of_node(nodes, x, t);
  }

  return t;
}


/*
 * Convert b (and all nodes reachable from b) to boolean terms
 * - b must be a valid bit expression in table 'nodes'
 * - new terms are created in table 'terms'
 *
 * The subgraph rooted at b is explored and all nodes reachable from b
 * are converted to boolean terms. No simplification or flattening is
 * applied.
 *
 * Side effect: the mapping is stored in nodes->map.
 */
term_t convert_bit_to_term(term_table_t *terms, node_table_t *nodes, bit_t b) {
  return map_bit_to_term(terms, nodes, b);
}

#endif
