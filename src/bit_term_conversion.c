/*
 * CONVERSION BETWEEN BIT AND TERM REPRESENTATIONS
 */

#include <assert.h>

#include "bit_term_conversions.h"


/*
 * Convert a boolean term t to a bit expression
 * - t must be a valid boolean term in the term table
 *
 * Side effect: if conversion for t is x, and x is not mapped to anything yet,
 * then map[x] is set to t in the node table.
 */
bit_t boolean_term_to_bit(term_table_t *terms, node_table_t *nodes, term_t t) {
  select_term_t *s;
  bit_t x;
  int32_t i;

  assert(good_term(table, t) && is_boolean_term(table, t));

  i = index_of(t);
  switch (table->kind[i]) {
  case CONSTANT_TERM:
    assert(i == bool_const);
    x = true_bit;
    break;

  case BIT_TERM:
    s = select_for_idx(table, i);
    x = node_table_alloc_select(nodes, s->idx, s->arg);
    break;

  default:
    x = node_table_alloc_var(table, pos_term(i));
    break;
  }

  // save the mapping x --> i in the node table
  assert(bit_is_pos(x));
  if (map_of_node(nodes, node_of_bit(x)) == -1) {
    set_map_of_node(nodes, node_of_bit(x), i);
  }

  // flip x's polarity if t has negative polarity
  x ^= polarity_of(t);

  return x;
}




