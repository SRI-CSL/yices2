/*
 * CONVERSION BETWEEN BIT AND TERM REPRESENTATIONS
 */

#include <assert.h>

#include "bit_term_conversion.h"


/*
 * Convert a boolean term t to a bit expression
 * - t must be a valid boolean term in the term table
 *
 * Side effect: if conversion for t is x, and x is not mapped to anything yet,
 * then map[x] is set to t in the node table.
 */
bit_t convert_term_to_bit(term_table_t *table, node_table_t *nodes, term_t t) {
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
    x = node_table_alloc_var(nodes, pos_term(i));
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



/*
 * Breadth-first node collection:
 * - store all the nodes whose map is -1 and are reachable from x in vector v
 * - stop exploring if v's map is non-negative (i.e., v is already mappd to a term)
 * - mark the visited nodes by setting map[v] = -2 
 */
static void collect_reachable_nodes(node_table_t *nodes, node_t x, ivector_t *v) {
  int32_t *map;
  uint32_t i;
  node_t y;

  ivector_reset(v);  
  map = nodes->map;
  if (map[x] == -1) {
    map[x] = -2;
    ivector_push(v, x);
  }

  i = 0;
  while (i < v->size) {
    x = v->data[i];
    if (is_nonleaf_node(nodes, x)) {
      y = node_of_bit(left_child_of_node(nodes, x));
      if (map[y] == -1) {
	map[y] = -2;
	ivector_push(v, y);
      }
      y = node_of_bit(right_child_of_node(nodes, x));
      if (map[y] == -1) {
	map[y] = -2;
	ivector_push(v, y);
      }
    }
    i ++;
  }
}


/*
 * Get the term mapped to bit b, assuming node_of_bit(b) is mapped to a term t
 * - if b has positive polarity, map_of(b) = t
 * - if b has negative polarity, map_of(b) = not t
 */
static inline term_t map_of_bit(node_table_t *nodes, bit_t b) {
  assert(map_of_node(nodes, node_of_bit(b)) >= 0);
  return map_of_node(nodes, node_of_bit(b)) ^ polarity_of(b);
}


/*
 * Given two bits b1 = c[0] and b2 = c[1], convert (or b1 b2) to a term
 * - both b1 and b2 must be already mapped ot terms
 */
static term_t make_or2(term_table_t *terms, node_table_t *nodes, bit_t *c) {
  term_t aux[2];

  aux[0] = map_of_bit(nodes, c[0]);
  aux[1] = map_of_bit(nodes, c[1]);

  assert(is_boolean_term(terms, aux[0]) && is_boolean_term(terms, aux[1]));
  return or_term(terms, 2, aux);
}


/*
 * Same thing for (xor c[0] c[1])
 */
static term_t make_xor2(term_table_t *terms, node_table_t *nodes, bit_t *c) {
  term_t aux[2];

  aux[0] = map_of_bit(nodes, c[0]);
  aux[1] = map_of_bit(nodes, c[1]);

  assert(is_boolean_term(terms, aux[0]) && is_boolean_term(terms, aux[1]));
  return xor_term(terms, 2, aux);
}




/*
 * Process all nodes in v in reverse order: map them all to a term
 * then empty v.
 */
static void map_nodes_to_terms(term_table_t *terms, node_table_t *nodes, ivector_t *v) { 
  int32_t *map;
  uint32_t i;
  node_t x;

  map = nodes->map;
  i = v->size;
  while (i > 0) {
    i --;
    x = v->data[i];
    assert(map[x] == -2);
    switch (node_kind(nodes, x)) {
    case UNUSED_NODE:
      assert(false);
      abort();
      break;

    case CONSTANT_NODE:
      // x is true
      map[x] = true_term;
      break;

    case VARIABLE_NODE:
      // x is (var t) for a boolean term t
      map[x] = var_of_node(nodes, x);
      break;

    case SELECT_NODE:
      // x is (select k t) for a bit vector term t
      map[x] = bit_term(terms, index_of_select_node(nodes, x), var_of_select_node(nodes, x));
      break;

    case OR_NODE:
      // x is (or b1 b2)
      map[x] = make_or2(terms, nodes, children_of_node(nodes, x));
      break;

    case XOR_NODE:
      // x is (xor b1 b2)
      map[x] = make_xor2(terms, nodes, children_of_node(nodes, x));
      break;
    }

    assert(is_boolean_term(terms, map[x]));
  }

  ivector_reset(v);
}



/*
 * Convert b (and all nodes reachable from b) to boolean terms
 * - b must be a valid bit expression in table 'nodes'
 * - new terms are created in table 'terms'
 * - use auxiliary vector 'queue' to store the nodes reachable from b
 *   (so the current content of queue is lost).
 *
 * The subgraph rooted at b is explored and all nodes reachable from b
 * are converted to boolean terms. No simplification or flattening is
 * applied.
 * 
 * Side effect: the mapping is stored in nodes->map.
 */
term_t convert_bit_to_term(term_table_t *terms, node_table_t *nodes, ivector_t *queue, bit_t b) {
  term_t t;

  collect_reachable_nodes(nodes, node_of_bit(b), queue);
  map_nodes_to_terms(terms, nodes, queue);
  t = map_of_bit(nodes, b);
  assert(is_boolean_term(terms, t));

  return t;
}
