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
 * XOR/OR/NOT graph used to represent bit-vector expressions
 *
 * We need a new representation to replace BDDs. The BDDs blow
 * up on several benchmarks.
 *
 * Update: January 29, 2009.
 * - Tests show that flattening the nodes is dangerous. It can consume
 *   a lot of memory and the node table blows up on one QF_BV benchmark.
 * - Since flattening does not work, it makes sense to simplify the
 *   data structures. All OR and XOR nodes are now binary nodes.
 *
 * April 2010:
 * - adjusted this module to the new term representations
 * - added a new node type (select k i) for bit-select
 * - removed the vsets
 */

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "terms/bit_expr.h"
#include "utils/hash_functions.h"
#include "utils/int_array_sort.h"
#include "utils/memalloc.h"


/*
 * Initialize a node table (empty)
 * - n = initial size
 */
static void alloc_node_table(node_table_t *table, uint32_t n) {
  if (n == 0) {
    n = DEF_NODE_TABLE_SIZE;
  }

  static const indexed_table_vtbl_t vtbl = {
    .elem_size = sizeof(node_desc_t),
    .max_elems = MAX_NODE_TABLE_SIZE,
    .extend = NULL
  };

  indexed_table_init(&table->nodes, n, &vtbl);

  table->ref_counter = 0;

  init_ivector(&table->aux_buffer, 0);
  init_int_htbl(&table->htbl, 0);
}


/*
 * Allocate a node id
 * - set map[i] to the default (i.e., -1)
 */
static node_t allocate_node_id(node_table_t *table, uint8_t kind) {
  node_t i = indexed_table_alloc(&table->nodes);
  node_desc_t *n = node_table_elem(table, i);

  n->kind = kind;
  n->map = -1;

  return i;
}



/*
 * Create the constant node:
 * - this must be done first.
 */
static node_t build_constant_node(node_table_t *table) {
  node_t i;

  i = allocate_node_id(table, CONSTANT_NODE);
  assert(i == constant_node);

  bit_t *c = node_table_elem(table, i)->c;
  c[0] = c[1] = null_bit;

  return i;
}


/*
 * Build a variable node mapped to x
 */
static node_t new_variable_node(node_table_t *table, int32_t x) {
  node_t i;

  i = allocate_node_id(table, VARIABLE_NODE);
  node_table_elem(table, i)->var = x;
  
  return i;
}


/*
 * Build a select node (k, x)
 */
static node_t new_select_node(node_table_t *table, uint32_t k, int32_t x) {
  node_t i;

  i = allocate_node_id(table, SELECT_NODE);

  select_node_t *s = &node_table_elem(table, i)->sel;
  s->index = k;
  s->var = x;

  return i;
}


/*
 * Build a binary node (op a b)
 * - op must be OR_NODE or XOR_NODE
 */
static node_t new_binary_node(node_table_t *table, node_kind_t op, bit_t a, bit_t b) {
  node_t i;

  assert(op == OR_NODE || op == XOR_NODE);

  i = allocate_node_id(table, op);

  bit_t *c = node_table_elem(table, i)->c;
  c[0] = a;
  c[1] = b;

  return i;
}



/*
 * HASH CONSING
 */

/*
 * Hash codes
 */
static inline uint32_t hash_var(int32_t x) {
  return jenkins_hash_int32(x);
}

static inline uint32_t hash_select(uint32_t k, int32_t x) {
  return jenkins_hash_pair((int32_t) k, x, 0x13dae100);
}

static inline uint32_t hash_or(bit_t a, bit_t b) {
  return jenkins_hash_pair(a, b, 0x1298abef);
}

static inline uint32_t hash_xor(bit_t a, bit_t b) {
  return jenkins_hash_pair(a, b, 0xabed31fd);
}


/*
 * Structure for interfacing with int_hash_table
 * - node_hobj_t is used for both XOR and OR nodes
 */
typedef struct node_hobj_s {
  int_hobj_t m;
  node_table_t *tbl;
  bit_t child[2];
} node_hobj_t;

typedef struct var_node_hobj_s {
  int_hobj_t m;
  node_table_t *tbl;
  int32_t var;
} var_node_hobj_t;

typedef struct select_node_hobj_s {
  int_hobj_t m;
  node_table_t *tbl;
  uint32_t index;
  int32_t var;
} select_node_hobj_t;



/*
 * VAR Nodes
 */
static uint32_t hash_var_node(var_node_hobj_t *p) {
  return hash_var(p->var);
}

static bool eq_var_node(var_node_hobj_t *p, node_t i) {
  node_desc_t *node = node_table_elem(p->tbl, i);

  return node->kind == VARIABLE_NODE && node->var == p->var;
}

static node_t build_var_node(var_node_hobj_t *p) {
  return new_variable_node(p->tbl, p->var);
}

static node_t get_var_node(node_table_t *table, int32_t x) {
  var_node_hobj_t var_node_hobj;

  var_node_hobj.m.hash = (hobj_hash_t) hash_var_node;
  var_node_hobj.m.eq = (hobj_eq_t) eq_var_node;
  var_node_hobj.m.build = (hobj_build_t) build_var_node;

  var_node_hobj.tbl = table;
  var_node_hobj.var = x;
  return int_htbl_get_obj(&table->htbl, &var_node_hobj.m);
}


/*
 * SELECT Nodes
 */
static uint32_t hash_select_node(select_node_hobj_t *p) {
  return hash_select(p->index, p->var);
}

static bool eq_select_node(select_node_hobj_t *p, node_t i) {
  node_desc_t *node = node_table_elem(p->tbl, i);

  return node->kind == SELECT_NODE &&
    node->sel.index == p->index &&
    node->sel.var == p->var;
}

static node_t build_select_node(select_node_hobj_t *p) {
  return new_select_node(p->tbl, p->index, p->var);
}

static node_t get_select_node(node_table_t *table, uint32_t k, int32_t x) {
  select_node_hobj_t select_node_hobj;

  select_node_hobj.m.hash = (hobj_hash_t) hash_select_node;
  select_node_hobj.m.eq = (hobj_eq_t) eq_select_node;
  select_node_hobj.m.build = (hobj_build_t) build_select_node;
  select_node_hobj.tbl = table;
  select_node_hobj.index = k;
  select_node_hobj.var = x;
  return int_htbl_get_obj(&table->htbl, &select_node_hobj.m);
}


/*
 * OR Nodes
 */
static uint32_t hash_or_node(node_hobj_t *p) {
  return hash_or(p->child[0], p->child[1]);
}

static bool eq_or_node(node_hobj_t *p, node_t i) {
  node_desc_t *node = node_table_elem(p->tbl, i);

  return node->kind == OR_NODE &&
    node->c[0] == p->child[0] &&
    node->c[1] == p->child[1];
}

static node_t build_or_node(node_hobj_t *p) {
  return new_binary_node(p->tbl, OR_NODE, p->child[0], p->child[1]);
}

static node_t get_or_node(node_table_t *table, bit_t a, bit_t b) {
  node_hobj_t or_node_hobj;

  or_node_hobj.m.hash = (hobj_hash_t) hash_or_node;
  or_node_hobj.m.eq = (hobj_eq_t) eq_or_node;
  or_node_hobj.m.build = (hobj_build_t) build_or_node;
  or_node_hobj.tbl = table;
  or_node_hobj.child[0] = a;
  or_node_hobj.child[1] = b;
  return int_htbl_get_obj(&table->htbl, &or_node_hobj.m);
}


/*
 * XOR Nodes
 */
static uint32_t hash_xor_node(node_hobj_t *p) {
  return hash_xor(p->child[0], p->child[1]);
}

static bool eq_xor_node(node_hobj_t *p, node_t i) {
  node_desc_t *node = node_table_elem(p->tbl, i);

  return node->kind == XOR_NODE &&
    node->c[0] == p->child[0] &&
    node->c[1] == p->child[1];
}

static node_t build_xor_node(node_hobj_t *p) {
  return new_binary_node(p->tbl, XOR_NODE, p->child[0], p->child[1]);
}

static node_t get_xor_node(node_table_t *table, bit_t a, bit_t b) {
  node_hobj_t xor_node_hobj;

  xor_node_hobj.m.hash = (hobj_hash_t) hash_xor_node;
  xor_node_hobj.m.eq = (hobj_eq_t) eq_xor_node;
  xor_node_hobj.m.build = (hobj_build_t) build_xor_node;
  xor_node_hobj.tbl = table;
  xor_node_hobj.child[0] = a;
  xor_node_hobj.child[1] = b;
  return int_htbl_get_obj(&table->htbl, &xor_node_hobj.m);
}




/*****************************
 *  INITIALIZATION/DELETION  *
 ****************************/

/*
 * Global initialization: allocate and create the constant node
 * - n = initial table
 */
void init_node_table(node_table_t *table, uint32_t n) {
  alloc_node_table(table, n);
  (void) build_constant_node(table);
}


/*
 * Delete all nodes and the table
 */
void delete_node_table(node_table_t *table) {
  delete_ivector(&table->aux_buffer);
  delete_int_htbl(&table->htbl);
  indexed_table_destroy(&table->nodes);
}


/*
 * Reset: empty the table
 */
void reset_node_table(node_table_t *table) {
  assert(table->ref_counter == 0);

  indexed_table_clear(&table->nodes);
  table->nodes.nelems = 1; // keep the constant node
  assert(node_table_elem(table, 0)->kind == CONSTANT_NODE);

  ivector_reset(&table->aux_buffer);
  reset_int_htbl(&table->htbl);
}



/*
 * Garbage collection: decrement the reference counter
 * and reset the table if the ref count is zero
 */
void node_table_decref(node_table_t *table) {
  assert(table->ref_counter > 0);
  table->ref_counter --;
  if (table->ref_counter == 0) {
    reset_node_table(table);
  }
}



/********************************
 *  SUPPORT FOR SIMPLIFICATION  *
 *******************************/

/*
 * Label that describes the shape of a bit expression x
 *   (or a b) --> POS_OR
 *  ~(or a b) --> NEG_OR
 *  (xor a b) --> POS_XOR
 * ~(xor a b) --> NEG_XOR
 *     else   --> ATOMIC or ERROR
 */
typedef enum bit_shape {
  POS_OR,
  NEG_OR,
  POS_XOR,
  NEG_XOR,
  ATOMIC,
  ERROR,
} bit_shape_t;


/*
 * Table: given k = type_kind(node_of(x)) << sign_of(x)
 * then shape[k] = its shape code
 * - kind is one of UNUSED, CONSTANT, VARIABLE, OR_NODE, XOR_NODE
 * - sign is 0 or 1 (0 means positive, 1 means negative)
 */
static const bit_shape_t shape[12] = {
  ERROR,    // UNUSED, POSITIVE
  ERROR,    // UNUSED, NEGATIVE
  ATOMIC,   // CONSTANT, POSITIVE (true)
  ATOMIC,   // CONSTANT, NEGATIVE (false)
  ATOMIC,   // VARIABLE, POSITIVE
  ATOMIC,   // VARIABLE, NEGATIVE
  ATOMIC,   // SELECT, POSITIVE
  ATOMIC,   // SELECT, NEGATIVE
  POS_OR,   // OR, POSITIVE
  NEG_OR,   // OR, NEGATIVE
  POS_XOR,  // XOR, POSITIVE
  NEG_XOR,  // XOR, NEGATIE
};


/*
 * Compute the bit_shape of x
 */
static inline bit_shape_t shape_of_bit(node_table_t *table, bit_t x) {
  int32_t k;

  k = (node_kind(table, node_of_bit(x)) << 1) | sign_of_bit(x);
  assert(0 <= k && k < 12);
  return shape[k];
}



/*
 * Combination of two non-atomic shape labels s1 and s2
 */
typedef enum pair_shape {
  POS_OR_POS_OR,
  POS_OR_NEG_OR,
  POS_OR_POS_XOR,
  POS_OR_NEG_XOR,
  NEG_OR_POS_OR,
  NEG_OR_NEG_OR,
  NEG_OR_POS_XOR,
  NEG_OR_NEG_XOR,
  POS_XOR_POS_OR,
  POS_XOR_NEG_OR,
  POS_XOR_POS_XOR,
  POS_XOR_NEG_XOR,
  NEG_XOR_POS_OR,
  NEG_XOR_NEG_OR,
  NEG_XOR_POS_XOR,
  NEG_XOR_NEG_XOR,
} pair_shape_t;


/*
 * Compute the combination for s1 and s2
 */
static inline pair_shape_t combine_shapes(bit_shape_t s1, bit_shape_t s2) {
  assert(0 <= s1 && s1 <= NEG_XOR && 0 <= s2 && s2 <= NEG_XOR);
  return (pair_shape_t) ((s1 << 2) | s2);
}



/*******************
 *  CONSTRUCTORS   *
 ******************/

/*
 * Get node (VAR x)
 */
bit_t node_table_alloc_var(node_table_t *table, int32_t x) {
  return pos_bit(get_var_node(table, x));
}


/*
 * Get node (SELECT k x)
 */
bit_t node_table_alloc_select(node_table_t *table, uint32_t k, int32_t x) {
  return pos_bit(get_select_node(table, k, x));
}


/*
 * Normalize then return an expression equivalent to (or a b).
 * - ensure left child < right child
 * - intended to be used when (or a b) cannot be simplified
 */
static bit_t make_or2(node_table_t *table, bit_t a, bit_t b) {
  bit_t aux;

  assert(node_of_bit(a) != node_of_bit(b) && ! bit_is_const(a) && ! bit_is_const(b));

  if (a > b) {
    aux = a; a = b; b = aux;
  }
  return pos_bit(get_or_node(table, a, b));
}


/*
 * Normalize then build an expression equivalent to (xor a b)
 * - ensure left child < right child
 * - ensure both children are positive
 * - intended to be used when (xor a b) cannot be simplified
 */
static bit_t make_xor2(node_table_t *table, bit_t a, bit_t b) {
  uint32_t sign;
  bit_t aux;

  /*
   * Ensure child[0] < child[1] and children of xor
   * have positive polarity
   */
  sign = sign_of_bit(a) ^ sign_of_bit(b);   // sign of the result
  a &= ~1;  // force positive polarity (clear lower bit)
  b &= ~1;

  assert(bit_is_pos(a) && bit_is_pos(b) && a != b &&
         a != true_bit && b != true_bit);
  if (a > b) {
    aux = a; a = b; b = aux;
  }

  return mk_bit(get_xor_node(table, a, b), sign);
}






/*
 * Build (OR a b)
 * - baseline version: apply only the most basic simplifications
 */
bit_t bit_or2(node_table_t *table, bit_t a, bit_t b) {
  /*
   * (or a true) --> true
   * (or true b) --> true
   * (or a ~a)   --> true
   *
   * (or a false) --> a
   * (or false b) --> b
   * (or a a)     --> a
   */
  if (a == true_bit) return true_bit;
  if (b == true_bit) return true_bit;
  if (a == false_bit) return b;
  if (b == false_bit) return a;
  if (a == b) return a;
  if (a == bit_not(b)) return true_bit;

  return make_or2(table, a, b);
}


/*
 * Build (OR a b) using more simplification rules
 * - apply rules that simplify (OR a b) to true, a, ~a, b, or ~b
 *   (i.e., don't create a new node)
 * - assumptions used in the code:
 *   a and b are normalized so we have a0 < a1 and b0 < b1
 *   children of xor have positive polarity
 */
bit_t bit_or2simplify(node_table_t *table, bit_t a, bit_t b) {
  node_t na, nb;
  bit_t a0, a1;
  bit_t b0, b1;
  bit_shape_t a_shape, b_shape;

  /*
   * (or a true) --> true
   * (or true b) --> true
   * (or a ~a)   --> true
   *
   * (or a false) --> a
   * (or false b) --> b
   * (or a a)     --> a
   */
  if (a == true_bit) return true_bit;
  if (b == true_bit) return true_bit;
  if (a == false_bit) return b;
  if (b == false_bit) return a;
  if (a == b) return a;
  if (a == bit_not(b)) return true_bit;

  // Stop GCC warning
  a0 = null_bit;
  a1 = null_bit;
  b0 = null_bit;
  b1 = null_bit;

  /*
   * Simplifications based on b + shape and children of a
   */
  a_shape = shape_of_bit(table, a);
  na = node_of_bit(a);
  if (is_nonleaf_node(table, na)) {
    a0 = left_child_of_node(table, na);
    a1 = right_child_of_node(table, na);
    switch (a_shape) {
    case POS_OR:
      /*
       * (or (or a0 a1) a0)  --> (or a0 a1)
       * (or (or a0 a1) a1)  --> (or a0 a1)
       * (or (or a0 a1) ~a0) --> true
       * (or (or a0 a1) ~a1) --> true
       */
      if (b == a0 || b == a1) return a;
      if (opposite_bits(b, a0) || opposite_bits(b, a1)) return true_bit;
      break;
    case NEG_OR:
      /*
       * (or ~(or a0 a1) ~a0) --> ~a0
       * (or ~(or a0 a1) ~a1) --> ~a1
       */
      if (opposite_bits(b, a0) || opposite_bits(b, a1)) return b;
      break;
    case POS_XOR:
    case NEG_XOR:
      // nothing for now
      break;
    default:
      assert(false);
      break;
    }
  }

  /*
   * Symmetric rules: a + shape and children of b
   */
  b_shape = shape_of_bit(table, b);
  nb = node_of_bit(b);
  if (is_nonleaf_node(table, nb)) {
    b0 = left_child_of_node(table, nb);
    b1 = right_child_of_node(table, nb);
    switch (b_shape) {
    case POS_OR:
      /*
       * (or b0 (or b0 b1))  --> (or b0 b1)
       * (or b1 (or b0 b1))  --> (or b0 b1)
       * (or ~b0 (or b0 b1)) --> true
       * (or ~b1 (or b0 b1)) --> true
       */
      if (a == b0 || a == b1) return b;
      if (opposite_bits(a, b0) || opposite_bits(a, b1)) return true_bit;
      break;
    case NEG_OR:
      /*
       * (or ~b0 ~(or b0 b1)) --> ~b0
       * (or ~b1 ~(or b0 b1)) --> ~b1
       */
      if (opposite_bits(a, b0) || opposite_bits(a, b1)) return a;
      break;
    case POS_XOR:
    case NEG_XOR:
      break;
    default:
      assert(false);
      break;
    }
  }

  /*
   * Children of a + children of b
   */
  if (is_nonleaf_node(table, na) && is_nonleaf_node(table, nb)) {
    assert(a0 == left_child_of_node(table, na) && a1 == right_child_of_node(table, na) &&
           b0 == left_child_of_node(table, nb) && b1 == right_child_of_node(table, nb));

    switch (combine_shapes(a_shape, b_shape)) {
    case POS_OR_POS_OR:
      /*
       * (or (or a0 a1) (or ~a0 b1)) --> true
       * (or (or a0 a1) (or b0 ~a0)) --> true
       * (or (or a0 a1) (or ~a1 b1)) --> true
       * (or (or a0 a1) (or b0 ~a1)) --> true
       */
      if (opposite_bits(a0, b0) || opposite_bits(a0, b1) ||
          opposite_bits(a1, b0) || opposite_bits(a1, b1))
        return true_bit;
      break;

    case POS_OR_NEG_OR:
      /*
       * (or (or a0 a1) ~(or ~a0 b1))  --> (or a0 a1)
       * (or (or a0 a1) ~(or b0 ~a0))  --> (or a0 a1)
       * (or (or a0 a1) ~(or ~a1 b1))  --> (or a0 a1)
       * (or (or a0 a1) ~(or b0 ~a1))  --> (or a0 a1)
       */
      if (opposite_bits(a0, b0) || opposite_bits(a0, b1) ||
          opposite_bits(a1, b0) || opposite_bits(a1, b1))
        return a;
      break;
    case NEG_OR_POS_OR:
      /*
       * (or ~(or ~b0 a1) (or b0 b1))  --> (or b0 b1)
       * (or ~(or a0 ~b0) (or b0 b1))  --> (or b0 b1)
       * (or ~(or ~b1 a1) (or b0 b1))  --> (or b0 b1)
       * (or ~(or a0 ~b1) (or b0 b1))  --> (or b0 b1)
       */
      if (opposite_bits(a0, b0) || opposite_bits(a0, b1) ||
          opposite_bits(a1, b0) || opposite_bits(a1, b1))
        return b;
      break;

    case POS_OR_NEG_XOR:
      /*
       * We use the equality ~(xor b0 b1) == (xor ~b0 b1) and fall through
       */
      b0 ^= 1; // flip sign bit
    case POS_OR_POS_XOR:
      /*
       * (or (or a0 a1) (xor a0 a1))   --> (or a0 a1)
       * (or (or a0 a1) (xor ~a0 a1))  --> true
       * (or (or a0 a1) (xor a0 ~a1))  --> true
       * (or (or a0 a1) (xor ~a0 ~a1)) --> (or a0 a1)
       */
      if ((opposite_bits(a0, b0) && a1 == b1) || (a0 == b0 && opposite_bits(a1, b1)))
        return true_bit;
      if ((a0 == b0 && a1 == b1) || (opposite_bits(a0, b0) && opposite_bits(a1, b1)))
        return a;
      break;

    case NEG_XOR_POS_OR:
      /*
       * Rewrite ~(xor a0 a1) to (xor ~a0 a1) and fall through
       */
      a0 ^= 1; // flip sign bit
    case POS_XOR_POS_OR:
      /*
       * (or (xor b0 b1) (or b0 b1))   --> (or b0 b1)
       * (or (xor ~b0 b1) (or b0 b1))  --> true
       * (or (xor b0 ~b1) (or b0 b1))  --> true
       * (or (xor ~b0 ~b1) (or b0 b1)) --> (or b0 b1)
       */
      if ((opposite_bits(a0, b0) && a1 == b1) || (a0 == b0 && opposite_bits(a1, b1)))
        return true_bit;
      if ((a0 == b0 && a1 == b1) || (opposite_bits(a0, b0) && opposite_bits(a1, b1)))
        return b;
      break;

    case NEG_OR_NEG_OR:
      /*
       * (or ~(or a0 a1) ~(or ~a0 a1))  --> ~a1
       * (or ~(or a0 a1) ~(or a0 ~a1))  --> ~a0
       *
       * test: 2010/02/04
       * (or ~(or a0 a1) ~(or ~a0 ~a1)) --> ~(xor a0 a1)
       */
      if (opposite_bits(a0, b0) && a1 == b1)
        return bit_not(a1);
      if (a0 == b0 && opposite_bits(a1, b1))
        return bit_not(a0);
      // test rule: disabled for now
      //      if ((opposite_bits(a0, b0) && opposite_bits(a1, b1)) ||
      //          (opposite_bits(a0, b1) && opposite_bits(a1, b0)))
      //        return bit_not(bit_xor2(table, a0, a1));
      break;

    case NEG_OR_NEG_XOR:
      /*
       * Rewrite ~(xor b0 b1) to (xor ~b0 b1) and fall through
       */
      b0 ^= 1;
    case NEG_OR_POS_XOR:
      /*
       * (or ~(or a0 a1) (xor ~a0 a1))  --> (xor ~a0 a1)
       * (or ~(or a0 a1) (xor a0 ~a1))  --> (xor a0 ~a1)
       */
      if ((opposite_bits(a0, b0) && a1 == b1) || (a0 == b0 && opposite_bits(a1, b1)))
        return b;
      break;

    case NEG_XOR_NEG_OR:
      /*
       * Rewrite ~(xor a0 a1) to (xor ~a0 b1) and fall through
       */
      a0 ^= 1;
    case POS_XOR_NEG_OR:
      /*
       * (or (xor a0 a1) ~(or ~a0 a1))  --> (xor a0 a1)
       * (or (xor a0 a1) ~(or a0 ~a1))  --> (xor a0 a1)
       */
      if ((opposite_bits(a0, b0) && a1 == b1) || (a0 == b0 && opposite_bits(a1, b1)))
        return a;
      break;

    case POS_XOR_POS_XOR:
    case NEG_XOR_NEG_XOR:
    case POS_XOR_NEG_XOR:
    case NEG_XOR_POS_XOR:
      // nothing
      break;
    }
  }


  return make_or2(table, a, b);
}







/*
 * Build (XOR a b)
 * - baseline version: just use basic simplification rules
 */
bit_t bit_xor2(node_table_t *table, bit_t a, bit_t b) {
  /*
   * (xor true b)  --> ~b
   * (xor a true)  --> ~a
   * (xor false b) --> b
   * (xor a false) --> a
   * (xor a a)     --> false
   * (xor a ~a)    --> true
   */
  if (a == true_bit) return bit_not(b);
  if (b == true_bit) return bit_not(a);
  if (a == false_bit) return b;
  if (b == false_bit) return a;
  if (a == b) return false_bit;
  if (a == bit_not(b)) return true_bit;

  return make_xor2(table, a, b);
}


/*
 * Build (XOR a b)
 * - apply simplification rules that don't create a new node
 */
bit_t bit_xor2simplify(node_table_t *table, bit_t a, bit_t b) {
  node_t na, nb;
  bit_t a0, a1;
  bit_t b0, b1;
  bit_shape_t a_shape, b_shape;
  uint32_t sign;
  bit_t aux;

  /*
   * (xor true b)  --> ~b
   * (xor a true)  --> ~a
   * (xor false b) --> b
   * (xor a false) --> a
   * (xor a a)     --> false
   * (xor a ~a)    --> true
   */
  if (a == true_bit) return bit_not(b);
  if (b == true_bit) return bit_not(a);
  if (a == false_bit) return b;
  if (b == false_bit) return a;
  if (a == b) return false_bit;
  if (a == bit_not(b)) return true_bit;

  // Stop GCC warning
  a0 = null_bit;
  a1 = null_bit;
  b0 = null_bit;
  b1 = null_bit;

  // make a and b positive, keep sign
  sign = sign_of_bit(a) ^ sign_of_bit(b);
  a &= ~1;
  b &= ~1;

  a_shape = shape_of_bit(table, a);
  na = node_of_bit(a);
  if (is_nonleaf_node(table, na)) {
    assert(a_shape == POS_OR || a_shape == POS_XOR);
    a0 = left_child_of_node(table, na);
    a1 = right_child_of_node(table, na);
    if (a_shape == POS_XOR) {
      /*
       * (xor (xor a0 a1) a0)  --> a1
       * (xor (xor a0 a1) a1)  --> a0
       * (xor (xor a0 a1) ~a0) --> ~a1
       * (xor (xor a0 a1) ~a1) --> ~a0
       */
      if (b == a0) return sign ^ a1;
      if (b == a1) return sign ^ a0;
      // These rules can't match: b, a0, and a1 all have positive sign
      //      if (opposite_bits(b, a0)) return sign ^ bit_not(a1);
      //      if (opposite_bits(b, a1)) return sign ^ bit_not(a0);
    }
  }

  b_shape = shape_of_bit(table, b);
  nb = node_of_bit(b);
  if (is_nonleaf_node(table, nb)) {
    assert(b_shape == POS_OR || b_shape == POS_XOR);
    b0 = left_child_of_node(table, nb);
    b1 = right_child_of_node(table, nb);
    if (b_shape == POS_XOR) {
      /*
       * (xor b0 (xor b0 b1))  --> b1
       * (xor b1 (xor b0 b1))  --> b0
       * (xor ~b0 (xor b0 b1)) --> ~b1
       * (xor ~b1 (xor b0 b1)) --> ~b0
       */
      if (a == b0) return sign ^ b1;
      if (a == b1) return sign ^ b0;
      // These rules can't match: b, a0, and a1 all have positive sign
      //      if (opposite_bits(a, b0)) return sign ^ bit_not(b1);
      //      if (opposite_bits(a, b1)) return sign ^ bit_not(b0);
    }
  }


  if (is_nonleaf_node(table, na) && is_nonleaf_node(table, nb)) {
    assert(a0 == left_child_of_node(table, na) && a1 == right_child_of_node(table, na) &&
           b0 == left_child_of_node(table, nb) && b1 == right_child_of_node(table, nb));

    if (combine_shapes(a_shape, b_shape) == POS_OR_POS_OR ) {
      /*
       * (xor (or a0 a1) (or ~a0 a1))  --> ~a1
       * (xor (or a0 a1) (or a0 ~a1))  --> ~a0
       */
      if (opposite_bits(a0, b0) && a1 == b1) return sign ^ bit_not(a1);
      if (a0 == b0 && opposite_bits(a1, b1)) return sign ^ bit_not(a0);
    }
  }

  // normalize
  if (a > b) {
    aux = a; a = b; b = aux;
  }

  return mk_bit(get_xor_node(table, a, b), sign);
}






/***************************
 *   N-ARY CONSTRUCTORS    *
 **************************/

/*
 * Build (OR a[0] .... a[n-1])
 * - no simplifications
 * - build a balanced tree
 */
static bit_t make_or(node_table_t *table, uint32_t n, bit_t *a) {
  uint32_t h;
  bit_t left, right;

  assert(n > 0);

  if (n == 1) {
    return a[0];
  } else if (n == 2) {
    left = a[0];
    right = a[1];
  } else {
    h = n/2;
    left = make_or(table, h, a);        // (OR a[0] ... a[h-1])
    right = make_or(table, n-h, a+h);   // (OR a[h] ... a[n-1])
  }

  return make_or2(table, left, right);
}



/*
 * Build (OR a[0] ... a[n-1]) where a = v->data, n = v->size
 * - none of a[0] ... a[n-1] is a constant
 */
static bit_t bit_or_aux(node_table_t *table, ivector_t *v) {
  bit_t *a;
  bit_t b, c;
  uint32_t i, j, n;

  a = v->data;
  n = v->size;
  if (n == 0) {
    return false_bit;
  } else if (n == 1) {
    return v->data[0];
  }

  /*
   * Sort, remove duplicates, check for complementary bits
   */
  int_array_sort(a, n);
  b = a[0];
  j = 1;
  for (i=1; i<n; i++) {
    c = a[i];
    if (c != b) {
      if (c == bit_not(b)) {
        return true_bit;
      }
      a[j++] = c;
      b = c;
    }
  }

  if (j == 1) return a[0];

  return make_or(table, j, a);
}



/*
 * Simplify (OR a[0] ... a[n-1]) and return the corresponding
 * bit index
 */
bit_t bit_or(node_table_t *table, bit_t *a, uint32_t n) {
  ivector_t *v;
  bit_t b;
  uint32_t i;

  v = &table->aux_buffer;
  ivector_reset(v);

  /*
   * If any bit is true return true
   * If a[i] is false skip it
   * Otherwise, add a[i] to v
   */
  for (i=0; i<n; i++) {
    b = a[i];
    if (b == true_bit) {
      return true_bit;
    } else if (b != false_bit) {
      ivector_push(v, b);
    }
  }

  return bit_or_aux(table, v);
}



/*
 * Simplify (AND a[0] ... a[n-1]) and return the corresponding bit index
 */
bit_t bit_and(node_table_t *table, bit_t *a, uint32_t n) {
  ivector_t *v;
  bit_t b;
  uint32_t i;

  v = &table->aux_buffer;
  ivector_reset(v);

  /*
   * Copy (not a[i]) into v
   * - skip a[i] if it's true
   * - return false if a[i] is false
   */
  for (i=0; i<n; i++) {
    b = a[i];
    if (b == false_bit) {
      return false_bit;
    } else if (b != true_bit) {
      ivector_push(v, bit_not(b));
    }
  }

  return bit_not(bit_or_aux(table, v));
}




/*
 * Build (XOR a[0] .... a[n-1])
 * - no simplifications
 * - build a balanced tree
 */
static bit_t make_xor(node_table_t *table, uint32_t n, bit_t *a) {
  uint32_t h;
  bit_t left, right, aux;

  assert(n > 0);

  if (n == 1) {
    return a[0];
  } else if (n == 2) {
    left = a[0];
    right = a[1];
  } else {
    h = n/2;
    left = make_xor(table, h, a);       // (XOR a[0] ... a[h-1])
    right = make_xor(table, n-h, a+h);  // (XOR a[h] ... a[n-1])
  }

  if (left > right) {
    aux = left; left = right; right = aux;
  }

  return pos_bit(get_xor_node(table, left, right));
}




/*
 * Simplify (XOR a[0] ... a[n-1]) and return the corresponding bit index
 */
bit_t bit_xor(node_table_t *table, bit_t *a, uint32_t n) {
  ivector_t *v;
  bit_t b;
  uint32_t sign, i, j;

  v = &table->aux_buffer;
  ivector_reset(v);

  /*
   * Remove all constant and negative bits
   */
  sign = 0;
  for (i=0; i<n; i++) {
    b = a[i];
    if (b == true_bit) {
      // flip sign
      sign ^= 1;
    } else if (b != false_bit) {
      // if b is (not b0), flip sign and add b0 to v
      sign ^= sign_of_bit(b);
      b &= ~1; // force sign = 0 (low-order bit)
      ivector_push(v, b);
    }
  }

  n = v->size;
  a = v->data;
  j = 0;
  if (n > 0) {
    // remove the duplicates: (XOR b b) == false_bit
    int_array_sort(v->data, n);
    i = 0;
    while (i<n-1) {
      b = a[i];
      assert(bit_is_pos(b));
      if (b == a[i+1]) {
        i += 2;
      } else {
        a[j++] = b;
        i ++;
      }
    }
    if (i == n-1) {
      assert(bit_is_pos(a[i]));
      a[j++] = a[i];
    }
    ivector_shrink(v, j);
  }

  /*
   * The result is sign XOR ( a[0] XOR ... XOR a[n-1] )
   * (where sign is 0 or 1)
   */
  if (j == 0) return sign ^ false_bit;
  if (j == 1) return sign ^ a[0];
  return sign ^ make_xor(table, j, a);
}
