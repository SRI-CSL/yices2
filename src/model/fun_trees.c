/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TREES USED TO BUILD MODELS IN THE FUNCTION/ARRAY SOLVER.
 */

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "model/fun_trees.h"


/*
 * Initialization
 */
void init_fun_tree(fun_tree_t *tree, pstore_t *pstore) {
  tree->root = NULL;
  tree->ftype = NULL;
  tree->pstore = pstore;

  init_objstore(&tree->store, sizeof(fun_node_t), FUN_TREE_BANK_SIZE);
  init_ivector(&tree->buffer, FUN_TREE_BUFFER_SIZE);
}


/*
 * Deletion
 */
void delete_fun_tree(fun_tree_t *tree) {
  tree->root = NULL;
  delete_objstore(&tree->store);
  delete_ivector(&tree->buffer);
}


/*
 * Empty the tree
 */
void reset_fun_tree(fun_tree_t *tree) {
  tree->root = NULL;
  tree->ftype = NULL;
  reset_objstore(&tree->store);
  ivector_reset(&tree->buffer);
}


/*
 * Allocate a new node
 * - nothing is initialized
 */
static inline fun_node_t *fun_tree_alloc_node(fun_tree_t *tree) {
  return (fun_node_t *) objstore_alloc(&tree->store);
}


/*
 * Create a new leaf node
 * - map = its map
 * - v = its value
 * - the next field is initialized to NULL
 */
static fun_node_t *fun_tree_make_leaf(fun_tree_t *tree, map_t *map, particle_t v) {
  fun_node_t *leaf;

  leaf = fun_tree_alloc_node(tree);
  leaf->index = null_particle;
  leaf->value = v;
  leaf->size = 1;
  leaf->next = NULL;
  leaf->u.map = map;

  return leaf;
}




#ifndef NDEBUG

/*
 * FOR DEBUGGING: CHECK THE SIZES
 */

/*
 * Add the size of all children of node p
 */
static uint32_t children_sizes(fun_node_t *p) {
  fun_node_t *c;
  uint32_t s;

  assert(p->index != null_particle);
  s = 0;
  c = p->u.child;
  while (c != NULL) {
    s += c->size;
    c = c->next;
  }
  return s;
}


/*
 * Check that the size of node n is locally consistent
 */
static bool size_locally_good(fun_node_t *n) {
  if (n->index == null_particle) {
    return n->size == 1;
  } else {
    return n->size == children_sizes(n);
  }
}


/*
 * Check that the sizes are all nodes reachable from n are correct
 */
static bool good_sizes(fun_node_t *n) {
  fun_node_t *c;

  if (n->index != null_particle) {
    // recursively check all children first
    c = n->u.child;
    while (c != NULL) {
      if (! good_sizes(c)) {
        return false;
      }
      c = c->next;
    }
  }

  // check n
  return size_locally_good(n);
}


/*
 * Check the whole tree
 */
static bool good_sizes_in_tree(fun_tree_t *tree) {
  return tree->root == NULL || good_sizes(tree->root);
}


#endif




/*
 * Search a list of nodes:
 * - list must be sorted in increasing order of values
 * - return the last node in the list whose value is <= v
 * - return NULL if all nodes in the list have a value > v
 */
static fun_node_t *search_list(fun_node_t *list, particle_t v) {
  fun_node_t *pre;

  pre = NULL;
  while (list != NULL && list->value <= v) {
    pre = list;
    list = list->next;
  }
  return pre;
}




/*
 * SIMPLE ADDITION
 */

/*
 * Check whether m2 and the current map m1 of node n are distinct,
 * if so add two children leaves to n, one for m1, the other for m2.
 * - v must contain the indices used on the path from the root to n
 * - return true if the split works (i.e., m1 and m2 are distinct)
 * - return false otherwise
 */
static bool split_leaf(fun_tree_t *tree, fun_node_t *n, map_t *m2, ivector_t *v) {
  map_t *m1;
  function_type_t *f;
  fun_node_t *left, *right;
  particle_t idx, a, b;

  assert(n->index == null_particle);  // n must be a leaf
  m1 = n->u.map;

  idx = disagreement_point(m1, m2);
  if (idx != null_particle) {
    /*
     * m1 and m2 disagree at idx
     */
    a = eval_map(m1, idx);
    b = eval_map(m2, idx);

  } else {
    /*
     * Check whether the default values are distinct
     */
    a = map_default_value(m1);
    b = map_default_value(m2);
    if (a != b) {
      // get an idx not used on the path to n or in the domain of m1 or m2
      collect_map_indices(m1, v);
      collect_map_indices(m2, v);

      f = tree->ftype;
      if (f->ndom == 1) {
        idx = get_distinct_particle(tree->pstore, f->domain[0], v->size, v->data);
      } else {
        idx = get_distinct_tuple(tree->pstore, f->ndom, f->domain, v->size, v->data);
      }

      if (idx == null_particle) {
        /*
         * this means that the domain is finite and all elements
         * in the domain occur on the path from the root to n
         * so the default values are irrelevant and the two maps are equal.
         */
        return false;
      }

    } else {
      // same default values: the maps are equal
      return false;
    }

  }

  /*
   * Split node n here
   */
  assert(a != b && idx != null_particle && a == eval_map(m1, idx) && b == eval_map(m2, idx));

  if (a < b) {
    left = fun_tree_make_leaf(tree, m1, a);
    right = fun_tree_make_leaf(tree, m2, b);
  } else {
    left = fun_tree_make_leaf(tree, m2, b);
    right = fun_tree_make_leaf(tree, m1, a);
  }

  // convert n to a non-leaf node of index idx
  // add left and right as its children
  n->index = idx;
  n->u.child = left;
  left->next = right;

  return true;

}


/*
 * Restore correct sizes if map m cannot be added.
 * Follow the path defined by m. For all nodes on that path,
 * reduce the size by one.
 */
static void restore_sizes(fun_tree_t *tree, map_t *m) {
  fun_node_t *n;
  particle_t idx, x;

  n = tree->root;

  for (;;) {
    assert(n != NULL && n->size > 0);

    n->size --;
    idx = n->index;
    if (idx == null_particle) {
      break;
    }
    x = eval_map(m, idx);
    n = search_list(n->u.child, x);
  }
}



/*
 * Attempt to add map m to tree. The addition succeeds if
 * m is distinct from all the other maps already in tree.
 * - tree->ftype must be set and m must be of that type.
 * - return true if the addition works, false otherwise
 */
bool fun_tree_add_map(fun_tree_t *tree, map_t *m) {
  fun_node_t *n, *new, *c;
  ivector_t *v;
  particle_t idx, x;

  assert(tree->ftype != NULL && map_default_value(m) != null_particle);

  n = tree->root;
  if (n == NULL) {
    tree->root = fun_tree_make_leaf(tree, m, null_particle);
    assert(good_sizes_in_tree(tree));
    return true;
  }

  // v: stores the indices on the path
  v = &tree->buffer;
  assert(v->size == 0);


  /*
   * Size update: if m is added successfully as a leaf N, the size counter
   * of all nodes from root to N (excluding N) must be incremented.
   * We do increment the counter on all nodes visited and fix it if the
   * addition fails.
   */
  n->size ++;


  /*
   * Loop invariant:
   * - n = current node, idx = its index
   * - m agrees with the path to n
   * - v = set of all indices on the path from the root to n
   */
  idx = n->index;
  while (idx != null_particle) {
    ivector_push(v, idx);
    x = eval_map(m, idx); // x == m[idx]
    assert(x != null_particle);

    c = search_list(n->u.child, x);
    if (c == NULL) {
      // add m in a new leaf, first child of n
      new = fun_tree_make_leaf(tree, m, x);
      new->next = n->u.child;
      n->u.child = new;
      goto done;
    } else if (c->value < x) {
      // add m in a new leaf, after child c
      new = fun_tree_make_leaf(tree, m, x);
      new->next = c->next;
      c->next = new;
      goto done;
    } else {
      assert(c->value == x);
      // continue with node c
      n = c;
      n->size ++;
      idx = n->index;
    }
  }

  /*
   * - n is a leaf node
   * - m agrees with the path from the root to n
   */
  if (! split_leaf(tree, n, m, v)) {
    // failed addition: n->u,map is equal to m
    restore_sizes(tree, m);
    assert(good_sizes_in_tree(tree));
    ivector_reset(v);
    return false;
  }

 done:
  assert(good_sizes_in_tree(tree));
  ivector_reset(v);
  return true;
}

