/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TREES USED TO BUILD MODELS IN THE FUNCTION/ARRAY SOLVER.
 */

/*
 * A tree stores a set of map objects and is used to ensure
 * that maps for distinct arrays are actually distinct.
 *
 * Each map object defines a mapping f from a domain D to a range
 * R. More precisely, the map lists the values of f on a finite subset
 * C of D, and a default value d is assumed for the rest of D.  The
 * array solver may assign identical mappings f1 and f2 to two array
 * variables that are distinct. In such a case, we can modify f1 and f2
 * and make them distinct as follows:
 * 1) find an new index i of D that's not in C
 * 2) find two objects a and b of R such that a != b
 * 3) add the mapping [i --> a] to f1
 *    add the mapping [i --> b] to f2
 *
 * This should always be feasible if the function solver is sound.
 *
 * To support the construction, we store maps in a tree:
 * - an internal node N is labeled by an index i of D
 * - the n children of N have distinct values v_1, ..., v_n of R
 * - each leaf node contains a unique map object f
 * - all maps in the tree have the same domain D and range R.
 *
 * Let N_0 be the root and N_k be a node of the tree. On the path
 * N_0 --> N_2 --> .... N_{k-1} --> N_k from the root to N_k, let
 * i_t = index of N_t and v_t = value of N_t. By construction, the
 * indices i_0, ..., i_{k-1} are all distinct; the path defines a
 * partial map h: [i_0 -> v_1, i_1 -> v_2, ..., i_{k-1} -> v_k].
 * Then a map object f is stored in the subtree rooted at N_k iff
 * if agrees with h at i_0, ..., i_{k-1}
 * (i.e., f(i_0) = v_1, f(i_1) = v2, ..., f(i_{k-1}) = v_k).
 *
 */

#ifndef __FUN_TREES_H
#define __FUN_TREES_H

#include "model/abstract_values.h"
#include "model/fun_maps.h"
#include "terms/types.h"
#include "utils/int_vectors.h"
#include "utils/object_stores.h"


/*
 * Node structure:
 * - index (either null_particle or an object of D)
 * - value (an object in R or null_particle for the root)
 * - size = number of maps stored in the subtree rooted at that node
 *   TODO: remove size. It's not used anymore.
 * - next = sibling
 * - child/map = either list of children or the map
 *
 * A node is a leaf if its index is null_particle.
 * Then map is a pointer to the map object stored in that leaf.
 *
 * If index is non-null, the node is an internal node.  Then child is
 * the list of it children. The list is sorted in increasing
 * order of values.
 */
typedef struct fun_node_s fun_node_t;

struct fun_node_s {
  particle_t index;
  particle_t value;
  uint32_t size;
  fun_node_t *next;
  union {
    fun_node_t *child;
    map_t *map;
  } u;
};


/*
 * Tree:
 * - root node (NULL if the tree is empty)
 * - pstore: store for creating new particles
 * - ftype: type descriptor = the type of all maps in the tree
 * - store: for allocating nodes
 * - auxiliary buffers for internal use
 */
typedef struct fun_tree_s {
  fun_node_t *root;
  pstore_t *pstore;
  function_type_t *ftype;
  object_store_t store;
  ivector_t path_indices;
  ivector_t buffer;
} fun_tree_t;


/*
 * For the store: number of nodes per bank
 */
#define FUN_TREE_BANK_SIZE 256

/*
 * Initial size of the internal buffer
 */
#define FUN_TREE_BUFFER_SIZE 10




/*
 * Initialize tree
 * - pstore = the particle store to use
 * - root is set to NULL
 * - ftype is NULL
 */
extern void init_fun_tree(fun_tree_t *tree, pstore_t *pstore);


/*
 * Delete tree: free all memory
 */
extern void delete_fun_tree(fun_tree_t *tree);


/*
 * Empty the tree:
 * - root and ftype are reset to NULL
 * - all nodes and leaves are deleted
 */
extern void reset_fun_tree(fun_tree_t *tree);


/*
 * Initialize the type to f
 * - the tree must be empty (i.e., tree->root == NULL)
 */
static inline void set_fun_tree_type(fun_tree_t *tree, function_type_t *f) {
  assert(tree->root == NULL && tree->ftype == NULL && f != NULL);
  tree->ftype = f;
}



/*
 * Attempt to add map m to tree. The addition succeeds if
 * m is distinct from all the other maps already in tree.
 * - tree->ftype must be set and m must be of that type.
 * - return true if the addition works, false otherwise
 */
extern bool fun_tree_add_map(fun_tree_t *tree, map_t *m);


#endif /* __FUN_TREES_H */
