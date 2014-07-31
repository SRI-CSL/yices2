/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * INCREMENTAL FORM OF THE FLOYD-WARSHALL ALGORITHM,
 * ONLY FOR REAL-DIFFERENCE LOGIC.
 */

/*
 * Most of the algorithms and data structures are copied from
 * idl_floyd_warshall. The main difference is the use of
 * rational constants as edge labels.
 */

/*
 * Graph representation
 * - edges are stored in a stack (added and removed in FIFO order)
 * - each edge has source and destination vertices and a cost of the form (a + k delta)
 * - edges are indexed from 0 to n-1
 * - edge 0 is not really an edge. It's used as a mark.
 *
 * Matrix:
 * - for each pair of vertices (x, y), we maintain the distance from x to y and
 *   edge index M[x,y].id
 * - for each vertex x, M[x, x].id = 0 and M[x, x].dist = 0
 * - if there's no path from x to y, we set M[x, y] = null_edge (-1)
 * - if there's a path from x to y then M[x, y].id is an index between 1 and n-1
 * Invariant: a
 * - if M[x, y].id = i and edge i is from u to v then
 *   0 <= M[x, u].id < i and 0 <= M[u, y].id < i
 *
 * - Based on this, we can define the path from x to y represented by M
 *     path(x, y) =
 *       if x = y then empty-path
 *       else (concat path(x, u)  i path(v, y))
 *    where i = M[x, y].id and that edge is from u to v.
 *
 *   this recursion is well-founded by the Main invariant,
 *
 *   Then the length of path(x, y) can also be computed recursively:
 *     len(x, y) = if x = y then 0 else len(x, u) + c(i) + len(v, y)
 *   where i = M[x, y].m_edge_id and edge i has cost c(i) and goes from u to v.
 *
 *   That length is stored in M[x, y].dist
 *
 * - The data structure is constructed so that path(x, y) is a shortest
 *   path from x to y in the current graph.
 *   M[x, y].m_val is then the distance from x to y.
 *
 * The graph encodes the constraints asserted so far:
 * - an edge from x to y of cost d encodes the assertion (x - y <= d)
 * - if there's a path of length D from x to y, then the assertions imply (x - y <= D)
 */


#ifndef __RDL_FLOYD_WARSHALL_H
#define __RDL_FLOYD_WARSHALL_H

#include <stdint.h>
#include <stdbool.h>
#include <setjmp.h>

#include "utils/bitvectors.h"
#include "utils/int_hash_tables.h"
#include "utils/arena.h"
#include "utils/int_vectors.h"
#include "terms/rationals.h"
#include "terms/poly_buffer.h"
#include "solvers/floyd_warshall/dl_vartable.h"

#include "solvers/cdcl/smt_core.h"
#include "context/context.h"



/***************
 *  CONSTANTS  *
 **************/

/*
 * The edges in the graph are labeled by a rational
 * constant a/b + an optional infinitesimal delta.
 * The delta is used for strict inequalities:
 * - the constraint x - y <= a/b is encoded by an
 *   edge x ---> y with label a/b
 * - the constraint x - y < a/b is encoded by an
 *   edge x ---> y with label a/b - delta.
 *   (i.e., it's translated to x - y <= a/b - delta)
 *
 * Then the path from x ----> z has a length of the form
 *   a/b + k.delta (where k is a negative integer).
 * The length is stored in the following structure:
 */
typedef struct rdl_const_s {
  rational_t q;
  int32_t delta;
} rdl_const_t;





/***********
 *  GRAPH  *
 **********/

/*
 * Edge indices = signed 32 bit integers
 * - null_rdl_edge = -1 is a marker
 * Vertex index = signed 32 bit integers
 * - null_rdl_vertex = -1
 */
enum {
  null_rdl_edge = -1,
  null_rdl_vertex = -1,
};


/*
 * Edge descriptor: don't need the cost.
 */
typedef struct rdl_edge_s {
  int32_t source;
  int32_t target;
} rdl_edge_t;


/*
 * Stack of edges + a literal for each edge
 * - for edge i: lit[i] == true_literal if i was asserted as an axiom
 * - otherwise lit[i] = a literal l in the smt_core, such that l is true
 *   and l is attached to an rdl atom
 */
typedef struct rdl_edge_stack_s {
  uint32_t size;
  uint32_t top;
  rdl_edge_t *data;
  literal_t *lit;
} rdl_edge_stack_t;

#define DEFAULT_RDL_EDGE_STACK_SIZE 100
#define MAX_RDL_EDGE_STACK_SIZE (UINT32_MAX/sizeof(rdl_edge_t))


/*
 * Cell in the matrix
 * - cell[x, y].id = largest edge index along the shortest path from x to y
 *   (null_rdl_edge if there's no path from x to y)
 * - cell[x, y].dist = length of the shortest path from x to y
 */
typedef struct rdl_cell_s {
  int32_t id;
  rdl_const_t dist;
} rdl_cell_t;


/*
 * Matrix:
 * - data is an array of (size * size) cells
 * - the matrix itself is stored in data[0 ... dim*dim-1]
 */
typedef struct rdl_matrix_s {
  uint32_t size;
  uint32_t dim;
  rdl_cell_t *data;
} rdl_matrix_t;


/*
 * Maximal dimension: we want (dim * x + y) to fit a 32bit unsigned integer
 * where 0 <= x < dim and 0 <= y < dim
 */
#define MAX_RDL_MATRIX_DIMENSION 65535


/*
 * Stack for restoring cells in the matrix
 */
typedef struct rdl_saved_cell_s {
  uint32_t index;   // cell index: M[x, y] has index (nvertices * x + y)
  rdl_cell_t saved; // content to restore
} rdl_saved_cell_t;

typedef struct rdl_cell_stack_s {
  uint32_t size;
  uint32_t top;
  rdl_saved_cell_t *data;
} rdl_cell_stack_t;


#define DEFAULT_RDL_CELL_STACK_SIZE 100
#define MAX_RDL_CELL_STACK_SIZE (UINT32_MAX/sizeof(rdl_saved_cell_t))


/*
 * Graph
 */
typedef struct rdl_graph_s {
  rdl_matrix_t matrix;
  rdl_edge_stack_t edges;
  rdl_cell_stack_t cstack;
  ivector_t    buffer;
  rdl_const_t  c0;      // auxiliary variables for internal computations
} rdl_graph_t;



/***********
 *  ATOMS  *
 **********/

/*
 * Each atom has an index i (in the global atom table)
 * - the atom includes <source vertex, target vertex, cost, boolean variable>
 * - the atom is (source - target <= cost) so cost is a rational
 * - if atom->boolvar = v then the atom index is attached to v in the smt_core
 *   (Hack: this is done by converting the int32_t index to void*).
 */
typedef struct rdl_atom_s {
  int32_t source;
  int32_t target;
  rational_t cost;
  bvar_t boolvar;
} rdl_atom_t;


/*
 * Conversion from atom index to void* (and back)
 * TODO: add a 2bit tag to make this consistent with the egraph
 * tagging of atoms??
 */
static inline void *rdl_index2atom(int32_t i) {
  return (void *) ((size_t) i);
}

static inline int32_t rdl_atom2index(void *a) {
  return (int32_t) ((size_t) a);
}


/*
 * Record for doubly-linked list of free atoms
 */
typedef struct rdl_listelem_s {
  int32_t pre;
  int32_t next;
} rdl_listelem_t;


/*
 * Atom table: current set of atoms have indices between 0 and natoms-1
 * For theory propagation, we maintain a list of free atoms
 * (all atoms not assigned a truth value yet)
 * - size = size of the atoms and next array
 * - mark = one bit per atom
 *   mark = 1 means that the atom is assigned (present in the atom stack)
 *   mark = 0 means that the atom is unassigned (present in the free list)
 * - free_list is an array of n+1 list elements, indexed from -1 to n-1
 */
typedef struct rdl_atbl_s {
  uint32_t size;
  uint32_t natoms;
  rdl_atom_t *atoms;
  rdl_listelem_t *free_list;
  byte_t *mark;
} rdl_atbl_t;


/*
 * Atom stack & propagation queue:
 * - for all assigned atom, the queue contains its index + a sign bit
 * - this follows our usual encoding of index+sign in 32bit:
 *     sign bit = lowest order bit of data[k]
 *     if sign bit = 0, then atom k is true
 *     if sign bit = 1, then atom k is false
 * - every atom in the stack has its mark bit set to 1 in the atom table
 * - the propagation queue consists of the atoms in
 *   data[prop_ptr ... top -1]
 */
typedef struct rdl_astack_s {
  uint32_t size;
  uint32_t top;
  uint32_t prop_ptr;
  int32_t *data;
} rdl_astack_t;



#define DEFAULT_RDL_ATBL_SIZE 100
#define MAX_RDL_ATBL_SIZE (UINT32_MAX/sizeof(rdl_atom_t))

#define DEFAULT_RDL_ASTACK_SIZE 100
#define MAX_RDL_ASTACK_SIZE (UINT32_MAX/sizeof(int32_t))


/*
 * Maximal number of atoms: same as MAX_RDL_ATBL_SIZE
 * (so any atom index fits in 30 bits).
 */
#define MAX_RDL_ATOMS MAX_RDL_ATBL_SIZE



/****************
 *  UNDO STACK  *
 ***************/

/*
 * For backtracking: on entry to each decision level k we store:
 * - edge_id = id of the first edge of level k
 *   for level 0, edge_id must be -1.
 *   for level k>0, edge_id is the number of edges in the graph
 *   when the level k was entered.
 * - top of cell stack, top of atom stack
 */
typedef struct rdl_undo_record_s {
  int32_t edge_id;
  uint32_t nsaved;
  uint32_t natoms;
} rdl_undo_record_t;

typedef struct rdl_undo_stack_s {
  uint32_t size;
  uint32_t top;
  rdl_undo_record_t *data;
} rdl_undo_stack_t;

#define DEFAULT_RDL_UNDO_STACK_SIZE 100
#define MAX_RDL_UNDO_STACK_SIZE (UINT32_MAX/sizeof(rdl_undo_record_t))




/******************
 * PUSH/POP STACK *
 *****************/

/*
 * For each base level, we keep the number of vertices and atoms
 * on entry to that level.
 */
typedef struct rdl_trail_s {
  uint32_t nvertices;
  uint32_t natoms;
} rdl_trail_t;

typedef struct rdl_trail_stack_s {
  uint32_t size;
  uint32_t top;
  rdl_trail_t *data;
} rdl_trail_stack_t;

#define DEFAULT_RDL_TRAIL_SIZE  20
#define MAX_RDL_TRAIL_SIZE (UINT32_MAX/sizeof(rdl_trail_t))




/***************************
 *  FLOYD-WARHSALL SOLVER  *
 **************************/

typedef struct rdl_solver_s {
  /*
   * Attached smt core and gate manager
   */
  smt_core_t *core;
  gate_manager_t *gate_manager;

  /*
   * Base level and decision level (same interpretation as in smt_core)
   */
  uint32_t base_level;
  uint32_t decision_level;

  /*
   * Unsat flag: set to true if asserted axioms are inconsistent
   */
  bool unsat_before_search;

  /*
   * Variable table
   * - every variable (used by the context) is mapped to a
   *   difference logic triple (x - y + c) where x and y are vertices
   *   in the graph.
   */
  dl_vartable_t vtbl;

  /*
   * Graph
   */
  uint32_t nvertices;  // number of vertices
  int32_t zero_vertex; // index of the zero vertex (or null)
  rdl_graph_t graph;

  /*
   * Atom table and stack
   */
  rdl_atbl_t atoms;
  rdl_astack_t astack;

  /*
   * Backtracking stack
   */
  rdl_undo_stack_t stack;

  /*
   * Push/pop stack
   */
  rdl_trail_stack_t trail_stack;

  /*
   * Auxiliary buffers and data structures
   */
  int_htbl_t htbl;       // for hash-consing of atoms
  arena_t arena;         // for storing explanations of implied atoms
  ivector_t expl_buffer; // for constructing explanations
  ivector_t aux_vector;  // general-purpose vector
  rdl_const_t c1;        // for internal use
  rational_t q;          // for internalization

  dl_triple_t triple;     // for variable construction
  poly_buffer_t buffer;   // for internal polynomial operations

  /*
   * Structures used for building a model
   * - value = rational value for each vertex. The array is allocated when needed.
   * - epsilon = safe value for delta
   * - aux = auxiliary rational buffer
   */
  rational_t epsilon;
  rational_t factor;
  rational_t aux;
  rational_t aux2;
  rational_t *value;

  /*
   * Jump buffer for exception handling during internalization
   */
  jmp_buf *env;
} rdl_solver_t;



/*
 * Maximal number of vertices: same as maximal matrix dimension
 */
#define MAX_RDL_VERTICES MAX_RDL_MATRIX_DIMENSION

#define DEFAULT_RDL_BUFFER_SIZE 20




/*********************
 *  MAIN OPERATIONS  *
 ********************/

/*
 * Initialize an rdl solver
 * - core = the attached smt-core object
 * - gates = the attached gate manager
 */
extern void init_rdl_solver(rdl_solver_t *solver, smt_core_t *core, gate_manager_t *gates);


/*
 * Attach a jump buffer for exceptions
 */
extern void rdl_solver_init_jmpbuf(rdl_solver_t *solver, jmp_buf *buffer);


/*
 * Delete: free all allocated memory
 */
extern void delete_rdl_solver(rdl_solver_t *solver);


/*
 * Get interface descriptors to attach solver to a core
 */
extern th_ctrl_interface_t *rdl_ctrl_interface(rdl_solver_t *solver);
extern th_smt_interface_t  *rdl_smt_interface(rdl_solver_t *solver);


/*
 * Get interface descriptor for the internalization functions.
 */
extern arith_interface_t *rdl_arith_interface(rdl_solver_t *solver);



/******************************
 *  VERTEX AND ATOM CREATION  *
 *****************************/

/*
 * Create a new theory variable = a new vertex
 * - return null_rdl_vertex if there are too many vertices
 */
extern int32_t rdl_new_vertex(rdl_solver_t *solver);


/*
 * Return the zero_vertex (create it if needed)
 * - return null_rdl_vertex if the vertex can't be created
 *   (i.e. too many vertices)
 */
extern int32_t rdl_zero_vertex(rdl_solver_t *solver);


/*
 * Create the atom (x - y <= c) and return the corresponding literal
 * - x and y must be vertices in the solver
 * - if x - y <= c simplifies to true or false (given the current graph)
 *   return true_literal or false_literal
 */
extern literal_t rdl_make_atom(rdl_solver_t *solver, int32_t x, int32_t y, rational_t *c);


/*
 * Assert (x - y <= c) or (x - y < c) as an axiom
 * - x and y must be vertices in solver
 * - the solver must be at base level (i.e., solver->decision_level == solver->base_level)
 * - strict true means  assert (x - y < c)
 *   strict false means assert (x - y <= c)
 *
 * - this adds an edge from x to y with cost c to the graph
 * - if the edge causes a conflict, then solver->unsat_before_search is set to true
 */
extern void rdl_add_axiom_edge(rdl_solver_t *solver, int32_t x, int32_t y, rational_t *c, bool strict);


/*
 * Assert (x - y == d) as an axiom:
 * - add edge x ---> y with cost d   (x - y <= d)
 *   and edge y ---> x with cost -d  (y - x <= -d)
 */
extern void rdl_add_axiom_eq(rdl_solver_t *solver, int32_t x, int32_t y, rational_t *d);





/*******************************
 *  INTERNALIZATION FUNCTIONS  *
 ******************************/

/*
 * These functions are used by the context to convert terms to
 * variables and literals. They form the arith_interface descriptor.
 */

/*
 * Create a new theory variable
 * - is_int indicates whether the variable should be an integer,
 *   so it should always be true for this solver.
 * - raise exception NOT_RDL if is_int is true
 * - raise exception TOO_MANY_VARS if we can't create a new vertex
 *   for that variable
 */
extern thvar_t rdl_create_var(rdl_solver_t *solver, bool is_int);


/*
 * Create a variable that represents the constant q
 */
extern thvar_t rdl_create_const(rdl_solver_t *solver, rational_t *q);


/*
 * Create a variable for a polynomial p, with variables defined by map:
 * - p is of the form a_0 t_0 + ... + a_n t_n where t_0, ..., t_n
 *   are arithmetic terms.
 * - map[i] is the theory variable x_i for t_i
 *   (with map[0] = null_thvar if t_0 is const_idx)
 * - the function constructs a variable equal to a_0 x_0 + ... + a_n x_n
 *
 * - fails if a_0 x_0 + ... + a_n x_n is not an RDL polynomial
 *   (i.e., not of the form x - y + c)
 */
extern thvar_t rdl_create_poly(rdl_solver_t *solver, polynomial_t *p, thvar_t *map);


/*
 * Internalization for a product: always fails with NOT_RDL exception
 */
extern thvar_t rdl_create_pprod(rdl_solver_t *solver, pprod_t *p, thvar_t *map);


/*
 * Create the atom x = 0
 */
extern literal_t rdl_create_eq_atom(rdl_solver_t *solver, thvar_t x);


/*
 * Create the atom x >= 0
 */
extern literal_t rdl_create_ge_atom(rdl_solver_t *solver, thvar_t x);


/*
 * Create the atom p = 0
 * - map is used as in create_poly
 * - fails if p is not of the form (x - y + c)
 */
extern literal_t rdl_create_poly_eq_atom(rdl_solver_t *solver, polynomial_t *p, thvar_t *map);


/*
 * Create the atom p >= 0
 * - map is used as in create_poly
 * - fails if p is not of the form (x - y + c)
 */
extern literal_t rdl_create_poly_ge_atom(rdl_solver_t *solver, polynomial_t *p, thvar_t *map);


/*
 * Create the atom (x = y)
 */
extern literal_t rdl_create_vareq_atom(rdl_solver_t *solver, thvar_t x, thvar_t y);


/*
 * Assert the top-level constraint (x == 0) or (x != 0)
 * - if tt is true: assert x == 0
 * - if tt is false: assert x != 0
 */
extern void rdl_assert_eq_axiom(rdl_solver_t *solver, thvar_t x, bool tt);


/*
 * Assert the top-level constraint (x >= 0) or (x < 0)
 * - if tt is true: assert (x >= 0)
 * - if tt is false: assert (x < 0)
 */
extern void rdl_assert_ge_axiom(rdl_solver_t *solver, thvar_t x, bool tt);


/*
 * Assert the top-level constraint (p == 0) or (p != 0)
 * - map is as in create_poly
 * - if tt is true: assert p == 0
 * - if tt is false: assert p != 0
 * - fails if p is not of the form (x - y + c)
 */
extern void rdl_assert_poly_eq_axiom(rdl_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt);


/*
 * Assert the top-level constraint (p >= 0) or (p < 0)
 * - map is as in create_poly
 * - if tt is true: assert (p >= 0)
 * - if tt is false: assert (p < 0)
 * - fails if p is not of the form (x - y + c)
 */
extern void rdl_assert_poly_ge_axiom(rdl_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt);


/*
 * Assert (x == y) or (x != y)
 * - if tt is true: assert (x == y)
 * - if tt is false: assert (x != y)
 */
extern void rdl_assert_vareq_axiom(rdl_solver_t *solver, thvar_t x, thvar_t y, bool tt);


/*
 * Assert (c ==> x == y)
 */
extern void rdl_assert_cond_vareq_axiom(rdl_solver_t *solver, literal_t c, thvar_t x, thvar_t y);


/*
 * Assert (c[0] \/ ... \/ c[n-1] \/ x == y)
 */
extern void rdl_assert_clause_vareq_axiom(rdl_solver_t *solver, uint32_t n, literal_t *c, thvar_t x, thvar_t y);




/***********************
 *  SOLVER FUNCTIONS   *
 **********************/

/*
 * These functions are used by the core. They form the th_ctrl and
 * th_smt interfaces.
 */

/*
 * Start the search
 */
extern void rdl_start_search(rdl_solver_t *solver);

/*
 * Increase the decision level/backtrack
 */
extern void rdl_increase_decision_level(rdl_solver_t *solver);
extern void rdl_backtrack(rdl_solver_t *solver, uint32_t back_level);


/*
 * Push/pop/reset
 */
extern void rdl_push(rdl_solver_t *solver);
extern void rdl_pop(rdl_solver_t *solver);
extern void rdl_reset(rdl_solver_t *solver);


/*
 * Push an assertion into the queue
 * - atom is the index of an rdl_atom with boolean variable v
 * - l is either pos_lit(v) or neg_lit(v)
 * - if l == pos_lit(v), the atom is asserted true, otherwise it's false
 * - return false if a conflict is detected
 *   return true otherwise
 */
extern bool rdl_assert_atom(rdl_solver_t *solver, void *atom, literal_t l);


/*
 * Propagate: process the assertion queue
 * - return false if a conflict is detected
 * - return true otherwise.
 */
extern bool rdl_propagate(rdl_solver_t *solver);

/*
 * Support for theory-branching heuristic
 * - evaluate atom attached to l in the current model
 * - the result is either l or (not l)
 * - if atom is true, return pos_lit(var_of(l))
 * - if atom is false, return neg_lit(var_of(l))
 */
extern literal_t rdl_select_polarity(rdl_solver_t *solver, void *atom, literal_t l);


/*
 * Final check: do nothing and return SAT
 */
extern fcheck_code_t rdl_final_check(rdl_solver_t *solver);



/*
 * Explain why literal l is true.
 * - l is a literal set true by solver in the core (via implied_literal)
 * - expl is the explanation object given to implied_literal,
 *   (expl is an array of literals terminated by null_literal).
 * - expl must be expanded into a conjunction of literals l_0 ... l_k
 *   such that (l_0 and ... and l_k) implies l
 * - literals l_0 ... l_k that must be stored into v
 */
extern void rdl_expand_explanation(rdl_solver_t *solver, literal_t l, literal_t *expl, ivector_t *v);




/************************
 *  MODEL CONSTRUCTION  *
 ***********************/

/*
 * Build a model: assign an integer value to all vertices
 * - the zero vertex has value 0 (if it exists)
 * - the solver must be in a consistent state
 * - the mapping is stored internally in solver->value
 */
extern void rdl_build_model(rdl_solver_t *solver);


/*
 * Return (a pointer to) the value of edge x in the model
 */
static inline rational_t *rdl_vertex_value(rdl_solver_t *solver, int32_t x) {
  assert(solver->value != NULL && 0 <= x && x < solver->nvertices);
  return solver->value + x;
}


/*
 * Value of variable v in the model
 * - copy the value into q and return true
 */
extern bool rdl_value_in_model(rdl_solver_t *solver, thvar_t v, rational_t *q);



/*
 * Free the model
 */
extern void rdl_free_model(rdl_solver_t *solver);


/*****************
 *  STATISTICS   *
 ****************/

// we don't maintain any search statistics
static inline uint32_t rdl_num_vars(rdl_solver_t *solver) {
  return solver->vtbl.nvars;
}

static inline uint32_t rdl_num_atoms(rdl_solver_t *solver) {
  return solver->atoms.natoms;
}

static inline uint32_t rdl_num_vertices(rdl_solver_t *solver) {
  return solver->nvertices;
}





#endif /* __RDL_FLOYD_WARSHALL_H */
