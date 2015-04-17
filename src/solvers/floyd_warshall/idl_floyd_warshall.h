/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * INCREMENTAL FORM OF THE FLOYD-WARSHALL ALGORITHM FOR INTEGER DIFFERENCE LOGIC.
 */

/*
 * This solver is for integer difference logic only. It cannot be
 * attached to the egraph.
 *
 * WARNING: All path length computations are done using signed 32bit
 * integers. There's some check for this now (not very precise).
 */

/*
 * Graph representation
 * - edges are stored in a stack (added and removed in FIFO order)
 * - each edge has source and destination vertices and an integer cost
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


#ifndef __IDL_FLOYD_WARSHALL_H
#define __IDL_FLOYD_WARSHALL_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <setjmp.h>

#include "context/context_types.h"
#include "solvers/cdcl/smt_core.h"
#include "solvers/floyd_warshall/dl_vartable.h"
#include "terms/poly_buffer.h"
#include "utils/arena.h"
#include "utils/bitvectors.h"
#include "utils/int_hash_tables.h"
#include "utils/int_vectors.h"


/***********
 *  GRAPH  *
 **********/

/*
 * Edge indices = signed 32 bit integers
 * - null_idl_edge = -1 is a marker
 * Vertex index = signed 32 bit integers
 * - null_idl_vertex = -1
 */
enum {
  null_idl_edge = -1,
  null_idl_vertex = -1,
};


/*
 * Edge descriptor:
 * - the cost is used only by the debugging function valid_idl_graph
 */
typedef struct idl_edge_s {
  int32_t source;
  int32_t target;
#ifndef NDEBUG
  int32_t cost;
#endif
} idl_edge_t;


/*
 * Stack of edges + a literal for each edge
 * - for edge i: lit[i] == true_literal if i was asserted as an axiom
 * - otherwise lit[i] = a literal l in the smt_core, such that l is true
 *   and l is attached to an idl atom
 */
typedef struct edge_stack_s {
  uint32_t size;
  uint32_t top;
  idl_edge_t *data;
  literal_t *lit;
} edge_stack_t;

#define DEFAULT_IDL_EDGE_STACK_SIZE 100
#define MAX_IDL_EDGE_STACK_SIZE (UINT32_MAX/sizeof(idl_edge_t))


/*
 * Cell in the matrix
 */
typedef struct idl_cell_s {
  int32_t id; // edge index
  int32_t dist;
} idl_cell_t;


/*
 * Matrix:
 * - data is an array of (size * size) cells
 * - the matrix itself is stored in data[0 ... dim*dim-1]
 */
typedef struct idl_matrix_s {
  uint32_t size;
  uint32_t dim;
  idl_cell_t *data;
} idl_matrix_t;


/*
 * Maximal dimension: we want (dim * x + y) to fit a 32bit unsigned integer
 * where 0 <= x < dim and 0 <= y < dim
 */
#define MAX_IDL_MATRIX_DIMENSION 65535


/*
 * Stack for restoring cells in the matrix
 */
typedef struct saved_cell_s {
  uint32_t index;   // cell index: M[x, y] has index (nvertices * x + y)
  idl_cell_t saved; // content to restore
} saved_cell_t;

typedef struct cell_stack_s {
  uint32_t size;
  uint32_t top;
  saved_cell_t *data;
} cell_stack_t;


#define DEFAULT_IDL_CELL_STACK_SIZE 100
#define MAX_IDL_CELL_STACK_SIZE (UINT32_MAX/sizeof(saved_cell_t))


/*
 * Graph
 */
typedef struct idl_graph_s {
  idl_matrix_t matrix;
  edge_stack_t edges;
  cell_stack_t cstack;
  ivector_t    buffer;
} idl_graph_t;



/***********
 *  ATOMS  *
 **********/

/*
 * Each atom has an index i (in the global atom table)
 * - the atom includes <source vertex, target vertex, cost, boolean variable>
 * - if atom->boolvar = v then the atom index is attached to v in the smt_core
 *   (Hack: this is done by converting the int32_t index to void*).
 */
typedef struct idl_atom_s {
  int32_t source;
  int32_t target;
  int32_t cost;
  bvar_t boolvar;
} idl_atom_t;


/*
 * Conversion from atom index to void* (and back)
 * TODO: add a 2bit tag to make this consistent with the egraph
 * tagging of atoms??
 */
static inline void *index2atom(int32_t i) {
  return (void *) ((size_t) i);
}

static inline int32_t atom2index(void *a) {
  return (int32_t) ((size_t) a);
}


/*
 * Record for doubly-linked list of free atoms
 */
typedef struct idl_listelem_s {
  int32_t pre;
  int32_t next;
} idl_listelem_t;


/*
 * Atom table: current set of atoms have indices between 0 and natoms-1
 * For theory propagation, we maintain a list of free atoms
 * (all atoms not assigned a truth value yet)
 * - size = size of the atoms array
 * - mark = one bit per atom
 *   mark = 1 means that the atom is assigned (present in the atom stack)
 *   mark = 0 means that the atom is unassigned (present in the free list)
 * - free_list is an array of n+1 list elements, indexed from -1 to n-1
 */
typedef struct idl_atbl_s {
  uint32_t size;
  uint32_t natoms;
  idl_atom_t *atoms;
  idl_listelem_t *free_list;
  byte_t *mark;
} idl_atbl_t;


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
typedef struct idl_astack_s {
  uint32_t size;
  uint32_t top;
  uint32_t prop_ptr;
  int32_t *data;
} idl_astack_t;



#define DEFAULT_IDL_ATBL_SIZE 100
#define MAX_IDL_ATBL_SIZE (UINT32_MAX/sizeof(idl_atom_t))

#define DEFAULT_IDL_ASTACK_SIZE 100
#define MAX_IDL_ASTACK_SIZE (UINT32_MAX/sizeof(int32_t))


/*
 * Maximal number of atoms: same as MAX_IDL_ATBL_SIZE
 * (so any atom index fits in 30 bits).
 */
#define MAX_IDL_ATOMS MAX_IDL_ATBL_SIZE



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
typedef struct idl_undo_record_s {
  int32_t edge_id;
  uint32_t nsaved;
  uint32_t natoms;
} idl_undo_record_t;

typedef struct idl_undo_stack_s {
  uint32_t size;
  uint32_t top;
  idl_undo_record_t *data;
} idl_undo_stack_t;

#define DEFAULT_IDL_UNDO_STACK_SIZE 100
#define MAX_IDL_UNDO_STACK_SIZE (UINT32_MAX/sizeof(idl_undo_record_t))




/******************
 * PUSH/POP STACK *
 *****************/

/*
 * For each base level, we keep the number of vertices and atoms
 * on entry to that level.
 */
typedef struct idl_trail_s {
  uint32_t nvertices;
  uint32_t natoms;
} idl_trail_t;

typedef struct idl_trail_stack_s {
  uint32_t size;
  uint32_t top;
  idl_trail_t *data;
} idl_trail_stack_t;

#define DEFAULT_IDL_TRAIL_SIZE  20
#define MAX_IDL_TRAIL_SIZE (UINT32_MAX/sizeof(idl_trail_t))




/***************************
 *  FLOYD-WARHSALL SOLVER  *
 **************************/

typedef struct idl_solver_s {
  /*
   * Attached smt core + gate manager
   */
  smt_core_t *core;
  gate_manager_t *gate_manager;

  /*
   * Base level and decision level (same interpretation as in smt_core)
   */
  uint32_t base_level;
  uint32_t decision_level;

  /*
   * Unsat flag: set to true if the asserted axioms are inconsistent
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
  int32_t zero_vertex; // index of zero vertex or null
  idl_graph_t graph;

  /*
   * Atom table and stack
   */
  idl_atbl_t atoms;
  idl_astack_t astack;

  /*
   * Backtracking stack
   */
  idl_undo_stack_t stack;

  /*
   * Push/pop stack
   */
  idl_trail_stack_t trail_stack;

  /*
   * Auxiliary buffers and data structures
   */
  int_htbl_t htbl;        // for hash-consing of atoms
  arena_t arena;          // for storing explanations of implied atoms
  ivector_t expl_buffer;  // for constructing explanations
  ivector_t aux_vector;   // general-purpose vector

  dl_triple_t triple;     // for variable construction
  poly_buffer_t buffer;   // for internal polynomial operations

  /*
   * Variable assignment: allocated when needed in build_model
   */
  int32_t *value;

  /*
   * Jump buffer for exception handling during internalization
   */
  jmp_buf *env;
} idl_solver_t;



/*
 * Maximal number of vertices: same as maximal matrix dimension
 */
#define MAX_IDL_VERTICES MAX_IDL_MATRIX_DIMENSION

#define DEFAULT_IDL_BUFFER_SIZE 20




/*********************
 *  MAIN OPERATIONS  *
 ********************/

/*
 * Initialize an idl solver
 * - core = the attached smt-core object
 * - gates = the attached gate manager
 */
extern void init_idl_solver(idl_solver_t *solver, smt_core_t *core, gate_manager_t *gates);


/*
 * Attach a jump buffer for internalization exception
 */
extern void idl_solver_init_jmpbuf(idl_solver_t *solver, jmp_buf *buffer);


/*
 * Delete: free all allocated memory
 */
extern void delete_idl_solver(idl_solver_t *solver);


/*
 * Get interface descriptors to attach solver to a core
 */
extern th_ctrl_interface_t *idl_ctrl_interface(idl_solver_t *solver);
extern th_smt_interface_t  *idl_smt_interface(idl_solver_t *solver);


/*
 * Get interface descriptor for the internalization functions.
 */
extern arith_interface_t *idl_arith_interface(idl_solver_t *solver);




/******************************
 *  VERTEX AND ATOM CREATION  *
 *****************************/

/*
 * Create a new theory variable = a new vertex
 * - return null_idl_vertex if there are too many vertices
 */
extern int32_t idl_new_vertex(idl_solver_t *solver);


/*
 * Return the zero_vertex (create it if needed)
 * - return null_idl_vertex if the vertex can't be created
 *   (i.e. too many vertices)
 */
extern int32_t idl_zero_vertex(idl_solver_t *solver);


/*
 * Create the atom (x - y <= d) and return the corresponding literal
 * - x and y must be vertices in the solver
 * - if x - y <= d simplifies to true or false (given the current graph)
 *   return true_literal or false_literal
 */
extern literal_t idl_make_atom(idl_solver_t *solver, int32_t x, int32_t y, int32_t d);


/*
 * Assert (x - y <= d) as an axiom
 * - x and y must be vertices in solver
 * - the solver must be at base level (i.e., solver->decision_level == solver->base_level)
 *
 * - this adds an edge from x to y with cost d to the graph
 * - if the edge causes a conflict, then solver->unsat_before_search is set to true
 */
extern void idl_add_axiom_edge(idl_solver_t *solver, int32_t x, int32_t y, int32_t d);


/*
 * Assert (x - y == d) as an axiom:
 * - add edge x ---> y with cost d   (x - y <= d)
 *   and edge y ---> x with cost -d  (y - x <= -d)
 */
extern void idl_add_axiom_eq(idl_solver_t *solver, int32_t x, int32_t y, int32_t d);





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
 * - raise exception NOT_IDL if is_int is false
 * - raise exception TOO_MANY_VARS if we can't create a new vertex
 *   for that variable
 */
extern thvar_t idl_create_var(idl_solver_t *solver, bool is_int);


/*
 * Create a variable that represents the constant q
 * - raise an exception if q is not an integer
 */
extern thvar_t idl_create_const(idl_solver_t *solver, rational_t *q);


/*
 * Create a variable for a polynomial p, with variables defined by map:
 * - p is of the form a_0 t_0 + ... + a_n t_n where t_0, ..., t_n
 *   are arithmetic terms.
 * - map[i] is the theory variable x_i for t_i
 *   (with map[0] = null_thvar if t_0 is const_idx)
 * - the function constructs a variable equal to a_0 x_0 + ... + a_n x_n
 *
 * - fails if a_0 x_0 + ... + a_n x_n is not an IDL polynomial
 *   (i.e., not of the form x - y + c)
 */
extern thvar_t idl_create_poly(idl_solver_t *solver, polynomial_t *p, thvar_t *map);


/*
 * Internalization for a product: always fails with NOT_IDL exception
 */
extern thvar_t idl_create_pprod(idl_solver_t *solver, pprod_t *p, thvar_t *map);


/*
 * Create the atom x = 0
 */
extern literal_t idl_create_eq_atom(idl_solver_t *solver, thvar_t x);


/*
 * Create the atom x >= 0
 */
extern literal_t idl_create_ge_atom(idl_solver_t *solver, thvar_t x);


/*
 * Create the atom p = 0
 * - map is used as in create_poly
 * - fails if p is not of the form (x - y + c)
 */
extern literal_t idl_create_poly_eq_atom(idl_solver_t *solver, polynomial_t *p, thvar_t *map);


/*
 * Create the atom p >= 0
 * - map is used as in create_poly
 * - fails if p is not of the form (x - y + c)
 */
extern literal_t idl_create_poly_ge_atom(idl_solver_t *solver, polynomial_t *p, thvar_t *map);


/*
 * Create the atom (x = y)
 */
extern literal_t idl_create_vareq_atom(idl_solver_t *solver, thvar_t x, thvar_t y);


/*
 * Assert the top-level constraint (x == 0) or (x != 0)
 * - if tt is true: assert x == 0
 * - if tt is false: assert x != 0
 */
extern void idl_assert_eq_axiom(idl_solver_t *solver, thvar_t x, bool tt);


/*
 * Assert the top-level constraint (x >= 0) or (x < 0)
 * - if tt is true: assert (x >= 0)
 * - if tt is false: assert (x < 0)
 */
extern void idl_assert_ge_axiom(idl_solver_t *solver, thvar_t x, bool tt);


/*
 * Assert the top-level constraint (p == 0) or (p != 0)
 * - map is as in create_poly
 * - if tt is true: assert p == 0
 * - if tt is false: assert p != 0
 * - fails if p is not of the form (x - y + c)
 */
extern void idl_assert_poly_eq_axiom(idl_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt);


/*
 * Assert the top-level constraint (p >= 0) or (p < 0)
 * - map is as in create_poly
 * - if tt is true: assert (p >= 0)
 * - if tt is false: assert (p < 0)
 * - fails if p is not of the form (x - y + c)
 */
extern void idl_assert_poly_ge_axiom(idl_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt);


/*
 * Assert (x == y) or (x != y)
 * - if tt is true: assert (x == y)
 * - if tt is false: assert (x != y)
 */
extern void idl_assert_vareq_axiom(idl_solver_t *solver, thvar_t x, thvar_t y, bool tt);


/*
 * Assert (c ==> x == y)
 */
extern void idl_assert_cond_vareq_axiom(idl_solver_t *solver, literal_t c, thvar_t x, thvar_t y);


/*
 * Assert (c[0] \/ ... \/ c[n-1] \/ x == y)
 */
extern void idl_assert_clause_vareq_axiom(idl_solver_t *solver, uint32_t n, literal_t *c, thvar_t x, thvar_t y);




/**********************
 *  SOLVER FUNCTIONS  *
 *********************/

/*
 * These functions are used by the core. They form the th_ctrl and
 * th_smt interfaces.
 */

/*
 * Start the search
 */
extern void idl_start_search(idl_solver_t *solver);


/*
 * Increase the decision level/backtrack
 */
extern void idl_increase_decision_level(idl_solver_t *solver);
extern void idl_backtrack(idl_solver_t *solver, uint32_t back_level);


/*
 * Push/pop/reset
 */
extern void idl_push(idl_solver_t *solver);
extern void idl_pop(idl_solver_t *solver);
extern void idl_reset(idl_solver_t *solver);


/*
 * Push an assertion into the queue
 * - atom is the index of an idl_atom with boolean variable v
 * - l is either pos_lit(v) or neg_lit(v)
 * - if l == pos_lit(v), the atom is asserted true, otherwise it's false
 * - return false if a conflict is detected
 *   return true otherwise
 */
extern bool idl_assert_atom(idl_solver_t *solver, void *atom, literal_t l);


/*
 * Propagate: process the assertion queue
 * - return false if a conflict is detected
 * - return true otherwise.
 */
extern bool idl_propagate(idl_solver_t *solver);


/*
 * Support for theory-branching heuristic
 * - evaluate atom attached to l in the current model
 * - the result is either l or (not l)
 * - if atom is true, return pos_lit(var_of(l))
 * - if atom is false, return neg_lit(var_of(l))
 */
extern literal_t idl_select_polarity(idl_solver_t *solver, void *atom, literal_t l);


/*
 * Final check: do nothing and return SAT
 */
extern fcheck_code_t idl_final_check(idl_solver_t *solver);


/*
 * Explain why literal l is true.
 * - l is a literal set true by solver in the core (via implied_literal)
 * - expl is the explanation object given to implied_literal,
 *   (expl is an array of literals terminated by null_literal).
 * - expl must be expanded into a conjunction of literals l_0 ... l_k
 *   such that (l_0 and ... and l_k) implies l
 * - literals l_0 ... l_k that must be stored into v
 */
extern void idl_expand_explanation(idl_solver_t *solver, literal_t l, literal_t *expl, ivector_t *v);





/************************
 *  MODEL CONSTRUCTION  *
 ***********************/

/*
 * Build a model: assign an integer value to all vertices
 * - the zero vertex has value 0 (if it exists)
 * - the solver must be in a consistent state
 * - the mapping is stored internally in solver->value
 */
extern void idl_build_model(idl_solver_t *solver);


/*
 * Value of vertex x in the model
 */
static inline int32_t idl_vertex_value(idl_solver_t *solver, int32_t x) {
  assert(solver->value != NULL && 0 <= x && x < solver->nvertices);
  return solver->value[x];
}


/*
 * Value of variable v in the model
 * - copy the value in rational q and return true
 */
extern bool idl_value_in_model(idl_solver_t *solver, thvar_t v, rational_t *q);


/*
 * Free the model
 */
extern void idl_free_model(idl_solver_t *solver);



/*****************
 *  STATISTICS   *
 ****************/

// we don't maintain any search statistics
static inline uint32_t idl_num_vars(idl_solver_t *solver) {
  return solver->vtbl.nvars;
}

static inline uint32_t idl_num_atoms(idl_solver_t *solver) {
  return solver->atoms.natoms;
}

static inline uint32_t idl_num_vertices(idl_solver_t *solver) {
  return solver->nvertices;
}



#endif /* __IDL_FLOYD_WARSHALL_H */
