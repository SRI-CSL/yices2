/*
 * FRONT-END FOR DIFFERENCE LOGIC SOLVERS
 */

/*
 * This module is intended to facilitate conversion of arithmetic
 * terms and constraints (as seen by the context) to vertices and
 * edges (as used by difference logic solvers). 
 */

#ifndef __DL_FRONT_END_H
#define __DL_FRONT_END_H

#include <stdint.h>
#include <stdbool.h>
#include <setjmp.h>

#include "rationals.h"
#include "int_hash_tables.h"

#include "smt_core.h"
#include "context.h"




/*
 * Each arithmetic variable is mapped internally to a triple
 * (constant, x, y), where x and y are either nil (-1) or vertices in
 * the difference logic graph.
 *
 * The triple is interpreted as the term (c + x - y):
 *   (c, nil, nil) --> c
 *   (c, x,   nil) --> c + x
 *   (c, nil, y)   --> c - y
 *   (c, x,   y)   --> c + x - y (with x != y)
 *
 * So (c + x - y) >= 0 <--> (y - x <= c) corresponds to adding
 * vertex of y ---> x of cost c in the solver graph.
 */
typedef struct dl_triple_s {
  int32_t target;  // variable x
  int32_t source;  // variable y
  rational_t q;    // constant c
} dl_triple_t;


/*
 * Marker: nil 
 */
enum {
  nil_vertex = -1,
};


/*
 * Variable table:
 * - nvars = number of variables in the table
 * - table->triple[i] = triple for variable x
 * - size = full size of array triple
 * - hash table for hash consing
 */
typedef struct dl_vartable_s {
  uint32_t nvars;
  uint32_t size;
  dl_triple_t *triple;
  int_htbl_t htbl;
} dl_vartable_t;


/*
 * Default and maximal size
 */
#define DEF_DL_VARTABLE_SIZE 100
#define MAX_DL_VARTABLE_SIZE (UINT32_MAX/sizeof(dl_triple_t))


/*
 * Stack for push/pop:
 * - top = the current level (should be equal to base_level in the context)
 *   for 0 <= i < top: data[i] = number of variables defined at level i
 * - size = size of array data
 */
typedef struct dl_trail_stack_s {
  uint32_t size;
  uint32_t top;
  uint32_t *data;
} dl_trail_stack_t;

#define DEF_DL_TRAIL_SIZE 20
#define MAX_DL_TRAIL_SIZE (UINT32_MAX/sizeof(uint32_t))



/*
 * Operations provided by an RDL sub-solver
 *
 * 1) make_vertex(void *solver): create a new vertex
 *    return -1 if error (too many vertices)
 *
 * 2) zero_vertex(void *solver): get a vertex that represents '0'
 *    return -1 if error
 *
 * 3) make_atom(void *solver, int32_t x, int32_t y, rational_t *q)
 *    return a literal for the atom (x - y <= q)
 *
 * 4) add_edge(void *solver, int32_t x, int32_t y, rational_t *q, bool strict)
 *    add the edge [x - y <= q] if strict is false
 *              or [x - y < q]  if strict is true
 *
 * 5) add_eq(void *solver, int32_t x, int32_t y, rational_t *q)
 *    add two edges: [x - y <= q] and [y - x <= -q]
 *
 * 6) build_model(void *solver)
 *    must assign a rational value to all edges
 *
 * 7) value_in_model(void *solver, int32_t x, rational_t *v)
 *    must copy value of x into v (this is called after build_model)
 *
 * 8) free_model(void *solver)
 *    notify solver that the model is no longer needed
 */
typedef int32_t (*dl_make_vertex_fun_t)(void *solver);
typedef int32_t (*dl_zero_vertex_fun_t)(void *solver);
typedef literal_t (*dl_make_atom_fun_t)(void *solver, int32_t x, int32_t y, rational_t *q);
typedef void (*dl_add_edge_fun_t)(void *solver, int32_t x, int32_t y, rational_t *q, bool strict);
typedef void (*dl_add_eq_fun_t)(void *solver, int32_t x, int32_t y, rational_t *q);

typedef void (*dl_build_model_fun_t)(void *solver);
typedef void (*dl_val_in_model_fun_t)(void *solver, int32_t x, rational_t *q);
typedef void (*dl_free_model_fun_t)(void *solver);


typedef struct rdl_interface_s {
  dl_make_vertex_fun_t make_vertex;
  dl_zero_vertex_fun_t zero_vertex;
  dl_make_atom_fun_t make_atom;
  dl_add_edge_fun_t add_edge;
  dl_add_eq_fun_t add_eq;

  dl_build_model_fun_t build_model;
  dl_val_in_model_fun_t value_in_model;
  dl_free_model_fun_t free_model;
} rdl_interface_t;


/*
 * Operations provided by an IDL subsolver: more restricted
 * than the RDL operations. All constants are required to fit
 * in a signed 32bit integer.
 * 
 * 1) make_vertex: same as above
 * 
 * 2) zero_vertex: same as above
 *
 * 3) make_atom(void *solver, int32_t x, int32_t y, int32_t c):
 *    return a literal for the atom (x - y <= c)
 *
 * 4) add_edge(void *solver,  int32_t x, int32_t y, int32_t c)
 *    add the edge [x - y <= c] (no strict version)
 *
 * 5) add_eq(void *solver, int32_t x, int32_t y, int32_t c);
 *    add two egdes: [x - y <= c] and [y - x <= -c]
 *
 * 6) build model: same as above
 *
 * 7) value_in_model(void *solver, int32_t x)
 *    must return the value of x in the model (as an int32_t)
 *
 * 8) free_model: same as above
 */
typedef literal_t (*idl_make_atom_fun_t)(void *solver, int32_t x, int32_t y, int32_t c);
typedef void (*idl_add_edge_fun_t)(void *solver, int32_t x, int32_t y, int32_t c);
typedef void (*idl_add_eq_fun_t)(void *solver, int32_t x, int32_t y, int32_t c);
typedef int32_t (*idl_val_in_model_fun_t)(void *solver, int32_t x);


typedef struct idl_interface_s {
  dl_make_vertex_fun_t make_vertex;
  dl_zero_vertex_fun_t zero_vertex;
  idl_make_atom_fun_t make_atom;
  idl_add_edge_fun_t add_edge;
  idl_add_eq_fun_t add_eq;

  dl_build_model_fun_t build_model;
  idl_val_in_model_fun_t value_in_model;
  dl_free_model_fun_t free_model;
} idl_interface_t;





/*****************
 *  FULL SOLVER  *
 ****************/

/*
 * The full solver is attached to:
 * - core = DPLL sat solver 
 * - gate_manager = manager for boolean gates
 * - sub_solver = the actual difference logic solver
 */
typedef struct dl_front_end_s {
  /*
   * Attached smt code + gate manager
   */
  smt_core_t *core;
  gate_manager_t *gate_manager;

  /*
   * Variable table + trail stack
   */
  dl_vartable_t vtbl;
  dl_trail_stack_t trail_stack;

  /*
   * Subsolver + interface descriptors + flag to indicate
   * whether the subsolver is for IDL or RDL
   */
  void *solver;
  bool is_idl;
  rdl_interface_t rdl;
  idl_interface_t idl;

  /*
   * Auxiliary buffers
   */
  dl_triple_t aux;
  rational_t q0;

  /*
   * Jmp buffer for internalization exceptions
   */
  jmp_buf *env;

} dl_front_end_t;




/****************
 *  OPERATIONS  *
 ***************/

/*
 * Initialize:
 * - core = attached core
 * - gates = attached gate manager
 * - the subsolver is NULL
 */
extern void init_dl_front_end(dl_front_end_t *dl, smt_core_t *core, gate_manager_t *gates);


/*
 * Attach an IDL solver
 * - idl = interface descriptor
 * - there must not be an existing solver attached to dl
 */
extern void dl_front_end_attach_idl_solver(dl_front_end_t *dl, void *solver, idl_interface_t *idl);


/*
 * Attach an RDL sub-solver
 * - rdl = interface descriptor
 * - there must not be an existing solver attached to dl
 */
extern void dl_front_end_attach_rdl_solver(dl_front_end_t *dl, void *solver, rdl_interface_t *rdl);


/*
 * Attach a jump buffer for internalization exceptions
 */
extern void dl_front_end_init_jmpbuf(dl_front_end_t *dl, jmp_buf *buffer);


/*
 * Delete: free memory
 */
extern void delete_dl_front_end(dl_front_end_t *dl);


/*
 * Push/pop/reset
 */
extern void dl_front_end_push(dl_front_end_t *dl);
extern void dl_front_end_pop(dl_front_end_t *dl);
extern void dl_front_end_reset(dl_front_end_t *dl);



/*******************************
 *  INTERNALIZATION FUNCTIONS  *
 ******************************/

/*
 * Create a fresh variable
 * - is_int true means that the variable has type int 
 * - is_int false means that the variable has type real
 * This fails and raises exception NOT_IDL or NOT_RDL if this flag
 * does not match the internal solver type.
 *
 * Also fails with exception TOO_MANY_VARS if the subsolver can't 
 * create the variable.
 */
extern thvar_t dl_create_var(dl_front_end_t *dl, bool is_int);


/*
 * Create a variable that represents the constant q
 * - if the internal solver is for IDL, fails if q is not an integer
 */
extern thvar_t dl_create_const(dl_front_end_t *dl, rational_t *q);


/*
 * Create a variable for a polynomial p, with variables defined by map:
 * - p is of the form a_0 t_0 + ... + a_n t_n where t_0, ..., t_n
 *   are arithmetic terms.
 * - map[i] is the theory variable x_i for t_i 
 * - the function constructs a variable equal to a_0 x_0 + ... + a_n x_n
 * - fails if p is not an IDL or RDL polynomial
 */
extern thvar_t dl_create_poly(dl_front_end_t *dl, polynomial_t *p, thvar_t *map);


/*
 * Internalization for a product: always fails with NOT_IDL or NOT_RDL exception
 */
extern thvar_t dl_create_pprod(dl_front_end_t *dl, pprod_t *p, thvar_t *map);


/*
 * Create the atom x = 0
 */
extern literal_t dl_create_eq_atom(dl_front_end_t *dl, thvar_t x);


/*
 * Create the atom x >= 0
 */
extern literal_t dl_create_ge_atom(dl_front_end_t *dl, thvar_t x);


/*
 * Create the atom (x = y)
 */
extern literal_t dl_create_vareq_atom(dl_front_end_t *dl, thvar_t x, thvar_t y);


/*
 * Assert the top-level constraint (x == 0) or (x != 0)
 * - if tt is true: assert x == 0
 * - if tt is false: assert x != 0
 */
extern void dl_assert_eq_axiom(dl_front_end_t *dl, thvar_t x, bool tt);


/*
 * Assert the top-level constraint (x >= 0) or (x < 0)
 * - if tt is true: assert (x >= 0)
 * - if tt is false: assert (x < 0)
 */
extern void dl_assert_ge_axiom(dl_front_end_t *dl, thvar_t x, bool tt);


/*
 * Assert (x == y) or (x != y)
 * - if tt is true: assert (x == y)
 * - if tt is false: assert (x != y)
 */
extern void dl_assert_vareq_axiom(dl_front_end_t *dl, thvar_t x, thvar_t y, bool tt);


/*
 * Assert (c ==> x == y)
 */
extern void dl_assert_cond_vareq_axiom(dl_front_end_t *dl, literal_t c, thvar_t x, thvar_t y);





#endif /* __DL_FRONT_END_H */
