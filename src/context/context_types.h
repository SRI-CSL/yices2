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
 * CONTEXT
 */

#ifndef __CONTEXT_TYPES_H
#define __CONTEXT_TYPES_H

#include <stdint.h>
#include <stdbool.h>
#include <setjmp.h>

#include "api/smt_logic_codes.h"
#include "context/assumption_stack.h"
#include "context/common_conjuncts.h"
#include "context/divmod_table.h"
#include "context/internalization_table.h"
#include "context/pseudo_subst.h"
#include "context/shared_terms.h"
#include "io/tracer.h"
#include "solvers/cdcl/gates_manager.h"
#include "solvers/cdcl/smt_core.h"
#include "solvers/egraph/egraph.h"
#include "terms/bvpoly_buffers.h"
#include "terms/conditionals.h"
#include "terms/int_rational_hash_maps.h"
#include "terms/poly_buffer.h"
#include "terms/terms.h"
#include "utils/int_bv_sets.h"
#include "utils/int_hash_sets.h"
#include "utils/int_queues.h"
#include "utils/int_stack.h"
#include "utils/int_vectors.h"
#include "utils/object_stack.h"
#include "utils/mark_vectors.h"
#include "utils/pair_hash_map2.h"

#include "mcsat/solver.h"

/***********************
 *  OPTIONAL FEATURES  *
 **********************/

/*
 * Bit mask for specifying which features are supported by a context.
 * These are set when the context is created.
 */
#define MULTICHECKS_OPTION_MASK 0x1
#define PUSHPOP_OPTION_MASK     0x2
#define CLEANINT_OPTION_MASK    0x4


/*
 * Possible modes: each mode defines which of the three above
 * bits are set.
 */
typedef enum {
  CTX_MODE_ONECHECK,
  CTX_MODE_MULTICHECKS,
  CTX_MODE_PUSHPOP,
  CTX_MODE_INTERACTIVE,
} context_mode_t;

#define NUM_MODES (CTX_MODE_INTERACTIVE+1)


/*
 * Possible solver classes.
 */
typedef enum {
  CTX_SOLVER_TYPE_DPLLT,
  CTX_SOLVER_TYPE_MCSAT,
} context_solver_type_t;

#define NUM_SOLVER_TYPES (CTX_SOLVER_TYPE_MCSAT+1)

/*
 * More bit masks for enabling/disabling simplification
 * - VARELIM eliminate variables (via substitution)
 * - FLATTENOR rewrites (or ... (or ...) ...) into a single (or ....)
 * - FLATTENDISEQ rewrite arithmetic disequality
 *      (not (p == 0)) into (or (not (p >= 0)) (not (-p >= 0)))
 *   FLATTENDISEQ requires FLATTENOR to be enabled
 * - EQABSTRACT enables the abstraction-based equality learning heuristic
 * - ARITHELIM enables variable elimination in arithmetic
 * - KEEP_ITE: keep if-then-else terms in the egraph
 * - BREAKSYM: enables symmetry breaking
 * - PSEUDO_INVERSE: enables elimination of unconstrained terms using
 *   pseudo-inverse tricks
 * - CONDITIONAL_DEF: attempt to detect and use assertions of the form
 *     (condition => (term = constant))
 * - FLATTEN_ITE: avoid intermediate variables when converting nested
 *   if-then-else terms
 * - FACTOR_TOP_OR: extract common factors from top-level disjuncts
 *
 * BREAKSYM for QF_UF is based on the paper by Deharbe et al (CADE 2011)
 *
 * PSEUDO_INVERSE is based on Brummayer's thesis (Boolector stuff)
 * - not implemented yet
 *
 * ITE_BOUNDS: for a special if-then-else term t (i.e., if-then-else
 * term with constant leaves), compute the lower and upper bound on t
 * and assert that t is between these two bounds. Example: for t =
 * (ite c 0 1), assert (0 <= t <= 1), and similar for nested
 * if-then-elses.
 *
 * Options passed to the simplex solver when it's created
 * - EAGER_LEMMAS
 * - ENABLE_ICHECK
 * - EQPROP
 *
 * Options for testing and debugging
 * - LAX_OPTION: try to keep going when the assertions contain unsupported
 *               constructs (e.g., quantifiers/bitvectors).
 * - DUMP_OPTION
 */
#define VARELIM_OPTION_MASK             0x10
#define FLATTENOR_OPTION_MASK           0x20
#define FLATTENDISEQ_OPTION_MASK        0x40
#define EQABSTRACT_OPTION_MASK          0x80
#define ARITHELIM_OPTION_MASK           0x100
#define KEEP_ITE_OPTION_MASK            0x200
#define BVARITHELIM_OPTION_MASK         0x400
#define BREAKSYM_OPTION_MASK            0x800
#define PSEUDO_INVERSE_OPTION_MASK      0x1000
#define ITE_BOUNDS_OPTION_MASK          0x2000
#define CONDITIONAL_DEF_OPTION_MASK     0x4000
#define FLATTEN_ITE_OPTION_MASK         0x8000
#define FACTOR_OR_OPTION_MASK           0x10000

#define PREPROCESSING_OPTIONS_MASK \
 (VARELIM_OPTION_MASK|FLATTENOR_OPTION_MASK|FLATTENDISEQ_OPTION_MASK|\
  EQABSTRACT_OPTION_MASK|ARITHELIM_OPTION_MASK|KEEP_ITE_OPTION_MASK|\
  BVARITHELIM_OPTION_MASK|BREAKSYM_OPTION_MASK|PSEUDO_INVERSE_OPTION_MASK|\
  ITE_BOUNDS_OPTION_MASK|CONDITIONAL_DEF_OPTION_MASK|FLATTEN_ITE_OPTION_MASK|\
  FACTOR_OR_OPTION_MASK)

// SIMPLEX OPTIONS
#define SPLX_EGRLMAS_OPTION_MASK  0x1000000
#define SPLX_ICHECK_OPTION_MASK   0x2000000
#define SPLX_EQPROP_OPTION_MASK   0x4000000

// FOR TESTING
#define LAX_OPTION_MASK         0x40000000
#define DUMP_OPTION_MASK        0x80000000



/***************************************
 *  ARCHITECTURES/SOLVER COMBINATIONS  *
 **************************************/

/*
 * An architecture is specified by one of the following codes
 * - each architecture defines a set of solvers (and the supported theories)
 * - the special "auto" codes can be used if mode is CTX_MODE_ONECHECK
 */
typedef enum {
  CTX_ARCH_NOSOLVERS,    // core only
  CTX_ARCH_EG,           // egraph
  CTX_ARCH_SPLX,         // simplex
  CTX_ARCH_IFW,          // integer floyd-warshall
  CTX_ARCH_RFW,          // real floyd-warshall
  CTX_ARCH_BV,           // bitvector solver
  CTX_ARCH_EGFUN,        // egraph+array/function theory
  CTX_ARCH_EGSPLX,       // egraph+simplex
  CTX_ARCH_EGBV,         // egraph+bitvector solver
  CTX_ARCH_EGFUNSPLX,    // egraph+fun+simplex
  CTX_ARCH_EGFUNBV,      // egraph+fun+bitvector
  CTX_ARCH_EGSPLXBV,     // egraph+simplex+bitvector
  CTX_ARCH_EGFUNSPLXBV,  // all solvers (should be the default)

  CTX_ARCH_AUTO_IDL,     // either simplex or integer floyd-warshall
  CTX_ARCH_AUTO_RDL,     // either simplex or real floyd-warshall

  CTX_ARCH_MCSAT         // mcsat solver
} context_arch_t;


#define NUM_ARCH (CTX_ARCH_MCSAT+1)


/*
 * Supported theories (including arithmetic and function theory variants)
 * - a 32bit theories word indicate what's supported
 * - each bit selects a theory
 * The theory word is derived from the architecture descriptor
 */
#define UF_MASK        0x1
#define BV_MASK        0x2
#define IDL_MASK       0x4
#define RDL_MASK       0x8
#define LIA_MASK       0x10
#define LRA_MASK       0x20
#define LIRA_MASK      0x40
#define NLIRA_MASK     0x80     // non-linear arithmetic
#define FUN_UPDT_MASK  0x100
#define FUN_EXT_MASK   0x200
#define QUANT_MASK     0x400

// arith means all variants of linear arithmetic are supported
#define ARITH_MASK (LIRA_MASK|LRA_MASK|LIA_MASK|RDL_MASK|IDL_MASK)

// nlarith_mask means non-linear arithmetic is supported too
#define NLARITH_MASK (NLIRA_MASK|ARITH_MASK)

// fun means both function theories are supported
#define FUN_MASK   (FUN_UPDT_MASK|FUN_EXT_MASK)

// all theories, except non-linear arithmetic
#define ALLTH_MASK (UF_MASK|BV_MASK|ARITH_MASK|FUN_MASK)




/***********************************
 *  PREPROCESSING/SIMPLIFICATION   *
 **********************************/

/*
 * Marks for detecting cycles in variable substitutions
 * - white: term not visited
 * - grey: term found but not fully explored yet
 * - black: fully explored term
 */
enum {
  WHITE = 0,
  GREY = 1,
  BLACK = 2,
};




/**************************
 *  ARITHMETIC INTERFACE  *
 *************************/

/*
 * An arithmetic solver must implement the following internalization functions:
 *
 * Term constructors
 * -----------------
 * A term in the arithmetic solver is identified by an integer index (arithmetic variable).
 *
 * 1) thvar_t create_var(void *solver, bool is_int)
 *    - this must return the index of a new arithmetic variable (no eterm attached)
 *    - if is_int is true, that variable must have integer type, otherwise, it must
 *      be a real.
 *
 * 2) thvar_t create_const(void *solver, rational_t *q)
 *    - this must create a theory variable equal to q and return it (no eterm attached)
 *
 * 3) thvar_t create_poly(void *solver, polynomial_t *p, thvar_t *map)
 *    - this must return a theory variable equal to p with variables renamed as
 *      defined by map
 *    - p is of the form a_0 t_0 + a_1 t1 ... + a_n t_n,
 *       where t_0 is either the special marker const_idx (= 0) or an arithmetic term
 *         and t_1 ... t_n are arithmetic terms
 *    - map is an array of n+1 theory variables:
 *      map[i] = the theory variable x_i mapped to t_i (with the convention that const_idx
 *               is always mapped to null_thvar)
 *    - the solver must return a theory variable y equal to a_0 x_0 + ... + a_n x_n
 *
 * 4) thvar_t create_pprod(void *solver, pprod_t *r, thvar_t *map)
 *    - must return a theory variable equal to r with variables defined by map
 *    - r if of the form t_0^d_0 x ... x t_n^d_n where t_0 ... t_n are arithmetic
 *      terms
 *    - map is an array of n+1 variables: map[i] = variable x_i mapped to t_i
 *    - the solver must return an arithmetic variable y equal to (x_0^d_0 x ... x x_n^d_n)
 *
 *
 * Atom constructors
 * -----------------
 *
 * 5) literal_t create_eq_atom(void *solver, thvar_t x)
 *    - must create the atom (x == 0) and return the corresponding literal
 *    - x is an existing theory variable in solver
 *
 * 6) literal_t create_ge_atom(void *solver, thvar_t x)
 *    - must create the atom (x >= 0) and return the corresponding literal
 *    - x is an existing theory variable in solver
 *
 * 7) literal_t create_poly_eq_atom(void *solver, polynomial_t *p, thvar_t *map)
 *    - must create the atom (p == 0) and return the corresponding literal
 *    - p and map are as in create_poly
 *
 * 8) literal_t create_poly_ge_atom(void *solver, polynomial_t *p, thvar_t *map)
 *    - must create the atom (p >= 0) and return the corresponding literal
 *    - p and map are as in create_poly
 *
 * 9) literal_t create_vareq_atom(void *solver, thvar_t x, thvar_t y)
 *    - create the atom x == y where x and y are two existing variables in solver
 *
 *
 * Assertion of top-level axioms
 * -----------------------------
 *
 * 10) void assert_eq_axiom(void *solver, thvar_t x, bool tt)
 *     - if tt assert (x == 0) otherwise assert (x != 0)
 *
 * 11) void assert_ge_axiom(void *solver, thvar_t x, bool tt)
 *     - if tt assert (x >= 0) otherwise assert (x < 0)
 *
 * 12) void assert_poly_eq_axiom(void *solver, polynomial_t *p, thvar_t *map, bool tt)
 *     - if tt assert (p == 0) otherwise assert (p != 0)
 *     - p and map are as in create_poly
 *
 * 13) void assert_poly_ge_axiom(void *solver, polynomial_t *p, thvar_t *map, bool tt)
 *     - if tt assert (p >= 0) otherwise assert (p < 0)
 *     - p and map are as in create_poly
 *
 * 14) void assert_vareq_axiom(void *solver, thvar_t x, thvar_t y, bool tt)
 *     - if tt assert x == y, otherwise assert x != y
 *
 * 15) void assert_cond_vareq_axiom(void *solver, literal_t c, thvar_t x, thvar_t y)
 *     - assert (c implies x == y) as an axiom
 *     - this is used to convert if-then-else equalities:
 *        (x == (ite c y1 y2)) is flattened to (c implies x = y1) and (not c implies x = y2)
 *
 * 15b) void assert_clause_vareq_axiom(void *solver, uint32_t n, literal_t *c, thvar_t x, thvar_t y)
 *     - assert (c[0] \/ ... \/ c[n-1] \/ x == y)
 *
 * Egraph connection
 * -----------------
 *
 * 16) void attach_eterm(void *solver, thvar_t v, eterm_t t)
 *    - attach egraph term t to theory variable v
 *    - this function may be omitted for standalone solvers (no egraph is used in that case)
 *
 * 17) eterm_t eterm_of_var(void *solver, thvar_t v)
 *    - must return the eterm t attached to v (if any) or null_eterm if v has no term attached
 *    - this function may be omitted for standalone solvers (no egraph)
 *
 * NOTE: these functions are also used by the egraph. They are required only if
 * the context includes both the egraph and the arithmetic solver.
 *
 *
 * Model construction
 * ------------------
 *
 * The following functions are used when the solver reaches SAT (or UNKNOWN).
 * First, build_model is called. The solver must construct an assignment M from variables to
 * rationals at that point. Then, the context can query for the value of a variable x in M.
 * If the solver cannot assign a rational value to x, it can signal this when value_in_model
 * is called. M must not be changed until the context calls free_model.
 *
 * 18) void build_model(void *solver)
 *    - build a model M: maps variable to rationals.
 *     (or do nothing if the solver does not support model construction).
 *
 * 19) bool value_in_model(void *solver, thvar_t x, rational_t *v)
 *    - must return true and copy the value of x in M into v if that value is available.
 *    - return false otherwise (e.g., if model construction is not supported by
 *    solver or x has an irrational value).
 *
 * 20) void free_model(void *solver)
 *    - notify solver that M is no longer needed.
 *
 *
 * Queries about variables
 * -----------------------
 *
 * 21) bool arith_var_is_int(void *solver, thvar_t x):
 *     - return true if x is an integer variable, false otherwise.
 *
 * 
 * Exception mechanism
 * -------------------
 * When the solver is created and initialized it's given a pointer b to a jmp_buf internal to
 * the context. If the solver fails in some way during internalization, it can call
 * longjmp(*b, error_code) to interrupt the internalization and return control to the
 * context. For arithmetic solvers, the following error codes should be used:
 *
 *   FORMULA_NOT_IDL         (the solver supports only integer difference logic)
 *   FORMULA_NOT_RDL         (the solver supports only real difference logic)
 *   FORMULA_NOT_LINEAR      (the solver supports only linear arithmetic)
 *   TOO_MANY_ARITH_VARS     (solver limit is reached)
 *   TOO_MANY_ARITH_ATOMS    (solver limit is reached)
 *   ARITHSOLVER_EXCEPTION   (any other failure)
 *
 */
typedef thvar_t (*create_arith_var_fun_t)(void *solver, bool is_int);
typedef thvar_t (*create_arith_const_fun_t)(void *solver, rational_t *q);
typedef thvar_t (*create_arith_poly_fun_t)(void *solver, polynomial_t *p, thvar_t *map);
typedef thvar_t (*create_arith_pprod_fun_t)(void *solver, pprod_t *p, thvar_t *map);

typedef literal_t (*create_arith_atom_fun_t)(void *solver, thvar_t x);
typedef literal_t (*create_arith_patom_fun_t)(void *solver, polynomial_t *p, thvar_t *map);
typedef literal_t (*create_arith_vareq_atom_fun_t)(void *solver, thvar_t x, thvar_t y);

typedef void (*assert_arith_axiom_fun_t)(void *solver, thvar_t x, bool tt);
typedef void (*assert_arith_paxiom_fun_t)(void *solver, polynomial_t *p, thvar_t *map, bool tt);
typedef void (*assert_arith_vareq_axiom_fun_t)(void *solver, thvar_t x, thvar_t y, bool tt);
typedef void (*assert_arith_cond_vareq_axiom_fun_t)(void* solver, literal_t c, thvar_t x, thvar_t y);
typedef void (*assert_arith_clause_vareq_axiom_fun_t)(void* solver, uint32_t n, literal_t *c, thvar_t x, thvar_t y);

typedef void    (*attach_eterm_fun_t)(void *solver, thvar_t v, eterm_t t);
typedef eterm_t (*eterm_of_var_fun_t)(void *solver, thvar_t v);

typedef void (*build_model_fun_t)(void *solver);
typedef void (*free_model_fun_t)(void *solver);
typedef bool (*arith_val_in_model_fun_t)(void *solver, thvar_t x, rational_t *v);

typedef bool (*arith_var_is_int_fun_t)(void *solver, thvar_t x);

typedef struct arith_interface_s {
  create_arith_var_fun_t create_var;
  create_arith_const_fun_t create_const;
  create_arith_poly_fun_t create_poly;
  create_arith_pprod_fun_t create_pprod;

  create_arith_atom_fun_t create_eq_atom;
  create_arith_atom_fun_t create_ge_atom;
  create_arith_patom_fun_t create_poly_eq_atom;
  create_arith_patom_fun_t create_poly_ge_atom;
  create_arith_vareq_atom_fun_t create_vareq_atom;

  assert_arith_axiom_fun_t assert_eq_axiom;
  assert_arith_axiom_fun_t assert_ge_axiom;
  assert_arith_paxiom_fun_t assert_poly_eq_axiom;
  assert_arith_paxiom_fun_t assert_poly_ge_axiom;
  assert_arith_vareq_axiom_fun_t assert_vareq_axiom;
  assert_arith_cond_vareq_axiom_fun_t assert_cond_vareq_axiom;
  assert_arith_clause_vareq_axiom_fun_t assert_clause_vareq_axiom;

  attach_eterm_fun_t attach_eterm;
  eterm_of_var_fun_t eterm_of_var;

  build_model_fun_t build_model;
  free_model_fun_t free_model;
  arith_val_in_model_fun_t value_in_model;

  arith_var_is_int_fun_t arith_var_is_int;
} arith_interface_t;



/********************************
 *  BITVECTOR SOLVER INTERFACE  *
 *******************************/

/*
 * Term constructors
 * -----------------
 * 1) thvar_t create_var(void *solver, uint32_t n)
 *    - must return the index of a new bitvector variable (no eterm attached)
 *    - n = number of bits of that variable
 *
 * 2a) thvar_t create_const(void *solver, bvconst_term_t *const)
 * 2b) thvar_t create_const64(void *solver, bvconst64_term_t *const)
 *    - must return the index of a variable x equal to the constant const
 *    - const->nbits = number of bits
 *    - const->bits = array of uint32_t words (constant value)
 *
 * 2c) thvar_t create_zero(void *solver, uint32_t n)
 *     - must create the zero constant of n bits
 *
 * 3a) thvar_t create_poly(void *solver, bvpoly_t *p, thvar_t *map)
 * 3b) thvar_t create_poly64(void *solver, bvpoly64_t *p, thvar_t *map)
 *    - must return a theory variable that represents p with variables renamed as
 *      defined by map:
 *      p is a_0 t_0 + ... + a_n t_n and map[i] = variable x_i mapped to t_i
 *      with the exception that map[0] = null_thvar if x_0 is const_idx
 *
 * 4) thvar_t create_pprod(void *solver, pprod_t *r, thvar_t *map)
 *    - return a theory variable to represent the product (t_0 ^ d_0 ... t_n ^ d_n)
 *    - map is an array of n+1 theory variables x_0 ... x_n such that
 *      x_i is mapped to t_i in the internalization table.
 *
 * 5) thvar_t create_bvarray(void *solver, literal_t *a, uint32_t n)
 *    - must return a theory variable that represent the array a[0 ... n-1]
 *    - a[0 ... n-1] are all literals in the core
 *    - a[0] is the low order bit, a[n-1] is the high order bit
 *
 * 6) thvar_t create_bvite(void *solver, literal_t c, thvar_t x, thvar_t y)
 *    - create (ite c x y): x and y are two theory variables in solver,
 *      and c is a literal in the core.
 *
 * 7) binary operators
 *    thvar_t create_bvdiv(void *solver, thvar_t x, thvar_t y)
 *    thvar_t create_bvrem(void *solver, thvar_t x, thvar_t y)
 *    thvar_t create_bvsdiv(void *solver, thvar_t x, thvar_t y)
 *    thvar_t create_bvsrem(void *solver, thvar_t x, thvar_t y)
 *    thvar_t create_bvsmod(void *solver, thvar_t x, thvar_t y)
 *    thvar_t create_bvshl(void *solver, thvar_t x, thvar_t y)
 *    thvar_t create_bvlshr(void *solver, thvar_t x, thvar_t y)
 *    thvar_t create_bvashr(void *solver, thvar_t x, thvar_t y)
 *
 * 8) bit extraction
 *    literal_t select_bit(void *solver, thvar_t x, uint32_t i)
 *    - must return bit i of theory variable x as a literal in the core
 *
 * Atom creation
 * -------------
 * 9) literal_t create_eq_atom(void *solver, thvar_t x, thvar_t y)
 * 10) literal_t create_ge_atom(void *solver, thvar_t x, thvar_t y)
 * 11) literal_t create_sge_atom(void *solver, thvar_t x, thvar_t y)
 *
 * Axiom assertion
 * ---------------
 * assert axiom if tt is true, the negation of axiom otherwise
 * 12) void assert_eq_axiom(void *solver, thvar_t x, thvar_t y, bool tt)
 * 13) void assert_ge_axiom(void *solver, thvar_t x, thvar_t y, bool tt)
 * 14) void assert_sge_axiom(void *solver, thvar_t x, thvar_t y, bool tt)
 *
 * 15) void set_bit(void *solver, thvar_t x, uint32_t i, bool tt)
 *   - assign bit i of x to true or false (depending on tt)
 *
 * Egraph interface
 * ----------------
 * 16) void attach_eterm(void *solver, thvar_t v, eterm_t t)
 *    - attach egraph term t to theory variable v of solver
 *
 * 17) eterm_t eterm_of_var(void *solver, thvar_t v)
 *    - return the egraph term attached to v in solver (or null_eterm
 *      if v has no egraph term attached).
 *
 * Model construction
 * ------------------
 * Same functions as for the arithmetic solvers
 *
 * 18) void build_model(void *solver)
 *     - build a model (that maps solver variables to bitvector constants)
 *
 * 19) void free_model(void *solver)
 *     - notify the solver that the model is no longer needed
 *
 * 20) bool value_in_model(void *solver, thvar_t x, bvconstant_t *v):
 *     - copy the value of x into v and return true.
 *     - if model construction is not supported or the value is not available, return false.
 */
typedef thvar_t (*create_bv_var_fun_t)(void *solver, uint32_t nbits);
typedef thvar_t (*create_bv_const_fun_t)(void *solver, bvconst_term_t *c);
typedef thvar_t (*create_bv64_const_fun_t)(void *solver, bvconst64_term_t *c);
typedef thvar_t (*create_bv_zero_fun_t)(void *solver, uint32_t nbits);
typedef thvar_t (*create_bv_poly_fun_t)(void *solver, bvpoly_t *p, thvar_t *map);
typedef thvar_t (*create_bv64_poly_fun_t)(void *solver, bvpoly64_t *p, thvar_t *map);
typedef thvar_t (*create_bv_pprod_fun_t)(void *solver, pprod_t *p, thvar_t *map);
typedef thvar_t (*create_bv_array_fun_t)(void *solver, literal_t *a, uint32_t n);
typedef thvar_t (*create_bv_ite_fun_t)(void *solver, literal_t c, thvar_t x, thvar_t y);
typedef thvar_t (*create_bv_binop_fun_t)(void *solver, thvar_t x, thvar_t y);
typedef literal_t (*create_bv_atom_fun_t)(void *solver, thvar_t x, thvar_t y);
typedef literal_t (*select_bit_fun_t)(void *solver, thvar_t x, uint32_t i);
typedef void (*assert_bv_axiom_fun_t)(void *solver, thvar_t x, thvar_t y, bool tt);
typedef void (*set_bit_fun_t)(void *solver, thvar_t x, uint32_t i, bool tt);
typedef bool (*bv_val_in_model_fun_t)(void *solver, thvar_t x, bvconstant_t *v);

typedef struct bv_interface_s {
  create_bv_var_fun_t create_var;
  create_bv_const_fun_t create_const;
  create_bv64_const_fun_t create_const64;
  create_bv_zero_fun_t create_zero;
  create_bv_poly_fun_t create_poly;
  create_bv64_poly_fun_t create_poly64;
  create_bv_pprod_fun_t create_pprod;
  create_bv_array_fun_t create_bvarray;
  create_bv_ite_fun_t create_bvite;
  create_bv_binop_fun_t create_bvdiv;
  create_bv_binop_fun_t create_bvrem;
  create_bv_binop_fun_t create_bvsdiv;
  create_bv_binop_fun_t create_bvsrem;
  create_bv_binop_fun_t create_bvsmod;
  create_bv_binop_fun_t create_bvshl;
  create_bv_binop_fun_t create_bvlshr;
  create_bv_binop_fun_t create_bvashr;

  select_bit_fun_t select_bit;
  create_bv_atom_fun_t create_eq_atom;
  create_bv_atom_fun_t create_ge_atom;
  create_bv_atom_fun_t create_sge_atom;

  assert_bv_axiom_fun_t assert_eq_axiom;
  assert_bv_axiom_fun_t assert_ge_axiom;
  assert_bv_axiom_fun_t assert_sge_axiom;
  set_bit_fun_t set_bit;

  attach_eterm_fun_t attach_eterm;
  eterm_of_var_fun_t eterm_of_var;

  build_model_fun_t build_model;
  free_model_fun_t free_model;
  bv_val_in_model_fun_t value_in_model;
} bv_interface_t;



/******************************
 *  DIFFERENCE LOGIC PROFILE  *
 *****************************/

/*
 * For difference logic, we can use either the simplex solver
 * or a specialized Floyd-Warshall solver. The decision is
 * based on the following parameters:
 * - density = number of atoms / number of variables
 * - path_bound = an upper bound on the length of any simple
 *                path between two variables
 * - num_eqs = number of equalities (among all atoms)
 * dl_data stores the relevant data
 */
typedef struct dl_data_s {
  rational_t path_bound;
  uint32_t num_vars;
  uint32_t num_atoms;
  uint32_t num_eqs;
} dl_data_t;





/**************
 *  CONTEXT   *
 *************/

struct context_s {
  // mode + architecture + logic code
  context_mode_t mode;
  context_arch_t arch;
  smt_logic_t logic;

  // theories flag
  uint32_t theories;

  // options flag
  uint32_t options;

  // base_level == number of calls to push
  uint32_t base_level;

  // core and theory solvers
  smt_core_t *core;
  egraph_t *egraph;
  mcsat_solver_t *mcsat;
  void *arith_solver;
  void *bv_solver;
  void *fun_solver;
  void *quant_solver;

  // solver internalization interfaces
  arith_interface_t arith;
  bv_interface_t bv;

  // input are all from the following tables (from yices_globals.h)
  type_table_t *types;
  term_table_t *terms;

  // hash table for Boolean gates
  gate_manager_t gate_manager;

  // internalization table
  intern_tbl_t intern;

  // result of flattening and simplification
  ivector_t top_eqs;
  ivector_t top_atoms;
  ivector_t top_formulas;
  ivector_t top_interns;

  // auxiliary buffers and structures for internalization
  ivector_t subst_eqs;
  ivector_t aux_eqs;
  ivector_t aux_atoms;
  ivector_t aux_vector;
  int_queue_t queue;
  int_stack_t istack;
  objstack_t ostack;

  // data about shared subterms
  sharing_map_t sharing;

  // store for the conditional descriptors
  object_store_t cstore;

  // assumption stack
  assumption_stack_t assumptions;

  // optional components: allocated if needed
  pseudo_subst_t *subst;
  mark_vector_t *marks;
  int_bvset_t *cache;
  int_hset_t *small_cache;
  int_rat_hmap_t *edge_map;
  pmap2_t *eq_cache;
  divmod_tbl_t *divmod_table;
  bfs_explorer_t *explorer;

  // buffer to store difference-logic data
  dl_data_t *dl_profile;

  // buffers for arithmetic simplification/internalization
  rba_buffer_t *arith_buffer;
  poly_buffer_t *poly_buffer;
  polynomial_t *aux_poly;
  uint32_t aux_poly_size;  // number of monomials in aux_poly

  // buffers for bitvector simplification
  bvpoly_buffer_t *bvpoly_buffer;

  // auxiliary buffers for model construction
  rational_t aux;
  bvconstant_t bv_buffer;

  // for exception handling
  jmp_buf env;

  // for verbose output (default NULL)
  tracer_t *trace;

  // options for the mcsat solver
  mcsat_options_t mcsat_options;
  // ordering for forcing mcsat assignment order
  ivector_t mcsat_var_order;

  // flag for enabling adding quant instances
  bool en_quant;
};



/*
 * Default initial size of auxiliary buffers and vectors
 */
#define CTX_DEFAULT_VECTOR_SIZE 10


/*
 * Default initial size for the solvers
 */
#define CTX_DEFAULT_CORE_SIZE 100


/*
 * Error and return codes used by internalization procedures:
 * - negative codes indicate an error
 * - these codes can also be used by the theory solvers to report exceptions.
 */
enum {
  TRIVIALLY_UNSAT = 1,   // simplifies to false
  CTX_NO_ERROR = 0,      // internalization succeeds/not solved
  // bugs
  INTERNAL_ERROR = -1,
  TYPE_ERROR = -2,
  // general errors
  FREE_VARIABLE_IN_FORMULA = -3,
  LOGIC_NOT_SUPPORTED = -4,  
  UF_NOT_SUPPORTED = -5,
  SCALAR_NOT_SUPPORTED = -6,
  TUPLE_NOT_SUPPORTED = -7,
  UTYPE_NOT_SUPPORTED = -8,
  ARITH_NOT_SUPPORTED = -9,
  BV_NOT_SUPPORTED = -10,
  FUN_NOT_SUPPORTED = -11,
  QUANTIFIERS_NOT_SUPPORTED = -12,
  LAMBDAS_NOT_SUPPORTED = -13,
  // arithmetic solver errors
  FORMULA_NOT_IDL = -14,
  FORMULA_NOT_RDL = -15,
  FORMULA_NOT_LINEAR = -16,
  DIV_BY_ZERO = -17,
  TOO_MANY_ARITH_VARS = -18,
  TOO_MANY_ARITH_ATOMS = -19,
  ARITHSOLVER_EXCEPTION = -20,
  // bv solver errors
  BVSOLVER_EXCEPTION = -21,
  // mcsat errors
  MCSAT_EXCEPTION_UNSUPPORTED_THEORY = -22,
  // new code: added 2021/06/29
  HIGH_ORDER_FUN_NOT_SUPPORTED = -23,
};


/*
 * NUM_INTERNALIZATION_ERRORS: must be (1 + number of negative codes)
 */
#define NUM_INTERNALIZATION_ERRORS 24



#endif /* __CONTEXT_TYPES_H */
