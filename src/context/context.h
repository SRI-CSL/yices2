/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CONTEXT
 */

#ifndef __CONTEXT_H
#define __CONTEXT_H

#include <stdint.h>
#include <stdbool.h>
#include <setjmp.h>

#include "yices_types.h"

#include "utils/int_queues.h"
#include "utils/int_stack.h"
#include "utils/int_vectors.h"
#include "utils/int_hash_sets.h"
#include "utils/int_bv_sets.h"
#include "utils/mark_vectors.h"
#include "utils/pair_hash_map2.h"
#include "terms/poly_buffer.h"
#include "io/tracer.h"

#include "terms/terms.h"
#include "terms/conditionals.h"
#include "context/internalization_table.h"
#include "context/internalization_codes.h"
#include "context/pseudo_subst.h"

#include "api/smt_logic_codes.h"
#include "api/search_parameters.h"
#include "solvers/cdcl/gates_manager.h"
#include "solvers/cdcl/smt_core.h"
#include "solvers/egraph/egraph.h"
#include "model/models.h"



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
 *
 * BREAKSYM for QF_UF is based on the paper by Deharbe et al (CADE 2011)
 *
 * PSEUDO_INVERSE is based on Brummayer's thesis (Boolector stuff)
 * - not implemented yet
 *
 * ITE_BOUNDS: for a special if-then-else termt t (i.e., if-then-else
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

#define PREPROCESSING_OPTIONS_MASK \
 (VARELIM_OPTION_MASK|FLATTENOR_OPTION_MASK|FLATTENDISEQ_OPTION_MASK|\
  EQABSTRACT_OPTION_MASK|ARITHELIM_OPTION_MASK|KEEP_ITE_OPTION_MASK|\
  BVARITHELIM_OPTION_MASK|BREAKSYM_OPTION_MASK|PSEUDO_INVERSE_OPTION_MASK|\
  ITE_BOUNDS_OPTION_MASK|CONDITIONAL_DEF_OPTION_MASK)

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
} context_arch_t;


#define NUM_ARCH (CTX_ARCH_AUTO_RDL+1)


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
 *    - this must return a theory variable equal to p with variable renamed as
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
 * - sum_const = sum of the absolute values of all constants in the
 *   difference logic atoms
 * - num_eqs = number of equalities (among all atoms)
 * dl_data stores the relevant data
 */
typedef struct dl_data_s {
  rational_t sum_const;
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
  void *arith_solver;
  void *bv_solver;
  void *fun_solver;

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

  // store for the conditional descriptors
  object_store_t cstore;

  // optional components: allocated if needed
  pseudo_subst_t *subst;
  mark_vector_t *marks;
  int_bvset_t *cache;
  int_hset_t *small_cache;
  pmap2_t *eq_cache;

  // buffer to store difference-logic data
  dl_data_t *dl_profile;

  // buffers for arithmetic simplification/internalization
  rba_buffer_t *arith_buffer;
  poly_buffer_t *poly_buffer;
  polynomial_t *aux_poly;
  uint32_t aux_poly_size;  // number of monomials in aux_poly

  // auxiliary buffers for model construction
  rational_t aux;
  bvconstant_t bv_buffer;

  // for exception handling
  jmp_buf env;

  // for verbose output (default NULL)
  tracer_t *trace;
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
  ARITH_NOT_SUPPORTED = -6,
  BV_NOT_SUPPORTED = -7,
  FUN_NOT_SUPPORTED = -8,
  QUANTIFIERS_NOT_SUPPORTED = -9,
  LAMBDAS_NOT_SUPPORTED = -10,
  // arithmetic solver errors
  FORMULA_NOT_IDL = -11,
  FORMULA_NOT_RDL = -12,
  FORMULA_NOT_LINEAR = -13,
  TOO_MANY_ARITH_VARS = -14,
  TOO_MANY_ARITH_ATOMS = -15,
  ARITHSOLVER_EXCEPTION = -16,
  // bv solver errors
  BVSOLVER_EXCEPTION = -17,
};


/*
 * NUM_INTERNALIZATION_ERRORS: must be (1 + number of negative codes)
 */
#define NUM_INTERNALIZATION_ERRORS 18





/********************************
 *  INITIALIZATION AND CONTROL  *
 *******************************/

/*
 * Initialize ctx for the given logic, mode, and architecture
 * - terms = term table for this context
 * - qflag = false means quantifier-free variant
 * - qflag = true means quantifiers allowed
 * If arch is one of the ARCH_AUTO_... variants, then mode must be ONECHECK
 */
extern void init_context(context_t *ctx, term_table_t *terms, smt_logic_t logic,
                         context_mode_t mode, context_arch_t arch, bool qflag);


/*
 * Deletion
 */
extern void delete_context(context_t *ctx);


/*
 * Reset: remove all assertions
 */
extern void reset_context(context_t *ctx);


/*
 * Set the trace:
 * - the current tracer must be NULL.
 * - the tracer is also attached to the context's smt_core
 *   (so all solvers can use it to print stuff).
 */
extern void context_set_trace(context_t *ctx, tracer_t *trace);


/*
 * Push and pop
 * - should not be used if the push_pop option is disabled
 */
extern void context_push(context_t *ctx);
extern void context_pop(context_t *ctx);




/**********************************
 *  SIMPLIFICATION AND UTILITIES  *
 *********************************/

/*
 * The following functions are implemented in context_simplifier.c.
 * They can be used by any procedure that processes assertions but does
 * not depend on the solvers instantiated in a conterxt.
 */

/*
 * INTERNAL CACHES AND AUXILIARY STRUCTURES
 */

/*
 * There are two internal caches for visiting terms.
 * - the 'cache' uses a bitvector implementation and should be
 *   better for operations that visit many terms.
 * - the 'small_cache' uses a hash table and should be better
 *   for operations that visit a small number of terms.
 *
 * There are three buffers for internal construction of polynomials
 * - arith_buffer is more expensive (requires more memory) but
 *   it supports more operations (e.g., term constructors in yices_api.c
 *   take arith_buffers as arguments).
 * - poly_buffer is a cheaper data structure, but it does not support
 *   all the operations
 * - aux_poly is even cheaper, but it's for direct construction only
 */

/*
 * Allocate/reset/free the small cache
 * - the cache is allocated and initialized on the first call to get_small_cache
 * - reset and free do nothing if the cache is not allocated
 */
extern int_hset_t *context_get_small_cache(context_t *ctx);
extern void context_reset_small_cache(context_t *ctx);
extern void context_free_small_cache(context_t *ctx);


/*
 * Allocate/free the cache
 * - same conventions as for the small_cache
 */
extern int_bvset_t *context_get_cache(context_t *ctx);
extern void context_free_cache(context_t *ctx);


/*
 * Buffers for polynomials
 */
extern rba_buffer_t *context_get_arith_buffer(context_t *ctx);
extern void context_free_arith_buffer(context_t *ctx);

extern poly_buffer_t *context_get_poly_buffer(context_t *ctx);
extern void context_free_poly_buffer(context_t *ctx);
extern void context_reset_poly_buffer(context_t *ctx);


/*
 * Allocate the auxiliary polynomial buffer and make it large enough
 * for n monomials.
 */
extern polynomial_t *context_get_aux_poly(context_t *ctx, uint32_t n);

/*
 * Free the auxiliary polynomial
 */
extern void context_free_aux_poly(context_t *ctx);



/*
 * EQUALITY CACHE
 */

/*
 * If lift-if is enabled then arithmetic equalities
 *  (eq (ite c t1 t2) u) are rewritten to (ite c (eq t1 u) (eq t2 u))
 * We don't create new terms (eq t1 u) or (eq t2 u). Instead, we store
 * the internalization of equalities (eq t1 u) in the eq_cache:
 * This cache maps pairs of terms <t, u> to a literal l (such that
 * l is the internalization of (t == u)).
 *
 * The following functions operate on this cache: reset/free/push/pop
 * do nothing if the cache does not exist.
 */
extern pmap2_t *context_get_eq_cache(context_t *ctx);
extern void context_free_eq_cache(context_t *ctx);
extern void context_eq_cache_push(context_t *ctx);
extern void context_eq_cache_pop(context_t *ctx);

static inline void context_reset_eq_cache(context_t *ctx) {
  context_free_eq_cache(ctx);
}


/*
 * Check what's mapped to (t1, t2) in the internal eq_cache.
 * - return null_literal if nothing is mapped to (t1, t2) (or if the cache does not exit)
 */
extern literal_t find_in_eq_cache(context_t *ctx, term_t t1, term_t t2);


/*
 * Add the mapping (t1, t2) --> l to the equality cache.
 * - allocate and initialize the cache if needed.
 * - the pair (t1, t2) must not be in the cache already.
 * - l must be different from null_literal
 */
extern void add_to_eq_cache(context_t *ctx, term_t t1, term_t t2, literal_t l);



/*
 * SIMPLIFICATION
 */

/*
 * Check whether t is true or false (i.e., mapped to 'true_occ' or 'false_occ'
 * in the internalization table.
 * - t must be a root in the internalization table
 */
extern bool term_is_true(context_t *ctx, term_t t);
extern bool term_is_false(context_t *ctx, term_t t);


/*
 * Check whether (t1 == t2) can be simplified to an existing term
 * (including true_term or false_term).
 * - t1 and t2 must be Boolean terms
 * - return NULL_TERM if no simplifcation is found
 */
extern term_t simplify_bool_eq(context_t *ctx, term_t t1, term_t t2);


/*
 * Same thing for bitvector terms
 * - both t1 and t2 must be root terms in the internalization table
 */
extern term_t simplify_bitvector_eq(context_t *ctx, term_t t1, term_t t2);



/*
 * FLATTENING AND VARIABLE ELIMINATION
 */

/*
 * Flattening of disjunctions
 * - rewrite nested OR terms to flat OR terms
 * - if option FLATTENDISEQ is enabled, also replace arithmetic
 *   disequalities by disjunctions of strict inequalities:
 *    (i.e., rewrite x!= 0 to (or (< x 0) (> x 0))
 *
 * The function applies flattenning to composite term or:
 * - or must be of the form (or t1 .... tn)
 * - v must be empty
 * - flattening is applied recursively to t1 ... t_n
 * - the result is stored in v: it 's an array of Boolean terms
 *   u_1 .... u_m such that (or t1 ... t_n)  is equivalent to (or u_1 ... u_m).
 *
 * Side effect: use ctx's small_cache then reset it
 */
extern void flatten_or_term(context_t *ctx, ivector_t *v, composite_term_t *or);


/*
 * If t is (ite c a b), we can try to rewrite (= t k) into a conjunction
 * of terms using the two rules:
 *   (= (ite c a b) k) --> c and (= a k)        if k != b holds
 *   (= (ite c a b) k) --> (not c) and (= b k)  if k != a holds
 *
 * This works best for the NEC benchmarks in SMT LIB, where many terms
 * are deeply nested if-then-else terms with constant leaves.
 *
 * The function below does that: it rewrites (eq t k) to (and c_0 ... c_n (eq t' k))
 * - the boolean terms c_0 ... c_n are added to vector v
 * - the term t' is returned
 *
 * So the simplification worked it the returned term t' is different from t
 * (and then v->size is not 0).
 */
extern term_t flatten_ite_equality(context_t *ctx, ivector_t *v, term_t t, term_t k);


/*
 * Simplify and flatten assertion f.
 *
 * This function performs top-down Boolean propagation and collects
 * all subterms of f that can't be flattened into four vectors:
 *
 * 1) ctx->top_eqs = top-level equalities.
 *    Every t in top_eqs is (eq t1 * t2) (or a variant) asserted true.
 *    t is mapped to true in the internalization table.
 *
 * 2) ctx->top_atoms = top-level atoms.
 *    Every t in top_atoms is an atom or the negation of an atom (that
 *    can't go into top_eqs).
 *    t is mapped to true in the internalization table.
 *
 * 3) ctx->top_formulas = non-atomic terms.
 *    Every t in top_formulas is either an (OR ...) or (ITE ...) or (XOR ...)
 *    or the negation of such a term.
 *    t is mapped to true in the internalization table.
 *
 * 4) ctx->top_interns = already internalized terms.
 *    Every t in top_interns is a term that's been internalized before
 *    and is mapped to a literal l or an egraph occurrence g in
 *    the internalization table.
 *    l or g must be asserted true in later stages.
 *
 *
 * If variable elimination is enabled, then equalities of the form (= x t)
 * where x is a variable are converted to substitutions if possible:
 *
 * 1) if t is a constant or variable: then [x := t] is added as a substitution
 *    to ctx->intern_tbl (if possible)
 *
 * 2) other equalities of the form (= x t) are added to ctx->subst_eqs. to
 *    be processed later by process_candidate_subst
 *
 * This function raises an exception via longjmp if there's an error
 * or if a contradiction is detected. So ctx->env must be set.
 */
extern void flatten_assertion(context_t *ctx, term_t f);


/*
 * Auxiliary equalities:
 * - add a new equality (x == y) in the aux_eq vector.
 * - this is useful for simplification procedures that are executed after
 *   assertion flattening (e.g., symmetry breaking).
 * - the auxiliary equalities can then be processed by process_aux_eqs
 */
extern void add_aux_eq(context_t *ctx, term_t x, term_t y);


/*
 * Process the auxiliary equalities:
 * - if substitution is not enabled, then all aux equalities are added to top_eqs
 * - otherwise, cheap substitutions are performand and candidate substitutions
 *   are added to subst_eqs.
 *
 * This function raises an exception via longjmp if a contradiction os detected.
 */
extern void process_aux_eqs(context_t *ctx);


/*
 * Process all candidate substitutions after flattening and processing of
 * auxiliary equalities.
 * - the candidate substitutions are in ctx->subst_eqs
 * - all elemenst of subst_eqs must be equality terms asserted true
 *   and of the form (= x t) for some variable x.
 * - converts these equalities into substitutions, as long as this
 *   can be done without creating substitution cycles.
 * - candidate substitution  that can't be converted are moved to
 *   ctx->top_eqs.
 */
extern void context_process_candidate_subst(context_t *ctx);


/*
 * Auxiliary atoms:
 * - add atom a to the aux_atoms vector
 * - the auxiliary atom can be processed later by process_aux_atoms
 */
extern void add_aux_atom(context_t *ctx, term_t atom);


/*
 * Process the auxiliary atoms:
 * - take all atoms in ctx->aux_atoms and assert them
 *   (map them to true and add them to ctx->top_atoms)
 * - if there's a trivial contradiction: an atom is both
 *   asserted true and false, this function raises an exception
 *   via longjmp
 */
extern void process_aux_atoms(context_t *ctx);



/*
 * TYPES AFTER VARIABLE ELIMINATION
 */

/*
 * Get the type of r's class
 * - r must be a root in the internalization table
 */
static inline type_t type_of_root(context_t *ctx, term_t r) {
  return intern_tbl_type_of_root(&ctx->intern, r);
}

/*
 * Check whether r is root of an integer class
 * - r must be a root in the internalization table
 */
static inline bool is_integer_root(context_t *ctx, term_t r) {
  return intern_tbl_is_integer_root(&ctx->intern, r);
}


/*
 * Check whether t is in an integer or real class
 */
static inline bool in_integer_class(context_t *ctx, term_t t) {
  return is_integer_root(ctx, intern_tbl_get_root(&ctx->intern, t));
}

static inline bool in_real_class(context_t *ctx, term_t t) {
  return is_real_type(type_of_root(ctx, intern_tbl_get_root(&ctx->intern, t)));
}



/*
 * PREPROCESSING/ANALYSIS AFTER FLATTENING
 */

/*
 * Attempt to learn global equalities implied
 * by the formulas stored in ctx->top_formulas.
 * Any such equality is added to ctx->aux_eqs
 */
extern void analyze_uf(context_t *ctx);


/*
 * Check difference logic after flattening:
 * - check whether all formulas in top_eqs, top_atoms, and top_formulas
 *   are in the difference logic fragment. If so, compute the benchmark
 *   profile (i.e., statistics on number of variables + atoms)
 * - if idl is true, all variables must be integer (i.e., the formula is
 *   in the IDL fragment), otherwise all variables must be real (i.e., the
 *   formula is in the RDL fragment).
 *
 * - if all assertions are in IDL or RDL.
 *   the statistics are stored in ctx->dl_profile.
 * - raise an exception 'LOGIC_NOT_SUPPORTED' otherwise.
 *
 * This function is used to decide whether to use simplex or a
 * specialized solver when the architecture is CTX_AUTO_IDL or
 * CTX_AUTO_RDL.  Because this function is called before the actual
 * arithmetic solver is created, we assume that no arithmetic term is
 * internalized, and that top_interns is empty.
 */
extern void analyze_diff_logic(context_t *ctx, bool idl);


/*
 * Break symmetries for uf theory: this is based on the following paper:
 *
 *   David Delharbe, Pascal Fontaine, Stephan Merz, and Bruno Woltzenlogel Paleo
 *   Exploiting Summetry in SMT Problems, CADE 2011
 *
 * Summary:
 * - search for clauses of the form (or (= t c0) ... (= t c_n))
 *   where c0 ... c_n are uninterpreted constants
 * - reduce the clause to (or (= t c0) .. (= t c_i)) for some i<n
 * - this can be done if the rest of the assertions are invariant
 *   with respect to permutations of c0 ... c_n, and if t doesn't
 *   contain c0 ... c_i.
 */
extern void break_uf_symmetries(context_t *ctx);


/*
 * Preprocessing of conditional definitions
 */
extern void process_conditional_definitions(context_t *ctx);



/*
 * CLEANUP
 */

/*
 * Subst/mark are used by flattening if variable elimination is
 * enabled. The dl_profile is allocated in analyze_diff_logic. The
 * following functions must be called to delete these internal
 * structures. They do nothing if the structures haven't been
 * allocated.
 */
extern void context_free_subst(context_t *ctx);
extern void context_free_marks(context_t *ctx);
extern void context_free_dl_profile(context_t *ctx);


/*
 * CONDITIONALS/FLATTENING OF NESTED IF-THEN-ELSE
 */

/*
 * Attempt to convert an if-then-else term to a conditional
 * - return NULL if the conversion fails
 * - return a conditional descriptor otherwise
 * - if NON-NULL, the result must be freed when no-longer used
 *   by calling context_free_conditional
 */
extern conditional_t *context_make_conditional(context_t *ctx, composite_term_t *ite);

/*
 * Free a conditional descriptor returned by the previous function
 */
extern void context_free_conditional(context_t *ctx, conditional_t *d);


/*
 * Check whether conditional_t *d can be simplified
 * - d is of the form
 *    COND c1 --> a1
 *         c2 --> a2
 *         ...
 *         else --> b
 *    END
 *   where c_1 ... c_n are pairwise disjoint
 *
 * - if one of c_i is true, the function returns a_i
 * - if all c_i's are false, the function returns d
 * - in all other cases, the function returns NULL_TERM
 */
extern term_t simplify_conditional(context_t *ctx, conditional_t *d);



/****************************
 *   ASSERTIONS AND CHECK   *
 ***************************/

/*
 * Assert a boolean formula f.
 *
 * The context status must be IDLE.
 *
 * Return code:
 * - TRIVIALLY_UNSAT means that an inconsistency is detected
 *   (in that case the context status is set to UNSAT)
 * - CTX_NO_ERROR means no internalization error and status not
 *   determined
 * - otherwise, the code is negative. The assertion could
 *   not be processed.
 */
extern int32_t assert_formula(context_t *ctx, term_t f);


/*
 * Assert all formulas f[0] ... f[n-1]
 * same return code as above.
 */
extern int32_t assert_formulas(context_t *ctx, uint32_t n, const term_t *f);


/*
 * Convert boolean term t to a literal l in context ctx
 * - return a negative code if there's an error
 * - return a literal (l >= 0) otherwise.
 */
extern int32_t context_internalize(context_t *ctx, term_t t);


/*
 * Add the blocking clause to ctx
 * - ctx->status must be either SAT or UNKNOWN
 * - this collects all decision literals in the current truth assignment
 *   (say l_1, ..., l_k) then clears the current assignment and adds the
 *  clause ((not l_1) \/ ... \/ (not l_k)).
 *
 * Return code:
 * - TRIVIALLY_UNSAT: means that the blocking clause is empty (i.e., k = 0)
 *   (in that case, the context status is set to UNSAT)
 * - CTX_NO_ERROR: means that the blocking clause is not empty (i.e., k > 0)
 *   (In this case, the context status is set to IDLE)
 */
extern int32_t assert_blocking_clause(context_t *ctx);


/*
 * Check whether the context is consistent
 * - parameters = search and heuristic parameters to use
 * - if parameters is NULL, the default values are used
 *
 * return status: either STATUS_UNSAT, STATUS_SAT, STATUS_UNKNOWN,
 * STATUS_INTERRUPTED (these codes are defined in smt_core.h)
 */
extern smt_status_t check_context(context_t *ctx, const param_t *parameters);


/*
 * Build a model: the context's status must be STATUS_SAT or STATUS_UNKNOWN
 * - model must be initialized (and empty)
 * - the model maps a value to every uninterpreted terms present in ctx's
 *   internalization tables
 * - if model->has_alias is true, the term substitution defined by ctx->intern_tbl
 *   is copied into the model
 */
extern void context_build_model(model_t *model, context_t *ctx);


/*
 * Interrupt the search
 * - this can be called after check_context from a signal handler
 * - this interrupts the current search
 * - if clean_interrupt is enabled, calling context_cleanup will
 *   restore the solver to a good state, equivalent to the state
 *   before the call to check_context
 * - otherwise, the solver is in a bad state from which new assertions
 *   can't be processed. Cleanup is possible via pop (if push/pop is supported)
 *   or reset.
 */
extern void context_stop_search(context_t *ctx);


/*
 * Cleanup after check is interrupted
 * - must not be called if the clean_interrupt option is disabled
 * - restore the context to a good state (status = IDLE)
 */
extern void context_cleanup(context_t *ctx);


/*
 * Clear boolean assignment and return to the IDLE state.
 * - this can be called after check returns UNKNOWN or SEARCHING
 *   provided the context's mode isn't ONECHECK
 * - after this call, additional formulas can be asserted and
 *   another call to check_context is allowed. Model construction
 *   is no longer possible until the next call to check_context.
 */
extern void context_clear(context_t *ctx);


/*
 * Cleanup after the search returned UNSAT
 * - if the clean_interrupt option is enabled, this restore
 *   the state to what it was at the start of search
 * - otherwise, this does nothing.
 *
 * NOTE: Call this before context_pop(ctx) if the context status
 * is unsat.
 */
extern void context_clear_unsat(context_t *ctx);


/*
 * Precheck: force generation of clauses and other stuff that's
 * constructed lazily by the solvers. For example, this
 * can be used to convert all the constraints asserted in the
 * bitvector to clauses so that we can export the result to DIMACS.
 *
 * If ctx status is IDLE:
 * - the function calls 'start_search' and does one round of propagation.
 * - if this results in UNSAT, the function returns UNSAT
 * - otherwise the function returns UNKNOWN and restore the status to
 *   IDLE
 *
 * If ctx status is not IDLE, the function returns it and does nothing
 * else.
 */
extern smt_status_t precheck_context(context_t *ctx);

/*
 * FOR TESTING/DEBUGGING
 */

/*
 * Preprocess formula f or array of formulas f[0 ... n-1]
 * - this does flattening + build substitutions
 * - return code: as in assert_formulas
 * - the result is stored in the internal vectors
 *     ctx->top_interns
 *     ctx->top_eqs
 *     ctx->top_atoms
 *     ctx->top_formulas
 *   + ctx->intern stores substitutions
 */
extern int32_t context_process_formula(context_t *ctx, term_t f);
extern int32_t context_process_formulas(context_t *ctx, uint32_t n, term_t *f);



/*****************************
 *  INTERNALIZATION OPTIONS  *
 ****************************/

/*
 * Set or clear preprocessing options
 */
static inline void enable_variable_elimination(context_t *ctx) {
  ctx->options |= VARELIM_OPTION_MASK;
}

static inline void disable_variable_elimination(context_t *ctx) {
  ctx->options &= ~VARELIM_OPTION_MASK;
}

static inline void enable_or_flattening(context_t *ctx) {
  ctx->options |= FLATTENOR_OPTION_MASK;
}

static inline void disable_or_flattening(context_t *ctx) {
  ctx->options &= ~FLATTENOR_OPTION_MASK;
}

static inline void enable_diseq_and_or_flattening(context_t *ctx) {
  ctx->options |= FLATTENOR_OPTION_MASK|FLATTENDISEQ_OPTION_MASK;
}

static inline void disable_diseq_and_or_flattening(context_t *ctx) {
  ctx->options &= ~(FLATTENOR_OPTION_MASK|FLATTENDISEQ_OPTION_MASK);
}

static inline void enable_eq_abstraction(context_t *ctx) {
  ctx->options |= EQABSTRACT_OPTION_MASK;
}

static inline void disable_eq_abstraction(context_t *ctx) {
  ctx->options &= ~EQABSTRACT_OPTION_MASK;
}

static inline void enable_arith_elimination(context_t *ctx) {
  ctx->options |= ARITHELIM_OPTION_MASK;
}

static inline void disable_arith_elimination(context_t *ctx) {
  ctx->options &= ~ARITHELIM_OPTION_MASK;
}

static inline void enable_keep_ite(context_t *ctx) {
  ctx->options |= KEEP_ITE_OPTION_MASK;
}

static inline void disable_keep_ite(context_t *ctx) {
  ctx->options &= ~KEEP_ITE_OPTION_MASK;
}

static inline void enable_bvarith_elimination(context_t *ctx) {
  ctx->options |= BVARITHELIM_OPTION_MASK;
}

static inline void disable_bvarith_elimination(context_t *ctx) {
  ctx->options &= ~BVARITHELIM_OPTION_MASK;
}

static inline void enable_symmetry_breaking(context_t *ctx) {
  ctx->options |= BREAKSYM_OPTION_MASK;
}

static inline void disable_symmetry_breaking(context_t *ctx) {
  ctx->options &= ~BREAKSYM_OPTION_MASK;
}

static inline void enable_pseudo_inverse_simplification(context_t *ctx) {
  ctx->options |= PSEUDO_INVERSE_OPTION_MASK;
}

static inline void disable_pseudo_inverse_simplification(context_t *ctx) {
  ctx->options &= ~PSEUDO_INVERSE_OPTION_MASK;
}

static inline void enable_assert_ite_bounds(context_t *ctx) {
  ctx->options |= ITE_BOUNDS_OPTION_MASK;
}

static inline void disable_assert_ite_bounds(context_t *ctx) {
  ctx->options &= ~ITE_BOUNDS_OPTION_MASK;
}

static inline void enable_cond_def_preprocessing(context_t *ctx) {
  ctx->options |= CONDITIONAL_DEF_OPTION_MASK;
}

static inline void disable_cond_def_preprocessing(context_t *ctx) {
  ctx->options &= ~CONDITIONAL_DEF_OPTION_MASK;
}


/*
 * Simplex-related options
 */
extern void enable_splx_eager_lemmas(context_t *ctx);
extern void disable_splx_eager_lemmas(context_t *ctx);
extern void enable_splx_periodic_icheck(context_t *ctx);
extern void disable_splx_periodic_icheck(context_t *ctx);
extern void enable_splx_eqprop(context_t *ctx);
extern void disable_splx_eqprop(context_t *ctx);


/*
 * Check which options are enabled
 */
static inline bool context_var_elim_enabled(context_t *ctx) {
  return (ctx->options & VARELIM_OPTION_MASK) != 0;
}

static inline bool context_flatten_or_enabled(context_t *ctx) {
  return (ctx->options & FLATTENOR_OPTION_MASK) != 0;
}

static inline bool context_flatten_diseq_enabled(context_t *ctx) {
  return (ctx->options & FLATTENDISEQ_OPTION_MASK) != 0;
}

static inline bool context_eq_abstraction_enabled(context_t *ctx) {
  return (ctx->options & EQABSTRACT_OPTION_MASK) != 0;
}

static inline bool context_arith_elim_enabled(context_t *ctx) {
  return (ctx->options & ARITHELIM_OPTION_MASK) != 0;
}

static inline bool context_keep_ite_enabled(context_t *ctx) {
  return (ctx->options & KEEP_ITE_OPTION_MASK) != 0;
}

static inline bool context_bvarith_elim_enabled(context_t *ctx) {
  return (ctx->options & BVARITHELIM_OPTION_MASK) != 0;
}

static inline bool context_breaksym_enabled(context_t *ctx) {
  return (ctx->options & BREAKSYM_OPTION_MASK) != 0;
}

static inline bool context_pseudo_inverse_enabled(context_t *ctx) {
  return (ctx->options & PSEUDO_INVERSE_OPTION_MASK) != 0;
}

static inline bool context_ite_bounds_enabled(context_t *ctx) {
  return (ctx->options & ITE_BOUNDS_OPTION_MASK) != 0;
}

static inline bool context_cond_def_preprocessing_enabled(context_t *ctx) {
  return (ctx->options & CONDITIONAL_DEF_OPTION_MASK) != 0;
}

static inline bool context_has_preprocess_options(context_t *ctx) {
  return (ctx->options & PREPROCESSING_OPTIONS_MASK) != 0;
}

static inline bool context_dump_enabled(context_t *ctx) {
  return (ctx->options & DUMP_OPTION_MASK) != 0;
}

static inline bool splx_eager_lemmas_enabled(context_t *ctx) {
  return (ctx->options & SPLX_EGRLMAS_OPTION_MASK) != 0;
}

static inline bool splx_periodic_icheck_enabled(context_t *ctx) {
  return (ctx->options & SPLX_ICHECK_OPTION_MASK) != 0;
}

static inline bool splx_eqprop_enabled(context_t *ctx) {
  return (ctx->options & SPLX_EQPROP_OPTION_MASK) != 0;
}


/*
 * Provisional: set/clear/test dump mode
 */
static inline void enable_dump(context_t *ctx) {
  ctx->options |= DUMP_OPTION_MASK;
}

static inline void disable_dump(context_t *ctx) {
  ctx->options &= ~DUMP_OPTION_MASK;
}

// Lax mode
static inline void enable_lax_mode(context_t *ctx) {
  ctx->options |= LAX_OPTION_MASK;
}

static inline void disable_lax_mode(context_t *ctx) {
  ctx->options &= ~LAX_OPTION_MASK;
}

static inline bool context_in_strict_mode(context_t *ctx) {
  return (ctx->options & LAX_OPTION_MASK) == 0;
}


/********************************
 *  CHECK THEORIES AND SOLVERS  *
 *******************************/

/*
 * Supported theories
 */
static inline bool context_allows_uf(context_t *ctx) {
  return (ctx->theories & UF_MASK) != 0;
}

static inline bool context_allows_bv(context_t *ctx) {
  return (ctx->theories & BV_MASK) != 0;
}

static inline bool context_allows_idl(context_t *ctx) {
  return (ctx->theories & IDL_MASK) != 0;
}

static inline bool context_allows_rdl(context_t *ctx) {
  return (ctx->theories & RDL_MASK) != 0;
}

static inline bool context_allows_lia(context_t *ctx) {
  return (ctx->theories & LIA_MASK) != 0;
}

static inline bool context_allows_lra(context_t *ctx) {
  return (ctx->theories & LRA_MASK) != 0;
}

static inline bool context_allows_lira(context_t *ctx) {
  return (ctx->theories & LIRA_MASK) != 0;
}

static inline bool context_allows_nlarith(context_t *ctx) {
  return (ctx->theories & NLIRA_MASK) != 0;
}

static inline bool context_allows_fun_updates(context_t *ctx) {
  return (ctx->theories & FUN_UPDT_MASK) != 0;
}

static inline bool context_allows_extensionality(context_t *ctx) {
  return (ctx->theories & FUN_EXT_MASK) != 0;
}

static inline bool context_allows_quantifiers(context_t *ctx) {
  return (ctx->theories & QUANT_MASK) != 0;
}


/*
 * Check which solvers are present
 */
static inline bool context_has_egraph(context_t *ctx) {
  return ctx->egraph != NULL;
}

static inline bool context_has_arith_solver(context_t *ctx) {
  return ctx->arith_solver != NULL;
}

static inline bool context_has_bv_solver(context_t *ctx) {
  return ctx->bv_solver != NULL;
}

static inline bool context_has_fun_solver(context_t *ctx) {
  return ctx->fun_solver != NULL;
}


/*
 * Check which variant of the arithmetic solver is present
 */
extern bool context_has_idl_solver(context_t *ctx);
extern bool context_has_rdl_solver(context_t *ctx);
extern bool context_has_simplex_solver(context_t *ctx);



/*
 * Get the difference-logic profile record (only useful for contexts
 * with architecture CTX_ARCH_AUTO_IDL or CTX_ARCH_AUTO_RDL).
 */
static inline dl_data_t *get_diff_logic_profile(context_t *ctx) {
  return ctx->dl_profile;
}


/*
 * Optional features
 */
static inline bool context_supports_multichecks(context_t *ctx) {
  return (ctx->options & MULTICHECKS_OPTION_MASK) != 0;
}

static inline bool context_supports_pushpop(context_t *ctx) {
  return (ctx->options & PUSHPOP_OPTION_MASK) != 0;
}

static inline bool context_supports_cleaninterrupt(context_t *ctx) {
  return (ctx->options & CLEANINT_OPTION_MASK) != 0;
}


/*
 * Read the mode flag
 */
static inline context_mode_t context_get_mode(context_t *ctx) {
  return ctx->mode;
}



/***************
 *  UTILITIES  *
 **************/

/*
 * Read the status: returns one of
 *  STATUS_IDLE        (before check_context)
 *  STATUS_SEARCHING   (during check_context)
 *  STATUS_UNKNOWN
 *  STATUS_SAT
 *  STATUS_UNSAT
 *  STATUS_INTERRUPTED
 */
static inline smt_status_t context_status(context_t *ctx) {
  return smt_status(ctx->core);
}


/*
 * Read the base_level (= number of calls to push)
 */
static inline uint32_t context_base_level(context_t *ctx) {
  return ctx->base_level;
}


/*
 * Value of a Boolean term in ctx
 * - t must be a Boolean term
 *
 * The result can be
 * - VAL_TRUE  if t is true
 * - VAL_FALSE if t is false
 * - VAL_UNDEF_FALSE or VAL_UNDEF_TRUE otherwise (value is not known)
 */
extern bval_t context_bool_term_value(context_t *ctx, term_t t);


/*
 * GARBAGE-COLLECTION SUPPORT
 */

/*
 * Mark all terms present in ctx (to make sure they survive the
 * next call to term_table_gc).
 */
extern void context_gc_mark(context_t *ctx);


#endif /* __CONTEXT_H */
