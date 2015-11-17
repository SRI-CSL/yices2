/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
#include "context/common_conjuncts.h"
#include "context/internalization_table.h"
#include "context/pseudo_subst.h"
#include "context/shared_terms.h"
#include "io/tracer.h"
#include "solvers/cdcl/gates_manager.h"
#include "solvers/cdcl/smt_core.h"
#include "solvers/egraph/egraph_base_types.h"
#include "terms/conditionals.h"
#include "terms/terms.h"
#include "utils/int_bv_sets.h"
#include "utils/int_hash_sets.h"
#include "utils/int_queues.h"
#include "utils/int_stack.h"
#include "utils/int_vectors.h"
#include "utils/mark_vectors.h"
#include "utils/pair_hash_map2.h"


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
 * - FLATTEN_ITE: avoid intermediate variables when converting nested
 *   if-then-else terms
 * - FACTOR_TOP_OR: extract common factors from top-level disjuncts
 *
 * BREAKSYM for QF_UF is based on the paper by Deharbe et al (CADE 2011)
 *
 * PSEUDO_INVERSE is based on Brummayer's thesis (Boolector stuff)
 * - not implemented yet
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

typedef void    (*attach_eterm_fun_t)(void *solver, thvar_t v, eterm_t t);
typedef eterm_t (*eterm_of_var_fun_t)(void *solver, thvar_t v);
typedef void (*build_model_fun_t)(void *solver);
typedef void (*free_model_fun_t)(void *solver);

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
  void *bv_solver;

  // solver internalization interfaces
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

  // data about shared subterms
  sharing_map_t sharing;

  // store for the conditional descriptors
  object_store_t cstore;

  // optional components: allocated if needed
  pseudo_subst_t *subst;
  mark_vector_t *marks;
  int_bvset_t *cache;
  int_hset_t *small_cache;
  pmap2_t *eq_cache;
  bfs_explorer_t *explorer;

  // auxiliary buffers for model construction
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
  TOO_MANY_ARITH_VARS = -17,
  TOO_MANY_ARITH_ATOMS = -18,
  ARITHSOLVER_EXCEPTION = -19,
  // bv solver errors
  BVSOLVER_EXCEPTION = -20,
};


/*
 * NUM_INTERNALIZATION_ERRORS: must be (1 + number of negative codes)
 */
#define NUM_INTERNALIZATION_ERRORS 21



#endif /* __CONTEXT_TYPES_H */
