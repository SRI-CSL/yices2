/*
 * CONTEXT
 *
 * Updated to work with the new term representation.
 *
 * Basic context: enough support for simplification
 * and flattening of assertion.
 */

#ifndef __CONTEXT_H
#define __CONTEXT_H

#include <stdint.h>
#include <stdbool.h>
#include <setjmp.h>

#include "yices_types.h"

#include "int_queues.h"
#include "int_stack.h"
#include "int_vectors.h"
#include "terms.h"
#include "internalization_table.h"
#include "internalization_codes.h"
#include "pseudo_subst.h"
#include "mark_vectors.h"

#include "gates_manager.h"
#include "smt_core.h"
#include "egraph.h"
#include "models.h"



/***********************
 *  OPTIONAL FEATURES  *
 **********************/

/*
 * Bit mask for specifying which features are supported
 */
#define MULTICHECKS_OPTION_MASK 0x1
#define PUSHPOP_OPTION_MASK     0x2
#define CLEANINT_OPTION_MASK    0x4


/*
 * Possible modes
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
 *
 * Options passed to the simplex solver when it's created
 * - EAGER_LEMMAS
 * - ENABLE_ICHECK
 */
#define VARELIM_OPTION_MASK      0x10
#define FLATTENOR_OPTION_MASK    0x20
#define FLATTENDISEQ_OPTION_MASK 0x40
#define EQABSTRACT_OPTION_MASK   0x80
#define ARITHELIM_OPTION_MASK    0x100
#define KEEP_ITE_OPTION_MASK     0x200
#define BVARITHELIM_OPTION_MASK  0x400

#define PREPROCESSING_OPTIONS_MASK \
 (VARELIM_OPTION_MASK|FLATTENOR_OPTION_MASK|FLATTENDISEQ_OPTION_MASK|\
  EQABSTRACT_OPTION_MASK|ARITHELIM_OPTION_MASK|KEEP_ITE_OPTION_MASK|BVARITHELIM_OPTION_MASK)

#define SPLX_EGRLMAS_OPTION_MASK  0x10000
#define SPLX_ICHECK_OPTION_MASK   0x20000

// FOR TESTING
#define DUMP_OPTION_MASK        0x80000000



/***************************************
 *  ARCHITECTURES/SOLVER COMBINATIONS  *
 **************************************/

/*
 * An architecture is specified by one of the following codes
 * - each architecture defines a set of solvers (and the supported theories)
 * - the special "auto" codes can be used if mode is CTX_MODE_ONECHECK
 *
 * Note: these are anticipated/planned architectures. Most don't exist yet.
 * Some may be removed and other added.
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
  CTX_ARCH_EGFUNSPLXBV,  // all solvers (should be the default)

  CTX_ARCH_AUTO_IDL,     // either simplex or integer floyd-warshall
  CTX_ARCH_AUTO_RDL,     // either simplex or real floyd-warshall
} context_arch_t;


#define NUM_ARCH (CTX_ARCH_AUTO_RDL+1)


/*
 * Supported theories (including arithmetic and function theory variants)
 * - a 32bit theories word indicate what's supported
 * - each bit selects a theory
 * The theory words is derived from the architecture descriptor
 */
#define UF_MASK        0x1
#define BV_MASK        0x2
#define IDL_MASK       0x4
#define RDL_MASK       0x8
#define LIA_MASK       0x10
#define LRA_MASK       0x20
#define LIRA_MASK      0x40
#define NLIRA_MASK     0x80     // non-linear arithmeatic
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


/*
 * Marks for cycle detection:
 * - white: term not visited
 * - grey: term found but not fully explored yet
 * - black: fully explored term
 */
enum {
  WHITE = 0,
  GREY = 1,
  BLACK = 2,
};


/**************
 *  CONTEXT   *
 *************/

/*
 * Context: minimal for now
 */
struct context_s {
    // mode + architecture
  context_mode_t mode;
  context_arch_t arch;

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

  // input are all from the following tables (from yices_globals.h)
  type_table_t *types; 
  term_table_t *terms;

  // hash table for Boolean gates
  gate_manager_t gate_manager;

  // internalization + assertion queue
  intern_tbl_t intern;
  ivector_t assertions;

  // result of flattening and simplification
  ivector_t top_eqs;
  ivector_t top_atoms;
  ivector_t top_formulas;
  ivector_t top_interns;
  
  // auxiliary buffers and structures for internalization
  ivector_t subst_eqs;
  int_stack_t istack;
  int_queue_t queue;
  pseudo_subst_t *subst;
  mark_vector_t *marks;

  // for exception handling
  jmp_buf env;
};



/*
 * Default initial size of auxiliary buffers and vectors
 */
#define CTX_DEFAULT_AUX_SIZE 20
#define CTX_MAX_AUX_SIZE (UINT32_MAX/4)
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
  INTERNAL_ERROR = -1,
  TYPE_ERROR = -2,
  FREE_VARIABLE_IN_FORMULA = -3,
  LOGIC_NOT_SUPPORTED = -4,
  UF_NOT_SUPPORTED = -5,
  ARITH_NOT_SUPPORTED = -6,
  BV_NOT_SUPPORTED = -7,
  FUN_NOT_SUPPORTED = -8,
  QUANTIFIERS_NOT_SUPPORTED = -9,
  FORMULA_NOT_IDL = -10,
  FORMULA_NOT_RDL = -11,
  NONLINEAR_NOT_SUPPORTED = -12,
  ARITHSOLVER_EXCEPTION = -13,
  BVSOLVER_EXCEPTION = -14,
};

#define NUM_INTERNALIZATION_ERRORS 15




/*********************************
 *  SEARCH PARAMETERS AND FLAGS  *
 ********************************/

/*
 * Possible branching heuristics:
 * - determine whether to assign the decision literal to true or false
 */
typedef enum {
  BRANCHING_DEFAULT,  // use internal smt_core cache
  BRANCHING_NEGATIVE, // branch l := false
  BRANCHING_POSITIVE, // branch l := true
  BRANCHING_THEORY,   // defer to the theory solver
  BRANCHING_TH_NEG,   // defer to theory solver for atoms, branch l := false otherwise
  BRANCHING_TH_POS,   // defer to theory solver for atoms, branch l := true otherwise
  BRANCHING_BV,       // experimental: default for atoms, random otherwise
} branch_t;



typedef struct param_s {
  /*
   * Restart heuristic: similar to PICOSAT or MINISAT
   *
   * If fast_restart is true: PICOSAT-style heuristic
   * - inner restarts based on c_threshold
   * - outer restarts based on d_threshold
   *
   * If fast_restart is false: MINISAT-style restarts
   * - c_threshold and c_factor are used
   * - d_threshold and d_threshold are ignored
   * - to get periodic restart set c_factor = 1.0
   */
  bool     fast_restart;
  uint32_t c_threshold;     // initial value of c_threshold
  uint32_t d_threshold;     // initial value of d_threshold
  double   c_factor;        // increase factor for next c_threshold
  double   d_factor;        // increase factor for next d_threshold

  /*
   * Clause-deletion heuristic
   * - initial reduce_threshold is max(r_threshold, num_prob_clauses * r_fraction)
   * - increase by r_factor on every outer restart provided reduce was called in that loop
   */
  uint32_t r_threshold;
  double   r_fraction;
  double   r_factor;

  /*
   * SMT Core parameters:
   * - randomness and var_decay are used by the branching heuristic
   *   the default branching mode uses the cached polarity in smt_core.
   * - clause_decay influence clause deletion
   * 
   * SMT Core caching of theory lemmas:
   * - if cache_tclauses is true, then the core internally turns 
   *   some theory lemmas into learned clauses
   * - for the core, a theory lemma is either a conflict reported by
   *   the theory solver or a theory implication
   * - a theory implication is considered for caching if it's involved
   *   in a conflict resolution
   * - parmeter tclause_size controls the lemma size: only theory lemmas 
   *   of size <= tclause_size are turned into learned clauses
   */
  double   var_decay;       // decay factor for variable activity
  float    randomness;      // probability of a random pick in select_unassigned_literal
  branch_t branching;       // branching heuristic
  float    clause_decay;    // decay factor for learned-clause activity
  bool     cache_tclauses;
  uint32_t tclause_size;

  /*
   * EGRAPH PARAMETERS
   *
   * Control of the Ackermann lemmas
   * - use_dyn_ack: if true, the dynamic ackermann heuristic is enabled for 
   *   non-boolean terms
   * - use_bool_dyn_ack: if true, the dynamic ackermann heuristic is enabled
   *   for boolean terms
   *
   * Limits to stop the Ackermann trick if too many lemmas are generated
   * - max_ackermann: limit for the non-boolean version
   * - max_boolackermann: limit for the boolem version
   *
   * The Ackermann clauses may require the construction of new equality
   * terms that were not present in the context. This is controlled by
   * the egraph's quota on auxiliary equalities. The quota is initialized
   * to max(aux_eq_ratio * n, aux_eq_quota) where n is the total
   * number of terms in the initial egraph.
   *
   * Control of interface equality generation: set a limit on
   * the number of interface equalities created per round.
   */
  bool     use_dyn_ack;
  bool     use_bool_dyn_ack;
  uint32_t max_ackermann;
  uint32_t max_boolackermann;
  uint32_t aux_eq_quota;
  double   aux_eq_ratio;
  uint32_t max_interface_eqs;


  /*
   * SIMPLEX PARAMETERS
   * - simplex_prop: if true enable propagation via propagation table
   * - max_prop_row_size: limit on the size of the propagation rows
   * - bland_threshold: threshold that triggers switching to Bland's rule
   * - integer_check_period: how often the integer solver is called
   */
  bool     use_simplex_prop;
  uint32_t max_prop_row_size;
  uint32_t bland_threshold;
  int32_t  integer_check_period;


  /*
   * ARRAY SOLVER PARAMETERS
   * - max_update_conflicts: limit on the number of update axioms generated
   *   per call to final_check
   * - max_extensionality: limit on the number of extensionality axioms 
   *   generated per call to reconcile_model
   */
  uint32_t max_update_conflicts;
  uint32_t max_extensionality;

} param_t;







/********************************
 *  INITIALIZATION AND CONTROL  *
 *******************************/

/*
 * Initialize ctx for the given mode and architecture
 * - terms = term table for this context
 * - qflag = false means quantifier-free variant
 * - qflag = true means quantifiers allowed
 * If arch is one of the ARCH_AUTO_... variants, then mode must be ONECHECK
 */
extern void init_context(context_t *ctx, term_table_t *terms, 
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
 * Push and pop
 * - should not be used if the push_pop option is disabled
 */
extern void context_push(context_t *ctx);
extern void context_pop(context_t *ctx);




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
extern int32_t assert_formulas(context_t *ctx, uint32_t n, term_t *f);







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


/*
 * Simplex-related options
 */
extern void enable_splx_eager_lemmas(context_t *ctx);
extern void disable_splx_eager_lemmas(context_t *ctx);
extern void enable_splx_periodic_icheck(context_t *ctx);
extern void disable_splx_periodic_icheck(context_t *ctx);


/*
 * Chek which options are enabled
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


/*
 * Provisional: set/clear/test dump mode
 */
static inline void enable_dump(context_t *ctx) {
  ctx->options |= DUMP_OPTION_MASK;
}

static inline void disable_dump(context_t *ctx) {
  ctx->options &= ~DUMP_OPTION_MASK;
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



#endif /* __CONTEXT_H */
