/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STAND-ALONE SAT SOLVER
 */

#ifndef __SAT_SOLVER_H
#define __SAT_SOLVER_H


#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "utils/bitvectors.h"
#include "utils/int_vectors.h"
#include "utils/tag_map.h"
#include "utils/stable_sort.h"


/************************************
 *  BOOLEAN VARIABLES AND LITERALS  *
 ***********************************/

/*
 * Boolean variables: integers between 0 and nvars - 1
 * Literals: integers between 0 and 2nvar - 1.
 *
 * For a variable x, the positive literal is 2x, the negative
 * literal is 2x + 1.
 *
 * -1 is a special marker for both variables and literals
 */
typedef int32_t bvar_t;
typedef int32_t literal_t;

enum {
  null_bvar = -1,
  null_literal = -1,
};


/*
 * Maximal number of boolean variables
 */
#define MAX_VARIABLES (UINT32_MAX >> 3)


/*
 * Conversions from variables to literals
 */
static inline literal_t pos_lit(bvar_t x) {
  return (x << 1);
}

static inline literal_t neg_lit(bvar_t x) {
  return (x << 1) + 1;
}

static inline bvar_t var_of(literal_t l) {
  return l>>1;
}

// sign: 0 --> positive, 1 --> negative
static inline int32_t sign_of(literal_t l) {
  return l & 1;
}

// negation of literal l
static inline literal_t not(literal_t l) {
  return l ^ 1;
}

// check whether l1 and l2 are opposite
static inline bool opposite(literal_t l1, literal_t l2) {
  return (l1 ^ l2) == 1;
}

// true if l has positive polarity (i.e., l = pos_lit(x))
static inline bool is_pos(literal_t l) {
  return !(l & 1);
}

static inline bool is_neg(literal_t l) {
  return (l & 1);
}


/*
 * Assignment values for a variable:
 * - we use four values to encode the truth value of x
 *   when x is assigned and the preferred value when x is
 *   not assigned.
 * - value[x] is interpreted as follows
 *   val_undef_false = 0b00 --> x not assigned, preferred value = false
 *   val_undef_true  = 0b01 --> x not assigned, preferred value = true
 *   val_false = 0b10       --> x assigned false
 *   val_true =  0b11       --> x assigned true
 *
 * The preferred value is used when x is selected as a decision variable.
 * Then we assign x to true or false depending on the preferred value.
 * This is done by setting bit 1 in value[x].
 */
typedef enum bval {
  val_undef_false = 0,
  val_undef_true = 1,
  val_false = 2,
  val_true = 3,
} bval_t;


// check whether val is undef_true or undef_false
static inline bool is_unassigned_val(bval_t val) {
  return (val & 0x2) == 0;
}

// check whether val is val_undef_true of val_true
static inline bool true_preferred(bval_t val) {
  return (val & 0x1) != 0;
}


/*
 * Problem status
 */
typedef enum solver_status {
  status_unsolved,
  status_sat,
  status_unsat,
} solver_status_t;


/*
 * Codes returned by the propagation functions
 */
enum {
  no_conflict,
  binary_conflict,
  clause_conflict,
};



/***********
 * CLAUSES *
 **********/

/*
 * Clauses structure
 * - two pointers to form lists of clauses for the watched literals
 * - a clause is an array of literals terminated by an end marker
 *   (a negative number).
 * - the first two literals stored in cl[0] and cl[1]
 *   are the watched literals.
 * Learned clauses have the same components as a clause
 * and an activity, i.e., a float used by the clause-deletion
 * heuristic. (Because of alignment and padding, this wastes 32bits
 * on a 64bit machine....)
 *
 * Linked lists:
 * - a link lnk is a pointer to a clause cl
 *   the low-order bits of lnk encode whether the next link is
 *   in cl->link[0] or cl->link[1]
 * - this is compatible with the tagged pointers used as antecedents.
 *
 * SPECIAL CODING: to distinguish between learned clauses and problem
 * clauses, the end marker is different.
 * - for problem clauses, end_marker = -1
 * - for learned clauses, end_marker = -2
 *
 * A solver stores a value for these two end_markers: it must
 * always be equal to VAL_UNDEF.
 *
 * CLAUSE DELETION: to mark a clause for deletion, cl[0] and cl[1]
 * are set to the same value.
 */

enum {
  end_clause = -1,  // end of problem clause
  end_learned = -2, // end of learned clause
};

typedef struct clause_s clause_t;

typedef size_t link_t;

struct clause_s {
  link_t link[2];
  literal_t cl[0];
};


#define INSTRUMENT_CLAUSES 0

#if INSTRUMENT_CLAUSES

/*
 * Instrumentation for learned clauses
 * - creation = number of conflicts when the clause was created
 * - deletion = number of conflicts when the clause is deleted
 * - props = number of propagations involving that clause
 * - last_prop = last time the clause caused a propagation
 * - resos = number of times the clause is used in resolution
 * - last_reso = last time the clause was involved in a resolution step
 * - base_glue = glue score at creation
 * - glue = last computed glue
 * - min_glue = minimal of all glues so far
 */
typedef struct lcstats_s {
  uint32_t creation;
  uint32_t deletion;
  uint32_t props;
  uint32_t last_prop;
  uint32_t resos;
  uint32_t last_reso;
  uint32_t base_glue;
  uint32_t glue;
  uint32_t min_glue;
} lcstat_t;


typedef struct learned_clause_s {
  lcstat_t stat;
  float activity;
  clause_t clause;
} learned_clause_t;


/*
 * Statistics array for learned clauses
 * - each element stores the stat record of a clause. It's set when
 *   the clause is deleted.
 */
typedef struct learned_clauses_stats_s {
  lcstat_t *data;
  uint32_t nrecords;
  uint32_t size;
  FILE *file;
} learned_clauses_stats_t;


#else

/*
 * No instrumentation of learned clauses
 */
typedef struct learned_clause_s {
  float activity;
  clause_t clause;
} learned_clause_t;

#endif


/*
 * Tagging/untagging of link pointers
 */
#define LINK_TAG ((size_t) 0x1)
#define NULL_LINK ((link_t) 0)

static inline link_t mk_link(clause_t *c, uint32_t i) {
  assert((i & ~LINK_TAG) == 0 && (((size_t) c) & LINK_TAG) == 0);
  return (link_t)(((size_t) c) | ((size_t) i));
}

static inline clause_t *clause_of(link_t lnk) {
  return (clause_t *)(lnk & ~LINK_TAG);
}

static inline uint32_t idx_of(link_t lnk) {
  return (uint32_t)(lnk & LINK_TAG);
}

static inline link_t next_of(link_t lnk) {
  return clause_of(lnk)->link[idx_of(lnk)];
}

/*
 * return a new link lnk0 such that
 * - clause_of(lnk0) = c
 * - idx_of(lnk0) = i
 * - next_of(lnk0) = lnk
 */
static inline link_t cons(uint32_t i, clause_t *c, link_t lnk) {
  assert(i <= 1);
  c->link[i] = lnk;
  return mk_link(c, i);
}

static inline link_t *cdr_ptr(link_t lnk) {
  return clause_of(lnk)->link + idx_of(lnk);
}






/**********
 * SOLVER *
 *********/

/*
 * INTERNAL STRUCTURES
 */

/*
 * Vectors of clauses and literals
 */
typedef struct clause_vector_s {
  uint32_t capacity;
  uint32_t size;
  clause_t *data[0];
} clause_vector_t;

typedef struct literal_vector_s {
  uint32_t capacity;
  uint32_t size;
  literal_t data[0];
} literal_vector_t;


/*
 * Default initial sizes of vectors
 */
#define DEF_CLAUSE_VECTOR_SIZE 100
#define DEF_LITERAL_VECTOR_SIZE 10
#define DEF_LITERAL_BUFFER_SIZE 100

#define MAX_LITERAL_VECTOR_SIZE (UINT32_MAX/4)


/*
 * Assignment stack/propagation queue
 * - an array of literals (the literals assigned to true)
 * - two pointers: top of the stack, beginning of the propagation queue
 * - for each decision level, an index into the stack points
 *   to the literal decided at that level (for backtracking)
 */
typedef struct {
  literal_t *lit;
  uint32_t top;
  uint32_t prop_ptr;
  uint32_t *level_index;
  uint32_t nlevels; // size of level_index array
} sol_stack_t;


/*
 * Initial size of level_index
 */
#define DEFAULT_NLEVELS 100


/*
 * Heap and variable activities for variable selection heuristic
 * - activity[x]: for every variable x between 0 and nvars - 1
 *   activity[-1] = DBL_MAX (higher than any activity)
 *   activity[-2] = -1.0 (lower than any variable activity)
 * - heap_index[x]: for every variable x,
 *      heap_index[x] = i if x is in the heap and heap[i] = x
 *   or heap_index[x] = -1 if x is not in the heap
 * - heap: array of nvars + 1 variables
 * - heap_last: index of last element in the heap
 *   heap[0] = -1,
 *   for i=1 to heap_last, heap[i] = x for some variable x
 * - size = number of variable (nvars)
 * - vmax = variable index (last variable not in the heap)
 * - act_inc: variable activity increment
 * - inv_act_decay: inverse of variable activity decay (e.g., 1/0.95)
 *
 * The set of variables is split into two segments:
 * - [0 ... vmax-1] = variables that are in the heap or have been in the heap
 * - [vmax ... size-1] = variables that may not have been in the heap
 *
 * To pick a decision variable:
 * - search for the most active unassigned variable in the heap
 * - if the heap is empty or all its variables are already assigned,
 *   search for the first unassigned variables in [vmax ... size-1]
 *
 * Initially: we set vmax to 0 (nothing in the heap yet) so decision
 * variables are picked in increasing order, starting from 0.
 */
typedef struct var_heap_s {
  double *activity;
  int32_t *heap_index;
  bvar_t *heap;
  uint32_t heap_last;
  uint32_t size;
  uint32_t vmax;
  double act_increment;
  double inv_act_decay;
} var_heap_t;



/*
 * Antecedent = either a clause or a literal or a generic explanation
 * represented as tagged pointers. tag = two low-order bits
 * - tag = 00: clause with implied literal as cl[0]
 * - tag = 01: clause with implied literal as cl[1]
 * - tag = 10: literal
 * - tag = 11: generic explanation
 *
 * NOTE: generic explanation is not used for Boolean problems
 */
typedef size_t antecedent_t;

enum {
  clause0_tag = 0,
  clause1_tag = 1,
  literal_tag = 2,
  generic_tag = 3,
};

static inline uint32_t antecedent_tag(antecedent_t a) {
  return a & 0x3;
}

static inline literal_t literal_antecedent(antecedent_t a) {
  return (literal_t) (a>>2);
}

static inline clause_t *clause_antecedent(antecedent_t a) {
  return (clause_t *) (a & ~((size_t) 0x3));
}

// clause index: 0 or 1, low order bit of a
static inline uint32_t clause_index(antecedent_t a) {
  return (uint32_t) (a & 0x1);
}

static inline void *generic_antecedent(antecedent_t a) {
  return (void *) (a & ~((size_t) 0x3));
}

static inline antecedent_t mk_literal_antecedent(literal_t l) {
  return (((size_t) l) << 2) | literal_tag;
}

static inline antecedent_t mk_clause0_antecedent(clause_t *cl) {
  assert((((size_t) cl) & 0x3) == 0);
  return ((size_t) cl) | clause0_tag;
}

static inline antecedent_t mk_clause1_antecedent(clause_t *cl) {
  assert((((size_t) cl) & 0x3) == 0);
  return ((size_t) cl) | clause1_tag;
}

static inline antecedent_t mk_clause_antecedent(clause_t *cl, int32_t index) {
  assert((((size_t) cl) & 0x3) == 0);
  return ((size_t) cl) | (index & 1);
}

static inline antecedent_t mk_generic_antecedent(void *g) {
  assert((((size_t) g) & 0x3) == 0);
  return ((size_t) g) | generic_tag;
}



/*
 * STATISTICS
 */
typedef struct solver_stats_s {
  uint32_t starts;           // 1 + number of restarts
  uint32_t simplify_calls;   // number of calls to simplify_clause_database
  uint32_t reduce_calls;     // number of calls to reduce_learned_clause_set

  uint64_t decisions;        // number of decisions
  uint64_t random_decisions; // number of random decisions
  uint64_t propagations;     // number of boolean propagations
  uint64_t conflicts;        // number of conflicts/backtracking

  uint64_t prob_literals;     // number of literals in problem clauses
  uint64_t learned_literals;  // number of literals in learned clauses
  uint64_t aux_literals;      // temporary counter for simplify_clause

  uint64_t prob_clauses_deleted;     // number of problem clauses deleted
  uint64_t learned_clauses_deleted;  // number of learned clauses deleted
  uint64_t bin_clauses_deleted;      // number of binary clauses deleted

  uint64_t literals_before_simpl;
  uint64_t subsumed_literals;
} solver_stats_t;


/*
 * Solver state
 * - global flags and counters
 * - clause data base divided into:
 *    - vector of problem clauses
 *    - vector of learned clauses
 *   unit and binary clauses are stored implicitly.
 * - propagation structures: for every literal l
 *   bin[l] = literal vector for binary clauses
 *   watch[l] = list of clauses where l is a watched literal
 *     (i.e., clauses where l occurs in position 0 or 1)
 *
 * - for every variable x between 0 and nb_vars - 1
 *   - antecedent[x]: antecedent type and value
 *   - level[x]: decision level (only meaningful if x is assigned)
 *   - mark[x]: 1 bit used in UIP computation
 *
 * - for every literal l between 0 and nb_lits - 1
 *   - value[l] = current assignment
 *   - value[-2] = value[-1] = val_undef_false
 * - a heap for the decision heuristic
 *
 * - an assignment stack
 *
 * - other arrays for constructing and simplifying learned clauses
 */
typedef struct sat_solver_s {
  uint32_t status;            // UNSOLVED, SAT, OR UNSAT

  uint32_t nb_vars;           // Number of variables
  uint32_t nb_lits;           // Number of literals = twice the number of variables
  uint32_t vsize;             // Size of the variable arrays (>= nb_vars)
  uint32_t lsize;             // size of the literal arrays (>= nb_lits)

  uint32_t nb_clauses;        // Number of clauses with at least 3 literals
  uint32_t nb_unit_clauses;   // Number of unit clauses
  uint32_t nb_bin_clauses;    // Number of binary clauses

  /* Activity increments and decays for learned clauses */
  float cla_inc;              // Clause activity increment
  float inv_cla_decay;        // Inverse of clause decay (e.g., 1/0.999)

  /* Current decision level */
  uint32_t decision_level;
  uint32_t backtrack_level;

  /* Simplify DB heuristic  */
  uint32_t simplify_bottom;     // stack top pointer after last simplify_clause_database
  uint64_t simplify_props;      // value of propagation counter at that point
  uint64_t simplify_threshold;  // number of propagations before simplify is enabled again

  /* Reduce DB heuristic */
  uint32_t reduce_threshold;    // number of learned clauses before reduce is called

  /* Statistics */
  solver_stats_t stats;

  /* Clause database */
  clause_t **problem_clauses;
  clause_t **learned_clauses;

  /* Variable-indexed arrays */
  antecedent_t *antecedent;
  uint32_t *level;
  byte_t *mark;                 // bitvector

  /* Literal-indexed arrays */
  uint8_t *value;
  literal_t **bin;             // array of literal vectors
  link_t *watch;               // array of watch lists

  /* Heap */
  var_heap_t heap;

  /* Stack */
  sol_stack_t stack;

  /* Auxiliary vectors for conflict analysis */
  ivector_t buffer;
  ivector_t buffer2;

  /* Conflict clauses stored in short_buffer or via conflict pointer */
  literal_t short_buffer[4];
  literal_t *conflict;
  clause_t *false_clause;

  /* Sorter: used in deletion of learned clauses */
  stable_sorter_t sorter;
} sat_solver_t;




/*
 * Access to truth assignment
 */
static inline bval_t lit_val(sat_solver_t *solver, literal_t l) {
  assert(-2 <= l && l < (int32_t) solver->nb_lits);
  return solver->value[l];
}

static inline bool lit_is_unassigned(sat_solver_t *solver, literal_t l) {
  return is_unassigned_val(lit_val(solver, l));
}

static inline bool lit_is_assigned(sat_solver_t *solver, literal_t l) {
  return ! lit_is_unassigned(solver, l);
}

static inline bool var_is_assigned(sat_solver_t *solver, bvar_t x) {
  return lit_is_assigned(solver, pos_lit(x));
}

static inline bool var_is_unassigned(sat_solver_t *solver, bvar_t x) {
  return !var_is_assigned(solver, x);
}


static inline bool lit_prefers_true(sat_solver_t *solver, literal_t l) {
  return true_preferred(lit_val(solver, l));
}


/********************
 *  MAIN FUNCTIONS  *
 *******************/

/*
 * Solver initialization
 * - size = initial size of the variable arrays
 */
extern void init_sat_solver(sat_solver_t *solver, uint32_t size);

/*
 * Set the prng seed
 */
extern void sat_solver_set_seed(sat_solver_t *solver, uint32_t seed);


/*
 * Delete solver
 */
extern void delete_sat_solver(sat_solver_t *solver);

/*
 * Add n fresh variables
 */
extern void sat_solver_add_vars(sat_solver_t *solver, uint32_t n);

/*
 * Allocate a fresh boolean variable and return its index
 */
extern bvar_t sat_solver_new_var(sat_solver_t *solver);

/*
 * Addition of simplified clause
 * - each clause is an array of literals (integers between 0 and 2nvars - 1)
 *   that does not contain twice the same literals or complementary literals
 */
extern void sat_solver_add_empty_clause(sat_solver_t *solver);
extern void sat_solver_add_unit_clause(sat_solver_t *solver, literal_t l);
extern void sat_solver_add_binary_clause(sat_solver_t *solver, literal_t l0, literal_t l1);
extern void sat_solver_add_ternary_clause(sat_solver_t *solver, literal_t l0, literal_t l1,
                                          literal_t l2);

// clause l[0] ... l[n-1]
extern void sat_solver_add_clause(sat_solver_t *solver, uint32_t n, literal_t *l);


/*
 * Simplify then add a clause: remove duplicate literals, and already
 * assigned literals, and simplify
 */
extern void sat_solver_simplify_and_add_clause(sat_solver_t *solver, uint32_t n, literal_t *l);



/*
 * Bounded search: search until either unsat or sat is determined, or until
 * the number of conflicts generated reaches conflict_bound.
 * Return status_unsat, status_sat if the problem is solved.
 * Return status_unknown if the conflict bound is reached.
 *
 * The return value is also kept as solver->status.
 */
extern solver_status_t search(sat_solver_t *solver, uint32_t conflict_bound);


/*
 * Solve the problem: repeatedly calls search until it returns sat or unsat.
 * - initial conflict_bound = 100.
 * - initial del_threshold = number of clauses / 3.
 * - at every iteration, conflict_bound is increased by 50% and del_threshold by 10%
 * - if verbose is true, print statistics on stderr during the search
 */
extern solver_status_t solve(sat_solver_t *solver, bool verbose);


/*
 * Access to solver fields
 */
static inline solver_status_t solver_status(sat_solver_t *solver) {
  return solver->status;
}

static inline uint32_t solver_nvars(sat_solver_t *solver) {
  return solver->nb_vars;
}

static inline uint32_t solver_nliterals(sat_solver_t *solver) {
  return solver->nb_lits;
}

static inline solver_stats_t * solver_statistics(sat_solver_t *solver) {
  return &solver->stats;
}


/*
 * Read variable/literal assignments
 */
static inline bval_t get_literal_assignment(sat_solver_t *solver, literal_t l) {
  assert(0 <= l && l < solver->nb_lits);
  return lit_val(solver, l);
}

static inline bval_t get_variable_assignment(sat_solver_t *solver, bvar_t x) {
  assert(0 <= x && x < solver->nb_vars);
  return lit_val(solver, pos_lit(x));
}

/*
 * Copy the full variable assignment in array val.
 * - val must have size >= solver->nb_vars
 */
extern void get_allvars_assignment(sat_solver_t *solver, bval_t *val);


/*
 * Copy all the literals assigned to true in array a
 * - return the number of literals copied.
 * - a must be have size >= solver->nb_vars
 */
extern uint32_t get_true_literals(sat_solver_t *solver, literal_t *a);


#if INSTRUMENT_CLAUSES

/*
 * Statistics records:
 * - allocate the statistics data structure
 * - f must be open and writeable. It will be use to
 *   store the statistics data.
 */
extern void init_learned_clauses_stats(FILE *f);


/*
 * Save all statistics into the statistics file
 */
extern void flush_learned_clauses_stats(void);

#endif


#endif /* __SAT_SOLVER_H */
