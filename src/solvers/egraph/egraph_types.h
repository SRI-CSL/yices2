/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * E-GRAPH DATA STRUCTURES
 *
 * Initial egraph module started in August 2007.
 * Functional version completed by October 2007 and integrated to
 * QF_UF prototype solver (yices_smt)
 *
 * 2008-02-08: started main revision
 * - need to adapt the egraph data structures to interface with the smt_core module
 * - need to provide better API for communication with sub_solvers (other theories)
 * - added support for egraph atoms here (rather than in an external solver module)
 * - removed lazy clause support (for now) to simplify the implementation
 * - removed support for disequality propagation (did not seem to provide any performance
 *   improvement on our benchmarks)
 * - revert to implementing the dynamic ackermann trick as in Yices 1 (i.e., by
 *   creating lemmas in the smt_core)
 *
 * 2008-12-30: modified term creation interface
 *
 * 2009-01-22: cleaned up interface with subsolvers
 *
 * 2012-09-06: added lambda terms
 *
 * 2013-11-11: changed model construction to use fresh_val_maker.
 */


/*
 * Terms
 * -----
 * Terms are represented by 32 bit signed integers (eterm_t) between 0
 * and nterms - 1. Negative indices are used as special markers.
 *
 * For each term t,
 * - body[t] is either a composite or a special marker.
 *
 * Atomic terms are constants or variables
 * - if t is a constant, body[t] = mk_constant(id) where id is a constant index.
 *   id is used during model construction.
 * - if t is a variable, body[t] = VARIABLE_BODY
 * The difference is that all constants are assumed distinct, whereas
 * variables are not. Term 0 is the boolean constant (true).
 *
 * Non-atomic terms are of one of the following forms:
 *   (apply f t_1 ... t_n)
 *   (update f t_1 ... t_n v)
 *   (tuple t_1 ... t_n)
 *   (eq t1 t2)
 *   (distinct t1 ... t_n)
 *   (ite t1 t2 t3)
 *   (or t1 .... t_n)
 *   (lambda t1 tag)
 * where f, t_i, v are occurrences of terms. These are stored as
 * composite_t objects.
 *
 * Lambda terms are of the form (lambda t1 tag) where tag is an integer index
 * that identifies the term domain. There's an associate lambda descriptor
 * table and lambda_desc[tag] stores:
 *    n = arity of the term
 *    dom[0] ... dom[n-1] = types
 * For example, we may have
 *    u = (lambda (x::int) (y::int) t)
 &    v = (lambda (x::real) t)
 * Then the egraph will contain
 *    u = (lambda t i)
 *    v = (lambda t j)
 * and the descriptor table will store
 *    i --> arity = 2, dom[0] = int, dom[1] = int
 *    j --> arity = 1, dom[0] = real.
 *
 *
 * To deal with boolean terms, we distinguish between positive and
 * negative occurrences of t. If t is boolean, a positive occurrence
 * denotes t, a negative occurrence denotes (not t). If t is
 * non-boolean, all its occurrences are positive. Occurrences are
 * represented by 32 bit signed integers (occ_t) and consist
 * of an eterm_t + a polarity bit. The polarity bit is the low-order bit.
 *
 * A term may have a theory variable attached: it's stored in thvar[t].
 *
 * 2009-01-23: For model construction, we also store the type of every
 * term (as an index in the generic type table = egraph->types).
 *
 *
 * Equivalence classes
 * -------------------
 * - an equivalence class is a set of term occurrences stored as a circular list
 * - for every term t,
 *   - label[t] = class identifier + polarity
 *     label is extended to term occurrence by setting label[t+] = label[t],
 *       and label[t-] = opposite of label[t]
 *   - next[t] = successor of t in the circular list
 * Polarities are always positive for non-boolean terms.
 * For a boolean class, there's an (implicit) complementary class that
 * contains the same terms with opposite polarities.
 *
 * Example: if  t, (not u), and (not v) are in the same class, then we would have
 *    next[t] = u-  label[t] = C+
 *    next[u] = v+  label[u] = C-
 *    next[v] = t-  label[v] = C-
 * this defines two complementary classes:
 *   C+ = { t+, u-, v- } = { t, (not u), (not v) }
 *   C- = { t-, u+, v+ } = { (not t), u, v }
 *
 * Classes are identified by an index from 0 to nclasses - 1.
 *
 * For every class c, we store
 * - parents[c] = vectors of composites that contain a term in class c
 * - root[c] = class representative = root of the explanation tree for c
 * - dmask[c] = bitmask for distinct predicates
 *   - bit 0 of dmask[c] is 1 if c contains a constant term
 *   - bit i of dmask[c] is 1 if predicate (distinct t_1 ... t_n) is asserted
 *     and t_j is in the class of c (i is an index attached to distinct ...)
 * - for boolean classes, only bit 0 matters. Distinct predicates with boolean
 *   arguments can be eliminated:
 *      (distinct t1 ... t_n) = false if n >= 3
 *      (distinct t1 t2) = (not (eq t1 t2))
 *   so if c is a class of boolean terms, then either dmask[c] == 1 if c is the
 *   class of true or dmask[c] == 0.
 *
 * The merge algorithm ensures that root[c] is fixed. When a term t is created,
 * it's initially assigned to a fresh class c_0 and root[c_0] is set to t. This
 * root term is never modified.
 * (TODO: check whether root[c] can be removed. Since roots and terms are created
 *  together, we could ensure that root term and class have the same integer index).
 *
 *
 * Atoms
 * -----
 * An egraph atom is a term t of the form (eq t1 t2) or (distinct t1 ... t_n).
 * Each such atom is mapped to a boolean variable v in the core. The mapping
 * from t to v is stored by setting thvar[t] = v. More generally, there can
 * be a core variable v attached to any boolean term t in the egraph.
 *
 * In addition, the egraph store atom objects. Each atom object is a
 * pair atm=<t, v> where t is a boolean term and v is a boolean variable
 * in the core. The core keeps the mapping from v to atm in its
 * internal atom table. If t1 ... t_n are boolean terms in the same class c
 * then their respective atoms are stored in a circular list:
 *   <t1, v1> --> ... <t_n,v_n> --> back to <t1, v1>
 * This is used to propagate implied literals to the core.
 *
 *
 * Additional data for classes
 * ---------------------------
 * For a class c, the egraph maintains:
 * - etype[c] = its type (either bool, nat, int, bitvector, tuple, array, or none)
 * - thvar[c] = an attached theory variable (or null_thvar)
 *            = a 32 bit integers, whose interpretation depends on type[c]
 *
 * The algorithms maintain the following invariant:
 * - if no term in class c has a theory variable then thvar[c] is null
 * - otherwise thvar[c] is equal to thvar[t] for some term t in c
 *
 * Initially, thvar[c] is the same as thvar[root[c]]. But thvar[c] is dynamically
 * updated as the classes are merged. If classes c2 is merged into class c1, and
 * c1 has no theory variable, then it inherits the theory variable of c2 (if any).
 * If both classes have theory variables v1 and v2, then a theory solver is notified
 * that v1 and v2 are now equal.
 *
 *
 * Special tricks: the egraph deals internally with boolean and tuple classes.
 * There is no theory solver involved for them:
 *
 * If etype[c] = ETYPE_TUPLE: then thvar[c] is a tuple-term that belongs to c.
 * - this is used to implement the propagation rule
 *    (tuple t_1 ... t_n) == (tuple u_1 ... u_n) ==> u_i == t_i
 *
 * If etype[c] = ETYPE_BOOL, thvar[c] is a boolean variable in the core
 * - for class 0 == class of true/false, we use thvar[c] = bool_const (bvar 0)
 * - for other boolean class, thvar[c] is a boolean variable v such that
 *   1) there is a term t in c  with thvar[c] = t
 *   2) there is an egraph atom of the form <t, v> in the atom table
 *
 *
 * Propagation queue
 * -----------------
 * - all assertions are written in the form t1 == t2, where t1 and t2 are term occurrences.
 * - in particular, asserting an atom <t, v> is translated to (t == true), and asserting its
 *   negation is turned into (t == false)
 * - a propagation queue stores all these assertions, and the equalities implied by congruence
 *   closure or other propagation mechanisms
 * - this is stored in a global queue: each element in the queue is a pair <t1, t2> representing
 *   the equality (t1 == t2)
 * - every pair <t1, t2> has an explanation
 *
 *
 * Explanations
 * ------------
 * - an explanation contains enough information for explaining how an equality (t1 == t2)
 *   was derived.
 * - explanations can be
 *   - axiom: empty antecedent
 *   - assertion: literal
 *   - congruence: means that t1 and t2 are equal by congruence
 *   or special codes and data encoding simplification and propagation rules
 *
 *
 * Distinct predicates
 * -------------------
 * - there can be no more than 31 terms of the form (distinct ....)
 * - when (distinct t_1 ... t_n) := true is asserted, a bit-index k is assigned and
 *   the composite (distinct ... ) is  stored in distinct[k]
 * - then bit k of dmask[class[t1] ... class[t_n]] is set to 1
 * - bit 0 is reserved and distinct[0] = NULL:
 *   bit 0 of dmask[c] is 1 iff c contains a constant term
 *
 *
 * Merge graph/explanation tree
 * ----------------------------
 * - with every class c is associated an explanation tree
 * - nodes in the tree are the terms in c
 * - the root of the tree is root[c]
 * - edges are of the form t1 ---> t2 where (t1 = t2) is an asserted or implied equality
 * - an edge of origin t1 is represented by storing edge[t1] = k where k is an index
 *   in the propagation queue (that contains <t1, t2> + an explanation)
 *
 */

#ifndef __EGRAPH_TYPES_H
#define __EGRAPH_TYPES_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "utils/arena.h"
#include "utils/object_stores.h"
#include "utils/int_vectors.h"
#include "utils/ptr_vectors.h"
#include "utils/use_vectors.h"
#include "utils/int_hash_tables.h"
#include "utils/int_hash_map.h"
#include "utils/int_stack.h"
#include "utils/cache.h"
#include "utils/ptr_partitions.h"
#include "utils/int_partitions.h"

#include "solvers/egraph/egraph_base_types.h"
#include "model/concrete_values.h"
#include "model/abstract_values.h"
#include "model/fun_maps.h"
#include "model/fresh_value_maker.h"

#include "solvers/cdcl/smt_core.h"




/*****************
 *  CLASS TABLE  *
 ****************/

/*
 * For each equivalence class c:
 * - root[c] = a term occurrence (used as class representative)
 * - dmask[c] = bitvector encoding distinct assertions
 * - parents[c] = composites that contain a term t whose class is c
 * - etype[c] = type of terms in class c
 * - thvar[c] = theory variable for class c
 */
typedef struct class_table_s {
  uint32_t size;         // size of all arrays
  uint32_t nclasses;     // number of classes

  occ_t *root;
  uint32_t *dmask;
  use_vector_t *parents;
  unsigned char *etype;
  thvar_t *thvar;
} class_table_t;


// max size: based on size of use_vector_t
#define DEFAULT_CLASS_TABLE_SIZE   200
#define MAX_CLASS_TABLE_SIZE  (UINT32_MAX>>4)

/*
 * Deletion threshold for parent vectors: When a class c is deleted,
 * its parent vector parent[c] is reset. In addition, if parent[c] has
 * size >= PARENT_DELETION_SIZE then the memory used by parent[c] is freed.
 */
#define PARENT_DELETION_SIZE 100



/****************
 *  TERM TABLE  *
 ***************/

/*
 * For each term t:
 * - body[t] = descriptor (composite or special pointers)
 * - next[t] = next element in the same class
 * - edge[t] = edge id, used for constructing explanations
 *           (or if t is not active, edge[t] = etype of t)
 * - thvar[t] = theory variable attached to t
 * - mark[t] = 1/0 bit, used for constructing explanations
 * - real_type[t] = type of t (this is necessary for constructing models)
 */
typedef struct eterm_table_s {
  uint32_t size;
  uint32_t nterms;

  composite_t **body;
  elabel_t *label;
  occ_t *next;
  int32_t *edge;
  thvar_t *thvar;
  byte_t *mark;
  type_t *real_type;
} eterm_table_t;


#define DEFAULT_ETERM_TABLE_SIZE   200
#define MAX_ETERM_TABLE_SIZE  ((uint32_t)(MAX_ETERMS))





/******************
 *  EXPLANATIONS  *
 *****************/

/*
 * Every equality (t1 == t2) in the propagation queue has an
 * antecedent that explains how (t1 == t2) was derived.
 *
 * An explanation is encoded in two parts:
 * - an 8bit tag defines its type
 * - extra data depending on the tag is stored in a union
 *
 * Explanation types:
 * - axiom:          (t1 == t2) needs no explanation
 * - assert(l):      (t1 == t2) was asserted (by setting l to true)
 * - eq(u, v):       (u == v) implies (t1 == t2)
 * - distinct0(u, v): (u != v) implies (t1 == t2)
 *      where u != v is obtained via constants (bit 0 of dmask)
 * - distinct[i](u, v): (u != v) implies (t1 == t2)
 *      where u != v is obtained via dmask (bit i of dmask)
 * - simp_or is used in two cases:
 *    (or u_1 ... u_n) == false (for all i, u_i == false)
 *    (or u_1 ... u_n) == v  (for all i, u_i == false or u_i == v)
 *
 * For equalities implied by congruence, we must be careful to
 * preserve causality: the explanation for (t1 == t2) must use only
 * equalities asserted before. To ensure causality, we use different
 * tags depending on the congruence rule applied:
 *
 * - basic_congruence: t1 and t2 are apply/update/tuple terms
 *
 * - eq_congruence1: (t1 == u1), (t2 == u2) implies (eq t1 t2) == (eq u1 u2)
 * - eq_congruence2: (t1 == u2), (t2 == u1) implies (eq t1 t2) == (eq u1 u2)
 *
 * - ite_congruence1: (t1 == u1), (t2 == u2), (t3 == u3) implies
 *                      (ite t1 t2 t3) == (ite u1 u2 u3)
 * - ite_congruence2: (t1 == (not u1)), (t2 == u3), (t3 == u2)
 *                      implies (ite t1 t2 t3) == (ite u1 u2 u3)
 *
 * - or_congruence(v) where v is an array of term occurrences
 * - distinct_congruence(v) where v is an array of term occurrences
 *
 * When (or t_1 ... t_n) == (or u_1 ... u_m) is implied by congruence,
 * we have to match each t_i to a u_j (and conversely) to produce an explanation.
 * To preserve causality, we compute the mapping t_i --> u_j at the time
 * the congruence is detected.  The mapping is stored as an array v of n + m elements
 * v_1 ... v_n, v_n+1 ... v_{n+m} and it encodes the conjunction
 * (t_1 == v1 ... t_n == v_n) and (u_1 == v_{n+1} ... u_m == v_{n+m}).
 *
 * The same thing is done when (distinct t1 ... t_n) == (distinct u_1 ... u_n) is
 * implied by congruence.
 *
 * Other explanations:
 * - Propagation via pseudo-clauses and Ackermann propagation are not used anymore.
 * - Equalities propagated from a satellite solver: the antecedent is a pointer
 *   The tag identifies the solver
 */
typedef enum expl_tag {
  EXPL_AXIOM,
  EXPL_ASSERT,
  EXPL_EQ,

  // Hackish: for EXPL_DISTINCT, we need to keep track of which bit of dmask
  // caused the propagation (i.e., the composite in egraph->dtable.distinct[i])
  // We use 32 tags since there are at most 32bits
  EXPL_DISTINCT0,
  EXPL_DISTINCT1,
  EXPL_DISTINCT2,
  EXPL_DISTINCT3,
  EXPL_DISTINCT4,
  EXPL_DISTINCT5,
  EXPL_DISTINCT6,
  EXPL_DISTINCT7,
  EXPL_DISTINCT8,
  EXPL_DISTINCT9,
  EXPL_DISTINCT10,
  EXPL_DISTINCT11,
  EXPL_DISTINCT12,
  EXPL_DISTINCT13,
  EXPL_DISTINCT14,
  EXPL_DISTINCT15,
  EXPL_DISTINCT16,
  EXPL_DISTINCT17,
  EXPL_DISTINCT18,
  EXPL_DISTINCT19,
  EXPL_DISTINCT20,
  EXPL_DISTINCT21,
  EXPL_DISTINCT22,
  EXPL_DISTINCT23,
  EXPL_DISTINCT24,
  EXPL_DISTINCT25,
  EXPL_DISTINCT26,
  EXPL_DISTINCT27,
  EXPL_DISTINCT28,
  EXPL_DISTINCT29,
  EXPL_DISTINCT30,
  EXPL_DISTINCT31,

  EXPL_SIMP_OR,

  // congruence rules
  EXPL_BASIC_CONGRUENCE,
  EXPL_EQ_CONGRUENCE1,
  EXPL_EQ_CONGRUENCE2,
  EXPL_ITE_CONGRUENCE1,
  EXPL_ITE_CONGRUENCE2,
  EXPL_OR_CONGRUENCE,
  EXPL_DISTINCT_CONGRUENCE,

  // equality propagated from a satellite theory
  // we just use a hardcoded index to identify the satellite solver for now
  EXPL_ARITH_PROPAGATION,
  EXPL_BV_PROPAGATION,
  EXPL_FUN_PROPAGATION,

  // attempt to reconcile models
  EXPL_RECONCILE,
} expl_tag_t;


typedef union expl_data_u {
  literal_t lit;      // for EXPL_ASSERT
  occ_t t[2];         // for EXPL_EQ, EXPL_DISTINCT, EXPL_DISTINCT0
  void *ptr;          // for EXPL_DISTINCT_CONGRUENCE, EXPL_OR_CONGRUENCE, theory propagation
} expl_data_t;



/*******************************
 *  DISTINCT ASSERTION TABLE   *
 ******************************/

/*
 * - npreds = number of assertions so far
 * - distinct[k] = composite (distinct ....)
 *   (the explanation is always (distinct ... ) == true).
 *
 * There's an implicit (distinct t_1 .... t_n) of index 0 where
 * t_1 ... t_n are the constant terms.
 * - index 0 is reserved (so npreds >= 1)
 * - distinct[0] = NULL
 */
#define NDISTINCTS 32
#define MAX_DISTINCT_TERMS (NDISTINCTS-1)

typedef struct distinct_table_s {
  uint32_t npreds;
  composite_t *distinct[NDISTINCTS];
} distinct_table_t;




/*********************************
 *  LAMBDA TAGS AND DESCRIPTORS  *
 ********************************/

/*
 * There are ntags descriptors.
 *
 * For each lambda tag we store:
 * - arity + domain
 */
typedef struct ltag_desc_s {
  uint32_t arity;
  type_t dom[0]; // real size = arity
} ltag_desc_t;

#define MAX_LTAG_DESC_ARITY ((UINT32_MAX-sizeof(ltag_desc_t))/sizeof(type_t))

typedef struct ltag_table_s {
  uint32_t size;
  uint32_t ntags;
  ltag_desc_t **data;
} ltag_table_t;

#define DEF_LTAG_TABLE_SIZE   8
#define MAX_LTAG_TABLE_SIZE   (UINT32_MAX/sizeof(ltag_desc_t *))



/******************
 *  UPDATE GRAPH  *
 *****************/

/*
 * To replace the fun_solver satellite.
 * The egraph has an optional 'update graph' component to
 * deal with lambda terms, updates, and extensionality.
 *
 * The data structure is defined in update_graph.h.
 */
typedef struct update_graph_s update_graph_t;


/*****************************
 *  PROPAGATION QUEUE/STACK  *
 ****************************/

/*
 * Each element i in the queue encodes an assertion
 * - eq[i] of the from (t1 == t2)
 * - with explanation defined by the pair <etag[i], edata[i]>
 *
 * When the assertion is processed, it's turned into an edge
 * t1 ---> t2 in an explanation tree (i.e., edge[t1] is set to i).
 *
 * Other components:
 * - top = top of the stack
 * - prop_ptr = index of the first equality to process
 *   so eq[prop_ptr ... top-1] = all assertions not yet processed.
 * - size = size of arrays eq, expl, saved_class
 * - mark = bitvector for constructing explanations
 *
 * Assertions are organized in levels:
 * - level_index[k] = index of the first assertion added at level k
 * - level_index[0] = 0
 * - nlevels = size of the level_index array
 */
typedef struct equeue_elem_s {
  occ_t lhs;
  occ_t rhs;
} equeue_elem_t;

typedef struct egraph_stack_s {
  equeue_elem_t *eq;
  unsigned char *etag;
  expl_data_t *edata;
  byte_t *mark;

  uint32_t top;
  uint32_t prop_ptr;
  uint32_t size;
  uint32_t *level_index;
  uint32_t nlevels;
} egraph_stack_t;


// Marker for edge[t] when t is a root
enum {
  null_edge = -1,
};


#define DEFAULT_EGRAPH_STACK_SIZE 200
#define MAX_EGRAPH_STACK_SIZE  (UINT32_MAX/8)

#define DEFAULT_EGRAPH_NLEVELS 100
#define MAX_EGRAPH_STACK_LEVELS (UINT32_MAX/8)




/****************
 *  UNDO STACK  *
 ***************/

/*
 * Data for backtracking. Some of the undo data is already in
 * the propagation queue, but it's simpler to use a special undo stack.
 * TODO: check cost and revise this if needed.
 *
 * Operations that can be undone:
 * - merge classes of t1 and t2
 * - assertion of a distinct atom
 * - simplification of a composite when dmask change
 *
 * Other operations that require processing after backtracking
 * are also recorded in the trail_stack:
 * - a composite term created during the search needs to
 *   be reanalyzed after backtracking
 *
 */
typedef enum undo_tag {
  // undo operations
  UNDO_MERGE,
  UNDO_DISTINCT,
  UNDO_SIMPLIFY,
  // reanalyze operations: two variants
  REANALYZE_CONGRUENCE_ROOT,
  REANALYZE_COMPOSITE,
} undo_tag_t;

typedef struct {
  occ_t saved_occ;
  elabel_t saved_label;
} undo_merge_t;

typedef union undo_u {
  undo_merge_t merge;
  void *ptr;
} undo_t;

/*
 * Undo stack:
 * - each trail object consists of an 8bit tag (tag[i]) + a union (data[i])
 * Other components:
 * - top = top of the stack
 * - size = size of arrays tag and data
 *
 * Levels as in egraph_stack:
 * - level_index[k] = first trail object of level k
 * - nlevels = size of level_index array
 */
typedef struct undo_stack_s {
  unsigned char *tag;
  undo_t *data;
  uint32_t top;
  uint32_t size;

  uint32_t *level_index;
  uint32_t nlevels;
} undo_stack_t;





/**********************
 *  SIGNATURE BUFFERS *
 *********************/

/*
 * The signature (sigma c) of a composite term c is derived from
 * label[t[0]] ... label[t[n-1]] where t[0] ... t[n-1] are c's children.
 * - two composites c1 and c2 are congruent iff they have equal signature
 * - signature computation also includes normalization
 *
 * A signature is a pair tag + array of class labels, stored in a signature
 * buffer. size = size of the array sigma
 */
typedef struct signature_s {
  uint32_t size;
  uint32_t tag;  // encodes kind + arity
  elabel_t *sigma;
} signature_t;




/***********************
 *  CONGRUENCE TABLE   *
 **********************/

/*
 * Hash-table of composites: stores a unique representative
 * (congruence root) per signature. It's similar to int_hash_table.
 */
typedef struct congruence_table_s {
  composite_t **data;  // the hash table proper
  uint32_t size;       // its size (must be a power of 2)
  uint32_t nelems;     // number of elements
  uint32_t ndeleted;   // deleted elements
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
  signature_t buffer;  // for internal use
} congruence_table_t;


/*
 * Marker for deleted elements in the congruence table
 * Empty slots contain the NULL pointer
 */
#define DELETED_COMPOSITE ((composite_t *) 1)
#define NULL_COMPOSITE ((composite_t *) 0)

#define DEFAULT_CONGRUENCE_TBL_SIZE 256
#define MAX_CONGRUENCE_TBL_SIZE (UINT32_MAX/sizeof(composite_t*))
#define CONGRUENCE_TBL_RESIZE_RATIO 0.6
#define CONGRUENCE_TBL_CLEANUP_RATIO 0.2





/*******************************
 *  TRAIL STACK FOR PUSH/POP   *
 ******************************/

/*
 * At every push we save the number of terms
 * + the current propagation pointer
 */
typedef struct egraph_trail_s {
  uint32_t nterms;
  uint32_t prop_ptr;
} egraph_trail_t;

typedef struct egraph_trail_stack_s {
  uint32_t size;
  uint32_t top;
  egraph_trail_t *data;
} egraph_trail_stack_t;

#define DEFAULT_EGRAPH_TRAIL_SIZE 20
#define MAX_EGRAPH_TRAIL_SIZE (UINT32_MAX/sizeof(egraph_trail_t))





/*********************************************
 *  COMMUNICATION WITH OTHER THEORY SOLVERS  *
 ********************************************/

/*
 * The egraph can be used standalone or as a central solver
 * connected to the core and communicating with other solvers.
 *
 * Two kinds of solvers can be attached to the egraph:
 * - full solvers: right now, this means arithmetic and bitvector solver,
 *   a full solver is one that has its own atoms (and could be attached
 *   directly to the core).
 * - subsolvers are theory solvers that cannot work without the egraph,
 *   a subsolver can deal only with equalities and disequalities.
 *
 * Full solvers must implement the th_ctrl and th_smt interfaces
 * (defined in smt_core.h) and the th_egraph interface defined
 * below.
 *
 * Sub-solvers must implement the th_ctrl and th_egraph interfaces.
 *
 * The egraph does the following:
 * - forward commands it gets from the core to all attached solvers
 * - forward atom-processing commands to the full solvers
 * - propagate equalities and disequalities to all sub-solvers
 * Satellite solvers may propagate equalities to the egraph.
 *
 *
 * GENERIC EGRAPH INTERFACE
 * ========================
 *
 * A set of functions common to all satellite solvers is used by the
 * egraph during the search. To propagate equalities and disequalities
 * to a satellite solver, the egraph calls one of the following
 * functions (in the th_egraph interface).
 *
 * 1) void assert_equality(void *solver, thvar_t x1, thvar_t x2, int32_t id)
 *    notify solver that x1 and x2 are equal (after merging classes c1 and c2,
 *    with thvar[c1] = x1  and thvar[c2] = x2).
 *    id is the egraph edge that caused c1 and c2 to be merged.
 *
 * 2) void assert_disequality(void *solver, thvar_t x1, thvar_t x2, composite_t *cmp)
 *    notify solver that x1 != x2 holds.
 *    cmp is an explanation hint. It allows the egraph to correctly generate an
 *    explanation for x1 != x2 if that's needed later.
 *
 * 3) void assert_distinct(void *solver, uint32_t n, thvar_t *a, composite_t *cmp)
 *    notify solver that a[0] ... a[n-1] are all distinct
 *    as above, cmp is an explanation hint.
 *
 * For all three assert functions above, the satellite solver must
 * store the assertions internally and process them when propagate is
 * called.
 *
 * 4) bool check_diseq(void *solver, thvar_t x1 thvar_t x2)
 *    return true if (x1 != x2) holds in the solver at the base level.
 *    (don't need to be complete: may return false)
 *
 * 4a) bool is_constant(void *solver, thvar_t x)
 *     return true if x is a constant in the theory solver (optional)
 *     return false otherwise
 *
 * Optional function: if the solver propagates equalities to the egraph,
 * it must implement the following function.
 *
 *
 * 5) void expand_th_explanation(void *solver, thvar_t x1, thvar_t x2, void *expl, th_explanation_t *result)
 *
 *    When the solver propagates an equality t1 == t2, it must provide an opaque explanation
 *    object expl (a void * pointer). The egraph calls the function expand_th_explanation
 *    when it needs to expand expl to a set of antecedent atoms. The parameters passed to
 *    the function are x1 --> theory variable of t1 and x2 --> theory variable of t2.
 *    The function must construct a conjunction of constraints that imply t1 == t2.
 *    Each constraint may be of the following forms:
 *     - atom(l): an atom from the satellite solver, attached to literal l
 *     - eq(u, v): an equality (u==v) that was propagated by egraph to the solver
 *                 via a call to assert_equality.
 *     - diseq(u, v): a disequality (u!=v) that was propagated by egraph to the solver,
 *                via a call to assert_disequality or assert_distinct. This must be given
 *                as a pre_expl object.
 *    The set of constraints is stored in a th_explanation data structure that maintains
 *    three resizable vectors, for atoms, equalities, and diseq constraints.
 *
 *
 * Theory conflict and explanations
 * --------------------------------
 *
 * To construct theory conflicts, a satellite solver can
 * query the egraph for explanations using functions
 *  - egraph_explain_term_eq
 *  - egraph_store_diseq_pre_expl
 *  - egraph_expand_diseq_pre_expl
 * These functions are defined in egraph_explanation.c.
 *
 * Another function 'egraph_explain_term_diseq' is defined in
 * egraph_explanation.c but it cannot be used reliably to
 * lazily build an explanation for (x1 != x2). It may generate an
 * incorrect (non-causal) explanation. The hint passed to
 * assert_distinct and assert_disequality is not enough to rebuild the
 * correct explanation in all cases (cf. egraph_explanation.c).
 *
 * If the satellite solver performs an inference or theory propagation
 * with (x1 != x2) as antecedent, it must use an intermediate
 * 'pre_expl' object that keeps enough information to build an
 * explanation for (x1 != x2) if it is needed later.  At the time of
 * the inference: the satellite must record the pre_expl data using
 * function
 *
 *   egraph_store_diseq_pre_expl(egraph, t1, t2, hint, pre_expl) where
 *   - t1 must be the egraph term attached to x1
 *   - t2 must be the egraph term attached to x2
 *   - hint is the composite provided by the egraph in
 *     assert_disequality or assert_distinct
 *   - pre_expl is a pointer to a pre_expl_t structure
 *
 * If the explanation for (x1 != x2) is needed later on (i.e., must be expanded to a list of
 * literal), then the satellite solver must call
 *
 *   egraph_expand_diseq_pre_expl(egraph, pre_expl, ..)
 *
 * at that time.
 *
 *
 * Interface equalities (2010/01/13)
 * ---------------------------------
 *
 * In final check, the egraph and satellite solver attempt to build consistent
 * modesl. If that fails, interface equalities must be generated. The egraph
 * currently supports to variant implementations of final_check, that use
 * different functions provided by the satellite solvers.
 *
 *
 * Baseline final_check: for this variant, a satellite solver must implement
 * the following function.
 *
 * 6) uint32_t reconcile_model(void *solver, uint32_t max_eq)
 *
 *     This function is called in final_check by the egraph to enforce consistency
 *     between the egraph and the solver's internal model. There's a conflict
 *     between egraph and solver if there are two terms t1 and t2 in the egraph,
 *     and two theory variables x1 and x2 in the solver such that:
 *      - t1 and t2 are in different classes in the egraph
 *      - x1 and x2 are equal in the solver's model
 *      - x1 is t1's theory variable and x2 is t2's theory variable.
 *
 *     The solver should attempt to resolve such conflicts by changing the
 *     values of x1 and x2 if that's possible. Otherwise, it must construct
 *     the interface equality (eq t1 t2) in the egraph (by calling egraph_make_simple_eq).
 *     - max_eq is a bound on the number of interface equalities the solver is
 *       allowed to generate
 *     - the function must return the number of interface equalities actually created
 *       (0 means that the egraph and solver model are consistent).
 *
 *
 * Experimental final_check: this variant implements a more flexible
 * interface generation algorithms. The egraph attempts to resolve
 * conflict by merging classes. If that fails, it asks the satellite
 * solver to generate interface lemmmas. To support this, the
 * satellite solvers must implement the following functions:
 *
 * 6a) void prepare_model(void *solver)
 *
 *    This function is called in final_check before the egraph generates interface lemmas.
 *    The solver must build a local model at this point (enough to be able to check
 *    whether two variables x1 and x2 have the same or different values in the local model).
 *
 * 6b) bool equal_in_model(void *solver, thvar_t x1, thvar_t x2)
 *
 *    Must return true if x1 and x2 have the same value in the model and false if
 *    they have different values. (So the model must assign a value to all theory variables).
 *
 * 6c) void gen_interface_lemma(void *solver, literal_t l, thvar_t x1, thvar_t x2, bool equiv)
 *
 *    Ask the theory solver to create a lemmas of the form (l => x1 /= x2).
 *    If equiv is true, then the solver can also create the reverse implication:  (x1 /= x2 => l).
 *
 * 6d) void release_model(void *solver)
 *
 *    Called at the end of final_check. This means that the local model built by prepare_model
 *    is no longer needed. The solver can free whatever internal data structures it used for
 *    the local model, or do other cleanup.
 *
 *
 * 6e) ipart_t *build_model_partition(void *solver)
 *
 *    Called after prepare_model and before release model. The solver
 *    must construct a partition of its variables: two variables are
 *    in the same class if they have the same value in the model. This
 *    can be restricted so that the partition uses one theory variable
 *    per Egraph class.
 *
 *    The solver should use 'int_partition.h' to build this.
 *
 * 6f) void release_model_partition(void *solver, ipart_t *partition)
 *
 *    Called by the egraph when the partition is no longer needed.
 *
 *
 * In addition, all satellite solvers must implement the following functions
 * to link egraph terms and theory variables.
 *
 * 7) void attach_eterm(void *solver, thvar_t x, eterm_t u): attach u as term for variable x
 *    in solver. This must be the same function as used by the context.
 *
 * 8) eterm_t eterm_of_var(void *solver, thvar_t v)
 *    return the eterm t attached to v (or null_eterm if v has no eterm attached).
 *    This must be the same function as used by the context.
 *
 *
 * New function for theory branching (2010/10/27)
 * ----------------------------------------------
 *
 * If theory branching is enabled, the egraph must decide whether an atom l := (eq u1 u2)
 * must be assigned true or false when l is selected as decision literal. If u1 and u2 are both
 * attached to two theory variables x1 and x2, then the egraph can delegate the decision to
 * the theory solver. For this purpose, it calls the function
 *
 * 9) literal_t select_eq_polarity(void *solver, thvar_t x1, thvar_t x2, literal_t l)
 *    - l is a decision literal attached to an egraph atom (eq u1 u2)
 *    - x1 and x2 are the theory variables for u1 and u2, respectively
 *    - the theory solver must decide between assigning l true or false
 *    - the function must return l to set l := true or (not l) to set l := false
 *
 *
 *
 * THEORY-SPECIFIC INTERFACES
 * ==========================
 *
 * In addition to the common egraph interface defined above, the egraph needs theory-specific
 * functions to create terms and theory variables, and to build a global model. These are
 * grouped in interface descriptors that are distinct for each theory.
 *
 * Support for term creation
 * -------------------------
 *
 * For new terms of arithmetic, bitvector, or function types, the egraph may create a theory variable
 * and attach it to the new term. For this purpose, the theory solver must provide functions for
 * creating theory variables. These functions are the same as the ones used in the context:
 *
 * For arithmetic variables:
 * - thvar_t create_arith_var(void *arith_solver, bool is_int): create a new arithmetic variable.
 *   If is_int is true, the variable is integer, otherwise it's real.
 *
 * For bitvector variables
 * - thvar_t create_bv_var(void *bv_solver, uint32_t n): create a new bitvector variable.
 *   n = number of bits
 *
 * For function variables
 * - thvar_t create_fun_var(void *fun_solver, type_t tau): create a new function/array variable
 *   tau = its type (in the global type table)
 *
 *
 * Support for model construction (global model)
 * ---------------------------------------------
 *
 * An egraph model maps term occurrences to objects (defined in
 * concrete_values.h).  To build the model, the egraph must query the
 * satellite solvers for rational/integer or bitvector values assigned
 * to theory variables.
 *
 * For this, we use the following functions:
 *
 *  a) arithmetic solver
 *     ----------------
 *    bool value_in_model(void *arith_solver, thvar_t x, rational_t *v)
 *
 *    Must return true if the arithmetic solver has a value for x in its current model
 *    and that value is rational (or integer). It must then copy that value in v.
 *    The function must return false otherwise.
 *
 *    This function should be identical to the function of the same name in
 *    the arithmetic solver arith_interface (used by the context).
 *
 *
 *  b) bitvector solver
 *     ----------------
 *    bool value_in_model(void *bv_solver, thvar_t x, bvconstant_t *b)
 *
 *    Must return true if the bitvector solver has a value for x in its current model.
 *    It must then copy that value in b. It must return false otherwise.
 *
 *    This function should be identical to the function of the same name in the
 *    bvsolver_interface used by the context.
 *
 *
 *  c) function-theory solver
 *     ----------------------
 *
 *    A function subsolver cannot be used without the egraph. So model
 *    construction requires close coordination between the egraph and
 *    the subsolver. We use a two-step approach:
 *
 *    - First the function solver constructs an abstract model (via
 *      fun_maps/abstract_values).  This may introduce new objects
 *      (fresh particles) that are not currently present in the
 *      egraph. The only requirement is that all fresh particles must be
 *      distinct from each other and from any existing egraph term.
 *
 *    - Then the egraph converts the abstract model into a concrete
 *      model by mapping the abstract particles to concrete values.
 *
 *    To support this, the function solver must implement the following functions:
 *
 *    1) void build_model(void *solver, pstore_t *store):
 *       Build a model that maps theory variables to abstract maps (map_t).
 *       Abstract values (particles) necessary for this model must be allocated in store.
 *
 *    2) map_t *value_in_model(void *solver, thvar_t x):
 *       Return the value assigned to theory variable x in the model.
 *       Return NULL if the value of x is not available.
 *
 *    3) void free_model(void *solver):
 *       Notify the solver that the model is no longer needed.
 *
 */


/*
 * THEORY EXPLANATION OBJECT
 */

/*
 * Disequality pre-explanation object:
 * This store enough data to encode the antecedents of a derived
 * disequality. A disequality is derived by one of the following
 * inference rules:
 * Rule 1) (eq u1 u2) = false, u1 == t1,  u2 == t2 IMPLIES (t1 != t2)
 * Rule 2) (distinct ... u2 ... u1 ,...) == true,
 *          u1 == t1, u2 == t2 IMPLIES (t1 != t2)
 * To reliably reconstruct the explanation for (t1 != t2) later on,
 * we must store
 * - the composite involved (either (eq u1 u2) or (distinct ....))
 * - the terms involved, namely, u1, u2, t1, and t2.
 */
typedef struct diseq_pre_expl_s {
  composite_t *hint;
  eterm_t t1, u1;
  eterm_t t2, u2;
} diseq_pre_expl_t;


// equality constraint in a theory explanation
typedef struct th_eq_s {
  eterm_t lhs;
  eterm_t rhs;
} th_eq_t;

// explanation object = three vectors (with hidden headers)
// see theory_explanations.h and theory_explanations.c
typedef struct th_explanation_s {
  literal_t *atoms;
  th_eq_t *eqs;
  diseq_pre_expl_t *diseqs;
} th_explanation_t;



/*
 * GENERIC EGRAPH INTERFACE
 */
typedef void (*assert_eq_fun_t)(void *satellite, thvar_t x1, thvar_t x2, int32_t id);
typedef void (*assert_diseq_fun_t)(void *satellite, thvar_t x1, thvar_t x2, composite_t *hint);
typedef bool (*assert_distinct_fun_t)(void *satellite, uint32_t n, thvar_t *a, composite_t *hint);
typedef bool (*check_diseq_fun_t)(void *satellite, thvar_t x1, thvar_t x2);
typedef bool (*is_constant_fun_t)(void *satellite, thvar_t x);
typedef void (*expand_eq_exp_fun_t)(void *satellite, thvar_t x1, thvar_t x2, void *expl, th_explanation_t *result);
typedef uint32_t (*reconcile_model_fun_t)(void *satellite, uint32_t max_eq);
typedef void (*prepare_model_fun_t)(void *satellite);
typedef bool (*equal_in_model_fun_t)(void *satellite, thvar_t x1, thvar_t x2);
typedef void (*gen_inter_lemma_fun_t)(void *satellite, literal_t l, thvar_t x1, thvar_t x2, bool equiv);
typedef void (*release_model_fun_t)(void *satellite);
typedef ipart_t *(*build_partition_fun_t)(void *satellite);
typedef void (*free_partition_fun_t)(void *satellite, ipart_t *partition);
typedef void (*attach_to_var_fun_t)(void *satellite, thvar_t x, eterm_t t);
typedef eterm_t (*get_eterm_fun_t)(void *satellite, thvar_t x);
typedef literal_t (*select_eq_polarity_fun_t)(void *satellite, thvar_t x, thvar_t y, literal_t l);

typedef struct th_egraph_interface_s {
  assert_eq_fun_t          assert_equality;
  assert_diseq_fun_t       assert_disequality;
  assert_distinct_fun_t    assert_distinct;
  check_diseq_fun_t        check_diseq;
  is_constant_fun_t        is_constant;
  expand_eq_exp_fun_t      expand_th_explanation;
  reconcile_model_fun_t    reconcile_model;
  prepare_model_fun_t      prepare_model;
  equal_in_model_fun_t     equal_in_model;
  gen_inter_lemma_fun_t    gen_interface_lemma;
  release_model_fun_t      release_model;
  build_partition_fun_t    build_model_partition;
  free_partition_fun_t     release_model_partition;
  attach_to_var_fun_t      attach_eterm;
  get_eterm_fun_t          eterm_of_var;
  select_eq_polarity_fun_t select_eq_polarity;
} th_egraph_interface_t;




/*
 * ARITHMETIC-SPECIFIC INTERFACE
 */
typedef thvar_t (*make_arith_var_fun_t)(void *solver, bool is_int);
typedef bool (*arith_val_fun_t)(void *arith_solver, thvar_t x, rational_t *v);

typedef struct arith_egraph_interface_s {
  make_arith_var_fun_t  create_arith_var;
  arith_val_fun_t       value_in_model;
} arith_egraph_interface_t;



/*
 * BITVECTOR-SPECIFIC INTERFACE
 */
typedef thvar_t (*make_bv_var_fun_t)(void *solver, uint32_t n);
typedef bool (*bv_val_fun_t)(void *solver, thvar_t x, bvconstant_t *v);

typedef struct bv_egraph_interface_s {
  make_bv_var_fun_t    create_bv_var;
  bv_val_fun_t         value_in_model;
} bv_egraph_interface_t;



/*
 * FUNCTION-SOLVER INTERFACE
 */
typedef thvar_t (*make_fun_var_fun_t)(void *solver, type_t tau);
typedef void (*fun_build_model_fun_t)(void *fun_solver, pstore_t *store);
typedef map_t *(*fun_val_fun_t)(void *fun_solver, thvar_t x);
typedef void (*fun_free_model_fun_t)(void *fun_solver);

typedef struct fun_egraph_interface_s {
  make_fun_var_fun_t    create_fun_var;
  fun_build_model_fun_t build_model;
  fun_val_fun_t         value_in_model;
  fun_free_model_fun_t  free_model;
} fun_egraph_interface_t;



/***********
 *  MODEL  *
 **********/

/*
 * Auxiliary structures used in model construction. We now use a
 * global fresh_value_maker to construct fresh values. For this to
 * work properly, we must assign a value to all classes of type tau
 * before attempting to create fresh values of type tau. To do this,
 * we sort the classes by rank when rank c = depth of c's type:
 * - all atomitc types have depth 0
 * - a function or tuple type has positive depth equal to 1 + max depth
 *   of the types it depends on.
 * Then we assign values to classes in increasing order of type depth.
 * This works since fresh values of type tau are used to construct
 * arrays/functions of some function type that contains tau.
 *
 *
 * Model components:
 * - value = maps classes to concrete values (if c is not a root class
 *   then value[c] = null_value).
 * - root_classes = vector of all root classes
 * - rank_ctr = vector of counters for sorting the root classes by rank
 * - pstore = auxiliary particle store used by the function solver
 * - fval_maker = data structure to create fresh values
 * - internal buffers for rational and bitvector values
 *
 */
typedef struct egraph_model_s {
  value_t *value;
  pstore_t *pstore;
  fresh_val_maker_t *fval_maker;
  ivector_t root_classes;
  ivector_t rank_ctr;
  rational_t arith_buffer;
  bvconstant_t bv_buffer;
} egraph_model_t;






/******************
 *  CACHED DATA   *
 *****************/

/*
 * Lemmas can be added to the core by the egraph:
 *
 * 1) Expansion of a (distinct ...) atom. When
 *   "not (distinct t1 ... t_n)" is asserted, then the clause
 *   "(distinct t1 ... t_n) or (eq t1 t2) or (eq t1 t3) ... or (eq t_n-1 t_n)"
 *   is added to the core
 *
 * 2) Ackermann clause. A heuristic may create clauses of the form
 *   "(eq t1 u1) and (eq t2 u2) ... (eq t_n u_n) implies
 *           (eq (f t_1 ... t_n) (f u_1 ... u_n))"
 *
 * An internal cache stores data about which lemmas have been created (to
 * prevents multiple generation of the same lemma).
 * - for a distinct-expansion, the cache stores <DISTINCT_LEMMA, u> where u = term id of
 *   the (distinct ...) term
 * - for an Ackermann clause, the cache stores <ACKERMANN_LEMMA, u, v> where u and v are
 *   the term ids of (f t_1 ... t_n) and (f u_1 ... u_n), respectively.
 */
typedef enum elemma_tag {
  DISTINCT_LEMMA = 0,
  ACKERMANN_LEMMA = 1,
} elemma_tag_t;



/****************
 *  STATISTICS  *
 ***************/

// search statistics
typedef struct egraph_stats_s {
  uint32_t app_reductions;

  uint32_t eq_props;         // equalities propagated by satellite solvers (simplex)
  uint32_t th_props;         // propagations from egraph to core
  uint32_t th_conflicts;     // conflicts detected by egraph
  uint32_t nd_lemmas;        // number of non-distinct lemmas

  // counters related to ackermann clauses
  uint32_t aux_eqs;          // number of equality terms created
  uint32_t boolack_lemmas;   // number of boolean ackermann instances created
  uint32_t ack_lemmas;       // number of non-boolean ackermann instances created

  // statistics on interface equalities
  uint32_t final_checks;     // number of calls to final check
  uint32_t interface_eqs;    // number of interface equalities generated

} egraph_stats_t;



/**************
 *   EGRAPH   *
 *************/

typedef struct egraph_s egraph_t;

struct egraph_s {
  /*
   * Attached smt_core + type table
   */
  smt_core_t *core;
  type_table_t *types;

  /*
   * base_level and decision_level mirror the same counters
   * in the attached core.
   * - base_level keeps track of the number of calls to push
   * - decision_level is incremented during the search, decremented
   *   during backtracking
   */
  uint32_t base_level;
  uint32_t decision_level;

  /*
   * Presearch flag: set on call to start_internalization
   * Cleared on call to start_search.
   */
  bool presearch;

  /*
   * Number of (distinct ...) terms allocated
   */
  uint32_t ndistincts;

  /*
   * Number of atoms
   */
  uint32_t natoms;

  /*
   * True if the egraph contains high-order terms
   */
  bool is_high_order;

  /*
   * Statistics
   */
  egraph_stats_t stats;

  /*
   * Option flag and search parameters
   * each option is a single bit in the option flag
   */
  uint32_t options;

  /*
   * Limits on ackermann clause generation
   * - max_ackermann = bound on the number of non-boolean Ackermann lemmas
   * - max_boolackermann = bound on the number of boolean Ackermann lemmas
   * - aux_eq_quota = bound on the number of auxiliary equalities created
   *   by Ackermann lemmas
   */
  uint32_t max_ackermann;
  uint32_t max_boolackermann;
  uint32_t aux_eq_quota;

  /*
   * Thresholds to trigger the generation of Ackermann/Boolean Ackermann
   * lemmas: when a candidate pair (t1 == t2) is selected, a counter
   * is increased. When that counter reaches the threshold, a lemma
   * is generated.
   */
  uint16_t ackermann_threshold;
  uint16_t boolack_threshold;

  /*
   * Two candidates for the next Ackermann lemma:
   * when the egraph detects a conflict while processing (t1 == t2)
   * then it stores t1 in ack_left and t2 in ack_right if
   * (t1 == t2) was propagated by BASIC_CONGRUENCE.
   */
  occ_t ack_left, ack_right;

  /*
   * Limit on the number of interface equalities created
   * in each call to final_check
   */
  uint32_t max_interface_eqs;

  /*
   * Main components
   */
  class_table_t classes;
  eterm_table_t terms;
  egraph_stack_t stack;
  undo_stack_t undo;
  distinct_table_t dtable;
  congruence_table_t ctable;
  ltag_table_t tag_table;

  update_graph_t *update_graph; // optional

  /*
   * Push/pop stack
   */
  egraph_trail_stack_t trail_stack;

  /*
   * Auxiliary buffers and structures
   */
  int_htbl_t *const_htbl;     // for hash-consing of constants (allocated on demand)
  int_htbl_t htbl;            // for hash-consing of composite terms
  object_store_t atom_store;  // for creating atoms
  cache_t cache;              // for creating lemmas

  int_hmap_t *imap;           // for or-congruence explanations
  signature_t sgn;            // auxiliary buffer for congruence closure
  arena_t arena;              // stack-based allocation
  ivector_t expl_queue;       // vector used as a queue of edges (explanation queue)
  ivector_t expl_vector;      // vector of literals for conflict/explanations
  pvector_t cmp_vector;       // generic vector to store composites
  ivector_t aux_buffer;       // generic buffer used in term construction
  int_stack_t istack;         // generic stack for recursive processsing


  /*
   * Experimental: attempt to produce better equality explanation
   * - when the egraph knows (t1 == t2) it can propagate a literal l := true
   *   where l is attached to (eq t1 t2).
   * - by default, we explore the egraph merge trees to construct an
   *   explanation for (t1 == t2)
   * - if short_cuts is true, we try to just use l as the explanation for (t1 == t2),
   *   but we have to make sure this does not introduce circularities.
   * - top_id is intended to prevent circular explanation
   */
  bool short_cuts;            // enable/disable short cuts in explanations
  int32_t top_id;             // used when building explanations

  /*
   * Support for model reconciliation
   */
  ivector_t interface_eqs;    // pairs of term occurrences (for interface lemmas)
  uint32_t reconcile_top;     // top of the undo stack when reconcile started
  uint32_t reconcile_neqs;    // number of equalities when reconcile started
  bool reconcile_mode;        // true if the egraph has some edges for model reconciliation


  /*
   * Support for on-the-fly creation of composite terms.
   * Composites created at decision_level > base_level
   * may need to be reactivated after backtracking. They
   * are stored in reanalyze_vector.
   */
  pvector_t reanalyze_vector;

  /*
   * Theory explanation object: for building explanation of equalities
   * propagated by a subsolver
   */
  th_explanation_t th_expl;

  /*
   * Helper for the array theory solver
   * allocated on demand
   */
  ppart_t *app_partition;

  /*
   * Satellite solvers and interface descriptors
   *
   * Generic:
   * - th[i] = solver for theory i
   * - ctrl[i] = its control interface
   * - eg[i] = its egraph interface
   *
   * Theory specific descriptors
   * - arith_smt:   core interface for arith solver
   * - bv_smt:      core interface for bitvector solver
   * - arith_eg: egraph interface for arith solver
   * - bv_eg:    egraph interface for the bitvector solver
   * - fun_eg:   egraph interface for the array/function solver
   */
  void *th[NUM_SATELLITES];
  th_ctrl_interface_t *ctrl[NUM_SATELLITES];
  th_egraph_interface_t *eg[NUM_SATELLITES];

  th_smt_interface_t *arith_smt;
  th_smt_interface_t *bv_smt;

  arith_egraph_interface_t *arith_eg;
  bv_egraph_interface_t  *bv_eg;
  fun_egraph_interface_t *fun_eg;


  /*
   * Model structure
   */
  egraph_model_t mdl;
};


#define DEFAULT_EXPL_VECTOR_SIZE  20
#define DEFAULT_CMP_VECTOR_SIZE   20


/*
 * Option flags:
 * - each mask selects a bit in the option word
 * - bit == 1 means option enabled, 0 means option disabled
 *
 * DYNAMIC_ACKERMANN enables generation of ackermann lemmas for non-boolean terms.
 * If it's enabled, max_ackermann is a bound on the number of lemmas generated.
 *
 * DYNAMIC_BOOLACKERMANN enables the generation of ackermann lemmas for boolean terms.
 * If that's enabled, max_boolackermann is a bound on the number of lemmas generated.
 *
 * OPTIMISTIC_FCHECK selects the experimental version of final_check instead of the
 * baseline verion.
 *
 * In addition, aux_eq_quota is a bound on the total number of new equalities allowed
 * for ackermann lemmas.
 *
 * MAX_INTERFACE_EQS is a bound on the number of interface equalities created
 * in each call to final_check.
 */
#define EGRAPH_DYNAMIC_ACKERMANN       0x1
#define EGRAPH_DYNAMIC_BOOLACKERMANN   0x2
#define EGRAPH_OPTIMISTIC_FCHECK       0x4
#define EGRAPH_DISABLE_ALL_OPTIONS     0x0

#define DEFAULT_MAX_ACKERMANN         1000
#define DEFAULT_MAX_BOOLACKERMANN     600000 // unlimited
#define DEFAULT_AUX_EQ_QUOTA          100

#define DEFAULT_ACKERMANN_THRESHOLD   8
#define DEFAULT_BOOLACK_THRESHOLD     8

#define DEFAULT_MAX_INTERFACE_EQS     200


//  disable boolean and non-boolean ackermann
#define EGRAPH_DEFAULT_OPTIONS  EGRAPH_DISABLE_ALL_OPTIONS



#endif /* __EGRAPH_TYPES_H */
