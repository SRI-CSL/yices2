/*
 * Print smt core data
 */

#ifndef __SOLVER_PRINTER_H
#define __SOLVER_PRINTER_H

#include <stdio.h>

#include "int_vectors.h"
#include "smt_core.h"
#include "gates_hash_table.h"

#if 0
// NOT DONE YET

#include "egraph_types.h"
#include "idl_floyd_warshall.h"
#include "rdl_floyd_warshall.h"
#include "simplex_types.h"
#include "fun_solver.h"
#include "bit_solver.h"
#include "bvsolver.h"
#include "context.h"

#endif


/*
 * Basic objects
 */
extern void print_bval(FILE *f, bval_t b);
extern void print_status(FILE *f, smt_status_t s);
extern void print_bvar(FILE *f, bvar_t x);
extern void print_literal(FILE *f, literal_t l);


/*
 * Clauses
 */
extern void print_unit_clause(FILE *f, literal_t l);
extern void print_binary_clause(FILE *f, literal_t l1, literal_t l2);
extern void print_litarray(FILE *f, uint32_t n, literal_t *a);
extern void print_clause(FILE *f, clause_t *cl);

extern void print_unit_clauses(FILE *f, smt_core_t *core);
extern void print_binary_clauses(FILE *f, smt_core_t *core);
extern void print_problem_clauses(FILE *f, smt_core_t *core);
extern void print_learned_clauses(FILE *f, smt_core_t *core);
extern void print_clauses(FILE *f, smt_core_t *core);
extern void print_all_clauses(FILE *f, smt_core_t *core);
extern void print_lemmas(FILE *f, smt_core_t *core);

/*
 * Core solver state
 */
extern void print_boolean_assignment(FILE *f, smt_core_t *core);
extern void print_conflict(FILE *f, smt_core_t *core);
extern void print_smt_core(FILE *f, smt_core_t *core);


/*
 * Boolean combinators/hash-consing
 */
extern void print_boolgate(FILE *f, boolgate_t *g);
extern void print_boolgate_list(FILE *f, lnkgate_t *list);
extern void print_boolgate_levlist(FILE *f, levlist_t *lv);
extern void print_gate_table_stack(FILE *f, gate_table_t *tbl);
extern void print_gate_table_htbl(FILE *f, gate_table_t *tbl);
extern void print_gate_table(FILE *f, gate_table_t *tbl);


#if 0
/*
 * Initialize the internal name table based on a context
 * (must be called after internalization).
 */
extern void printer_init(context_t *ctx);
extern void printer_cleanup(void);


/*
 * Basic egraph objects
 */
extern void print_etype(FILE *f, etype_t tau);
extern void print_theory_id(FILE *f, etype_t tau);
extern void print_eterm_id(FILE *f, eterm_t t);
extern void print_occurrence(FILE *f, occ_t t);
extern void print_class_id(FILE *f, class_t c);
extern void print_label(FILE *f, elabel_t l);
extern void print_dmask(FILE *f, uint32_t d);


/*
 * Composites and signatures
 */
extern void print_composite(FILE *f, composite_t *c);
extern void print_signature(FILE *f, signature_t *s);


/*
 * Parent vectors
 */
extern void print_parents(FILE *f, use_vector_t *v);
extern void print_parents_details(FILE *f, use_vector_t *v);


/*
 * Theory explanations
 */
extern void print_th_eq(FILE *f, th_eq_t *eq);
extern void print_th_diseq(FILE *f, diseq_pre_expl_t *diseq);
extern void print_theory_explanation(FILE *f, th_explanation_t *e);


/*
 * Terms/classes in the egraph
 */
extern void print_eterm(FILE *f, egraph_t *egraph, eterm_t t);
extern void print_eterm_def(FILE *f, egraph_t *egraph, eterm_t t);
extern void print_eterm_details(FILE *f, egraph_t *egraph, eterm_t t);

extern void print_class(FILE *f, egraph_t *egraph, class_t c);
extern void print_class_details(FILE *f, egraph_t *egraph, class_t c);

extern void print_class_of_term(FILE *f, egraph_t *egraph, eterm_t t);
extern void print_class_of_occ(FILE *f, egraph_t *egraph, occ_t t);

/*
 * Parents of all terms in the class of t
 */
extern void print_parents_of_term(FILE *f, egraph_t *egraph, eterm_t t);


/*
 * Egraph atoms
 */
extern void print_egraph_atom(FILE *f, egraph_t *egraph, atom_t *atom);
extern void print_egraph_atom_of_literal(FILE *f, egraph_t *egraph, literal_t l);


/*
 * All terms/atoms/root classes in egraph
 */
extern void print_egraph_terms(FILE *f, egraph_t *egraph);
extern void print_egraph_terms_details(FILE *f, egraph_t *egraph);
extern void print_egraph_atoms(FILE *f, egraph_t *egraph);
extern void print_egraph_root_classes(FILE *f, egraph_t *egraph);
extern void print_egraph_root_classes_details(FILE *f, egraph_t *egraph);


/*
 * Print the congruence table (all congruence roots are displayed)
 */
extern void print_egraph_congruence_roots(FILE *f, egraph_t *egraph);



/*
 * IDL variables and atoms
 */
extern void print_idl_var(FILE *f, thvar_t x);
extern void print_idl_atom(FILE *f, idl_atom_t *atom);
extern void print_idl_atoms(FILE *f, idl_solver_t *idl);
extern void print_idl_var_value(FILE *f, idl_solver_t *idl, thvar_t x);


/*
 * RDL variables, constants, and atoms
 */
extern void print_rdl_var(FILE *f, thvar_t x);
extern void print_rdl_const(FILE *f, rdl_const_t *c);
extern void print_rdl_atom(FILE *f, rdl_atom_t *atom);
extern void print_rdl_atoms(FILE *f, rdl_solver_t *rdl);
extern void print_rdl_var_value(FILE *f, rdl_solver_t *rdl, thvar_t x);


/*
 * Print some info (internal counters + levels) on solvers
 */
extern void print_core_summary(FILE *f, smt_core_t *core);
extern void print_egraph_summary(FILE *f, egraph_t *egraph);
extern void print_context_summary(FILE *f, context_t *context);


/*
 * Internalization codes for a context
 */
extern void print_internal_code_of_term(FILE *f, context_t *ctx, term_t t);
extern void print_internalization(FILE *f, context_t *ctx, term_t t); // more details
extern void print_internalization_table(FILE *f, context_t *ctx);
extern void print_term_vector(FILE *f, context_t *ctx, ivector_t *v);
extern void print_partition(FILE *f, context_t *ctx);
extern void print_substitutions(FILE *f, context_t *ctx);


/*
 * Tables of arithmetic variables and atoms
 */
extern void print_arith_vartable(FILE *f, arith_vartable_t *table);
extern void print_arith_atomtable(FILE *f, arith_vartable_t *vtbl, arith_atomtable_t *atbl);


/*
 * Internals of simplex solver
 */
extern void print_matrix(FILE *f, arith_vartable_t *vtbl, matrix_t *matrix);
extern void print_elim_matrix(FILE *f, arith_vartable_t *vtbl, elim_matrix_t *elim);
extern void print_fixed_var_vector(FILE *f, arith_vartable_t *vtbl, fvar_vector_t *fvars);

extern void print_simplex_vars(FILE *f, simplex_solver_t *solver);
extern void print_simplex_atoms(FILE *f, simplex_solver_t *solver);
extern void print_simplex_row(FILE *f, simplex_solver_t *solver, row_t *row);
extern void print_simplex_matrix(FILE *f, simplex_solver_t *solver);
extern void print_simplex_basic_vars(FILE *f, simplex_solver_t *solver);
extern void print_simplex_bounds(FILE *f, simplex_solver_t *solver);
extern void print_simplex_assignment(FILE *f, simplex_solver_t *solver);
extern void print_simplex_allvars(FILE *f, simplex_solver_t *solver);

extern void print_simplex_vardef(FILE *f, simplex_solver_t *solver, thvar_t v);
extern void print_simplex_var(FILE *f, simplex_solver_t *solver, thvar_t v);
extern void print_simplex_atom(FILE *f, simplex_solver_t *solver, int32_t id);
extern void print_simplex_atomdef(FILE *f, simplex_solver_t *solver, bvar_t v);
extern void print_simplex_atom_of_literal(FILE *f, simplex_solver_t *solver, literal_t l);
extern void print_simplex_buffer(FILE *f, simplex_solver_t *solver);
extern void print_simplex_bound(FILE *f, simplex_solver_t *solver, uint32_t i);

// value of v in the current assignment
extern void print_simplex_var_value(FILE *f, simplex_solver_t *solver, thvar_t v);



/*
 * Print row in a simplified form: replace fixed variables by their value
 */
extern void print_simplex_reduced_row(FILE *f, simplex_solver_t *solver, row_t *row);


/*
 * Print bounds on non-fixed variables
 * Use same variable names as in dsolver
 */
extern void print_simplex_bounds2(FILE *f, simplex_solver_t *solver);





/*
 * Array solver
 */
extern void print_fsolver_edge(FILE *f, fun_solver_t *solver, uint32_t edge_id);
extern void print_fsolver_edges(FILE *f, fun_solver_t *solver);
extern void print_fsolver_vars(FILE *f, fun_solver_t *solver);
extern void print_fsolver_roots(FILE *f, fun_solver_t *solver);
extern void print_fsolver_classes(FILE *f, fun_solver_t *solver);
extern void print_fsolver_apps(FILE *f, fun_solver_t *solver);
extern void print_fsolver_maps(FILE *f, fun_solver_t *solver);
extern void print_fsolver_base_values(FILE *f, fun_solver_t *solver);
extern void print_fsolver_diseqs(FILE *f, fun_solver_t *solver);
extern void print_fsolver_values(FILE *f, fun_solver_t *solver);


/*
 * Bit solver
 */
extern void print_bit_solver_unit_clauses(FILE *f, bit_solver_t *solver);
extern void print_bit_solver_binary_clauses(FILE *f, bit_solver_t *solver);
extern void print_bit_solver_problem_clauses(FILE *f, bit_solver_t *solver);
extern void print_bit_solver_learned_clauses(FILE *f, bit_solver_t *solver);
extern void print_bit_solver_clauses(FILE *f, bit_solver_t *solver);
extern void print_bit_solver_all_clauses(FILE *f, bit_solver_t *solver);
extern void print_bit_solver_assignment(FILE *f, bit_solver_t *solver);
extern void print_bit_solver_assumptions(FILE *f, bit_solver_t *solver);


/*
 * Bit-vector solver
 */
extern void print_bvsolver_var(FILE *f, thvar_t x);
extern void print_bvsolver_vardef(FILE *f, bv_solver_t *solver, thvar_t x);
extern void print_bvsolver_var_value(FILE *f, bv_solver_t *solver, thvar_t x);
extern void print_bvsolver_atom(FILE *f, bv_solver_t *solver, int32_t id);
extern void print_bvsolver_vars(FILE *f, bv_solver_t *solver);
extern void print_bvsolver_maps(FILE *f, bv_solver_t *solver);
extern void print_bvsolver_bitmaps(FILE *f, bv_solver_t *solver);
extern void print_bvsolver_atoms(FILE *f, bv_solver_t *solver);
extern void print_bvsolver_partition(FILE *f, bv_solver_t *solver);


#endif

#endif /* __SOLVER_PRINTER_H */
