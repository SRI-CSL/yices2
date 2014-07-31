/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRINT EGRAPH STRUCTURES
 */

#ifndef __EGRAPH_PRINTER_H
#define __EGRAPH_PRINTER_H

#include <stdio.h>

#include "solvers/egraph/egraph_types.h"


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

extern void print_egraph_conflict(FILE *f, egraph_t *egraph, ivector_t *expl_vector);


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




#endif /* __EGRAPH_PRINTER_H */
