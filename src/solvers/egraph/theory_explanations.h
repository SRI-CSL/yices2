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

/*************************
 *  THEORY EXPLANATIONS  *
 ************************/

/*
 * This module is part of the egraph code. It provides utilities for
 * managing theory explanations objects.
 *
 * A theory explanation consists of three vectors that store a set of
 * atoms, a set of equalities, and a set of disequalities, respectively.
 * These vectors are implemented as arrays with a hidden header.
 *
 * NOTE: the code overlaps (or repeats) other vector implementations
 * in smt_core.c. Should try to build a generic vector module?
 */

#ifndef __THEORY_EXPLANATIONS_H
#define __THEORY_EXPLANATIONS_H

#include <stdint.h>
#include <stddef.h>
#include <assert.h>

#include "solvers/egraph/egraph_types.h"


/*
 * Vectors: header + data
 */
typedef struct atom_vector_s {
  uint32_t capacity;
  uint32_t size;
  literal_t data[0];
} atom_vector_t;

typedef struct eq_vector_s {
  uint32_t capacity;
  uint32_t size;
  th_eq_t data[0];
} eq_vector_t;

typedef struct diseq_vector_s {
  uint32_t capacity;
  uint32_t size;
  diseq_pre_expl_t data[0];
} diseq_vector_t;


/*
 * Default initial capacity, maximal capacity
 * The default sizes must be positive
 */
#define DEF_ATOM_VECTOR_SIZE  10
#define DEF_EQ_VECTOR_SIZE    10
#define DEF_DISEQ_VECTOR_SIZE 4

#define MAX_ATOM_VECTOR_SIZE  (UINT32_MAX/sizeof(literal_t))
#define MAX_EQ_VECTOR_SIZE    (UINT32_MAX/sizeof(th_eq_t))
#define MAX_DISEQ_VECTOR_SIZE (UINT32_MAX/sizeof(diseq_pre_expl_t))


/*
 * Access to the headers
 */
static inline atom_vector_t *av_header(literal_t *v) {
  assert(v != NULL);
  return (atom_vector_t *)(((char *) v) - offsetof(atom_vector_t, data));
}

static inline eq_vector_t *eqv_header(th_eq_t *v) {
  assert(v != NULL);
  return (eq_vector_t *)(((char *) v) - offsetof(eq_vector_t, data));
}

static inline diseq_vector_t *diseqv_header(diseq_pre_expl_t *v) {
  assert(v != NULL);
  return (diseq_vector_t *)(((char *) v) - offsetof(diseq_vector_t, data));
}

static inline uint32_t get_av_size(literal_t *v) {
  return av_header(v)->size;
}

static inline uint32_t get_av_capacity(literal_t *v) {
  return av_header(v)->capacity;
}

static inline uint32_t get_eqv_size(th_eq_t *v) {
  return eqv_header(v)->size;
}

static inline uint32_t get_eqv_capacity(th_eq_t *v) {
  return eqv_header(v)->capacity;
}

static inline uint32_t get_diseqv_size(diseq_pre_expl_t *v) {
  return diseqv_header(v)->size;
}

static inline uint32_t get_diseqv_capacity(diseq_pre_expl_t *v) {
  return diseqv_header(v)->capacity;
}


/*
 * Operations on theory explanation object
 */
static inline void init_th_explanation(th_explanation_t *e) {
  e->atoms = NULL;
  e->eqs = NULL;
  e->diseqs = NULL;
}

extern void delete_th_explanation(th_explanation_t *e);


/*
 * Reset: empty all three vectors
 */
extern void reset_th_explanation(th_explanation_t *e);


/*
 * Add an atom, an equality, or a disequality to e
 */
extern void th_explanation_add_atom(th_explanation_t *e, literal_t l);
extern void th_explanation_add_eq(th_explanation_t *e, eterm_t t1, eterm_t t2);
extern void th_explanation_add_diseq(th_explanation_t *e, diseq_pre_expl_t *d);


/*
 * Cleanup functions to simplify the explanation object
 * - remove duplicate literals in e->atoms
 * - remove duplicate equalities in e->eqs
 *
 * TODO: Do we need more? (i.e, remove redundant equalities if any)
 */
extern void th_explanation_remove_duplicate_atoms(th_explanation_t *e);
extern void th_explanation_remove_duplicate_eqs(th_explanation_t *e);

// full cleanup
static inline void cleanup_th_explanation(th_explanation_t *e) {
  th_explanation_remove_duplicate_atoms(e);
  th_explanation_remove_duplicate_eqs(e);
}



#endif /* __THEORY_EXPLANATIONS_H */
