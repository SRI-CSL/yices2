/*************************
 *  THEORY EXPLANATIONS  *
 ************************/

#include <stdint.h>
#include <assert.h>

#include "memalloc.h"
#include "theory_explanations.h"


/*
 * Delete all three vectors in e
 */
void delete_th_explanation(th_explanation_t *e) {
  if (e->atoms != NULL) {
    safe_free(av_header(e->atoms));
    e->atoms = NULL;
  }
  if (e->eqs != NULL) {
    safe_free(eqv_header(e->eqs));
    e->eqs = NULL;
  }
  if (e->diseqs != NULL) {
    safe_free(diseqv_header(e->diseqs));
    e->diseqs = NULL;
  }
}


/*
 * Reset the three vectors
 */
void reset_th_explanation(th_explanation_t *e) {
  if (e->atoms != NULL) {
    av_header(e->atoms)->size = 0;
  }
  if (e->eqs != NULL) {
    eqv_header(e->eqs)->size = 0;
  }
  if (e->diseqs != NULL) {
    diseqv_header(e->diseqs)->size = 0;
  }
}


/*
 * Add an atom to a theory explanation
 * - l = literal attached to the atom
 */
void th_explanation_add_atom(th_explanation_t *e, literal_t l) {
  literal_t *atm;
  atom_vector_t *av;
  uint32_t i, n;

  atm = e->atoms;
  if (atm == NULL) {
    av = (atom_vector_t *) safe_malloc(sizeof(atom_vector_t) + DEF_ATOM_VECTOR_SIZE * sizeof(literal_t));
    av->size = 1;
    av->capacity = DEF_ATOM_VECTOR_SIZE;
    e->atoms = av->data;
    av->data[0] = l;
  } else {
    av = av_header(atm);
    i = av->size;
    n = av->capacity;
    if (i == n) {
      n ++;
      n += n>>1; // increase capacity by 50%
      if (n > MAX_ATOM_VECTOR_SIZE) {
        out_of_memory(); // abort
      }
      av = (atom_vector_t *) safe_realloc(av, sizeof(atom_vector_t) + n * sizeof(literal_t));
      av->capacity = n;
      e->atoms = av->data;
    }
    assert(i < n);
    av->data[i] = l;
    av->size = i+1;
  }
}

/*
 * Add equality t1 == t2 to e
 */
void th_explanation_add_eq(th_explanation_t *e, eterm_t t1, eterm_t t2) {
  th_eq_t *eqs;
  eq_vector_t *eqv;
  uint32_t i, n;

  eqs = e->eqs;
  if (eqs == NULL) {
    eqv = (eq_vector_t *) safe_malloc(sizeof(eq_vector_t) + DEF_EQ_VECTOR_SIZE * sizeof(th_eq_t));
    eqv->size = 1;
    eqv->capacity = DEF_EQ_VECTOR_SIZE;
    e->eqs = eqv->data;
    eqv->data[0].lhs = t1;
    eqv->data[0].rhs = t2;
  } else {
    eqv = eqv_header(eqs);
    i = eqv->size;
    n = eqv->capacity;
    if (i == n) {
      n ++;
      n += n>>1;
      if (n > MAX_EQ_VECTOR_SIZE) {
        out_of_memory();
      }
      eqv = (eq_vector_t *) safe_realloc(eqv, sizeof(eq_vector_t) + n * sizeof(th_eq_t));
      eqv->capacity = n;
      e->eqs = eqv->data;
    }
    assert(i < n);
    eqv->data[i].lhs = t1;
    eqv->data[i].rhs = t2;
    eqv->size = i + 1;
  }
}


/*
 * Add a disequality pre-explanation
 */
void th_explanation_add_diseq(th_explanation_t *e, diseq_pre_expl_t *d) {
  diseq_pre_expl_t *diseqs;
  diseq_vector_t *diseqv;
  uint32_t i, n;

  diseqs = e->diseqs;
  if (diseqs == NULL) {
    diseqv = (diseq_vector_t *) safe_malloc(sizeof(diseq_vector_t) + DEF_DISEQ_VECTOR_SIZE * sizeof(diseq_pre_expl_t));
    diseqv->size = 1;
    diseqv->capacity = DEF_DISEQ_VECTOR_SIZE;
    e->diseqs = diseqv->data;
    diseqv->data[0] = *d;
  } else {
    diseqv = diseqv_header(diseqs);
    i = diseqv->size;
    n = diseqv->capacity;
    if (i == n) {
      n ++;
      n += n>>1;
      if (n > MAX_DISEQ_VECTOR_SIZE) {
        out_of_memory();
      }
      diseqv = (diseq_vector_t *) safe_realloc(diseqv, sizeof(diseq_vector_t) + n * sizeof(diseq_pre_expl_t));
      diseqv->capacity = n;
      e->diseqs = diseqv->data;
    }
    assert(i < n);
    diseqv->data[i] = *d;
    diseqv->size = i + 1;
  }
}

