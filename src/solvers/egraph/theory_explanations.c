/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*************************
 *  THEORY EXPLANATIONS  *
 ************************/

#include <stdint.h>
#include <assert.h>

#include "solvers/egraph/theory_explanations.h"
#include "utils/int_array_sort.h"
#include "utils/memalloc.h"
#include "utils/prng.h"


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



/*
 * Cleanup: remove duplicate literals
 */
void th_explanation_remove_duplicate_atoms(th_explanation_t *e) {
  atom_vector_t *av;
  uint32_t i, j, n;
  literal_t l0, l1;

  if (e->atoms != NULL) {
    av = av_header(e->atoms);
    n = av->size;
    if (n >= 2) {
      int_array_sort(av->data, n);
      l0 = av->data[0];
      j = 1;
      for (i=1; i<n; i++) {
	l1 = av->data[i];
	if (l0 != l1) {
	  av->data[j] = l1;
	  l0 = l1;
	  j ++;
	}
      }
      av->size = j;
    }
  }
}



/*
 * Remove duplicate equalities
 */

// normalize eq: make sure lhs < rhs
static void normalize_eq(th_eq_t *eq) {
  eterm_t aux;

  if (eq->lhs > eq->rhs) {
    aux = eq->lhs; eq->lhs = eq->rhs; eq->rhs = aux;
  }
}

static void normalize_eq_array(th_eq_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    normalize_eq(a + i);
  }
}


/*
 * Sort array a[0 ... n-1].
 * All sort function requires normalized equalities
 */
// eq1 < eq2 in lex ordering
static bool eq_precedes(th_eq_t *eq1, th_eq_t *eq2) {
  return eq1->lhs < eq2->lhs || (eq1->lhs == eq2->lhs && eq1->rhs < eq2->rhs);
}

static bool same_eq(th_eq_t *eq1, th_eq_t *eq2) {
  return eq1->lhs == eq2->lhs && eq1->rhs == eq2->rhs;
}


static void sort_eq_array(th_eq_t *a, uint32_t n);

// insertion sort
static void isort_eq_array(th_eq_t *a, uint32_t n) {
  uint32_t i, j, k;
  th_eq_t eq;

  for (i=1; i<n; i++) {
    eq = a[i];
    j = 0;
    while (eq_precedes(&a[j], &eq)) j++; // while (a[j] < eq) j++;
    k = i;
    while (k > j) {
      a[k] = a[k-1];
      k --;
    }
    a[j] = eq;
  }
}


// quick sort: requires n > 1
static void qsort_eq_array(th_eq_t *a, uint32_t n) {
  uint32_t i, j;
  th_eq_t x, y;

  assert(n > 1);

  // x = random pivot
  i = random_uint(n);
  x = a[i];

  // swap x and a[0];
  a[i] = a[0];
  a[0] = x;

  i = 0;
  j = n;
  do { j--; } while (eq_precedes(&x, &a[j]));           // while x < a[j]
  do { i++; } while (i <= j && eq_precedes(&a[i], &x)); // while a[i] < x

  while (i < j) {
    // swap a[i] and a[j]
    y = a[i]; a[i] = a[j]; a[j] = y;

    do { j--; } while (eq_precedes(&x, &a[j])); // while x < a[j]
    do { i++; } while (eq_precedes(&a[i], &x)); // while a[i] < x
  }

  // move pivot into a[j]
  a[0] = a[j];
  a[j] = x;

  // sort a[0...j-1] and a[j+1 .. n-1]
  sort_eq_array(a, j);
  j++;
  sort_eq_array(a + j, n - j);
}

// top-level sort
static void sort_eq_array(th_eq_t *a, uint32_t n) {
  if (n < 10) {
    isort_eq_array(a, n);
  } else {
    qsort_eq_array(a, n);
  }
}


void th_explanation_remove_duplicate_eqs(th_explanation_t *e) {
  eq_vector_t *eqv;
  uint32_t i, j, n;

  if (e->eqs != NULL) {
    eqv = eqv_header(e->eqs);
    n = eqv->size;
    if (n >= 2) {
      normalize_eq_array(eqv->data, n);
      sort_eq_array(eqv->data, n);
      j = 0;
      for (i=1; i<n; i++) {
	if (! same_eq(eqv->data + j, eqv->data + i)) {
	  j ++;
	  eqv->data[j] = eqv->data[i];
	}
      }
      eqv->size = j+1;
    }
  }

}
