/*
 * INPUT TO THE EXISTS/FORALL SOLVER
 */

#include <assert.h>

#include "memalloc.h"
#include "index_vectors.h"
#include "ef_problem.h"

/*
 * Initialization: all empty
 */
void init_ef_prob(ef_prob_t *prob) {
  prob->all_evars = NULL;
  prob->all_uvars = NULL;
  prob->conditions = NULL;
  prob->num_cnstr = 0;
  prob->cnstr_size = 0;
  prob->cnstr = NULL;
}


/*
 * Reset to empty
 */
void reset_ef_prob(ef_prob_t *prob) {
  reset_index_vector(prob->all_evars);
  reset_index_vector(prob->all_uvars);
  reset_index_vector(prob->conditions);
  prob->num_cnstr = 0;
}


/*
 * Delete
 */
void delete_ef_prob(ef_prob_t *prob) {
  delete_index_vector(prob->all_evars);
  delete_index_vector(prob->all_uvars);
  delete_index_vector(prob->conditions);
  safe_free(prob->cnstr);
  prob->cnstr = NULL;
}


/*
 * Make the cnstr array larger
 */
static void extend_ef_prob(ef_prob_t *prob) {
  uint32_t n;

  n = prob->cnstr_size;
  if (n == 0) {
    n = DEF_EF_CNSTR_SIZE;
    assert(n < MAX_EF_CNSTR_SIZE);
    prob->cnstr_size = n;
    prob->cnstr = (ef_cnstr_t *) safe_malloc(n * sizeof(ef_cnstr_t));
  } else {
    n += (n >> 1) + 1; // about 50% larger
    if (n > MAX_EF_CNSTR_SIZE) {
      out_of_memory();
    }
    prob->cnstr_size = n;
    prob->cnstr = (ef_cnstr_t *) safe_realloc(prob->cnstr, n * sizeof(ef_cnstr_t));
  }
}


/*
 * Size of index vector v:
 */
static inline uint32_t iv_len(int32_t *v) {
  return (v == NULL) ? 0 : iv_size(v);
}

/*
 * For debugging: check that v is sorted (strictly increasing)
 */
#ifndef NDEBUG
static bool vector_is_sorted(int32_t *v) {
  uint32_t i, n;

  n = iv_len(v);
  for (i=1; i<n; i++) {
    if (v[i-1] >= v[i]) {
      return false;
    }
  }
  return true;
}
#endif


/*
 * Insert x in vector v if it's not already present
 * - v must be sorted
 */
static void insert_elem(int32_t **v, int32_t x) {
  int32_t *u;
  uint32_t i, j, k, n;

  u = *v;

  assert(vector_is_sorted(u));

  i = 0;
  n = iv_len(u);

  j = n;
  while (i < j) {
    k = (i + j) >> 1;
    assert(i <= k && k < j);
    if (u[k] == x) return;	
    if (u[k] < x) {
      j = k;
    } else {
      i = k+1;
    }
  }

  assert(i == j && 0 <= i && i <= n && 
	 (i == n || x < u[i]) && 
	 (i == 0 || u[i-1] < x));

  // TBD
  
}


/*
 * Add a[0 ... n-1] to index vector v
 * - v must be sorted
 */
static void add_to_vector(int32_t **v, int32_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    insert_elem(v, a[i]);
  }
}

/*
 * Add v[0...n-1] to all_evars or all_uvars (remove duplicates)
 */
void ef_prob_add_evars(ef_prob_t *prob, term_t *v, uint32_t n) {
  add_to_vector(&prob->all_evars, v, n);
}

void ef_prob_add_uvars(ef_prob_t *prob, term_t *v, uint32_t n) {
  add_to_vector(&prob->all_uvars, v, n);
}


/*
 * Add t as a constraint on x
 */
void ef_prob_add_condition(ef_prob_t *prob, term_t t) {
  add_index_to_vector(&prob->conditions, t);
}


/*
 * Add a forall constraint:
 * - ev = existential variables, nev = size of the ev array
 * - uv = universal variables, nuv = size of the uv array
 * - assumption = formula on uv
 * - guarantee = formula on uv and ev
 *
 * The global arrays all_evars and all_uvars are updated:
 * - all_evars := all_evars union ev
 * - all_uvars := all_uvars union uv
 */
void ef_prob_add_constraint(ef_prob_t *prob, term_t *ev, uint32_t nev, term_t *uv, uint32_t nuv,
			    term_t assumption, term_t guarantee) {
  uint32_t i;

  i = prob->num_cnstr;
  if (i == prob->cnstr_size) {
    extend_ef_prob(prob);
  }
  assert(i < prob->cnstr_size);
  prob->cnstr[i].evars = make_index_vector(ev, nev);
  prob->cnstr[i].uvars = make_index_vector(uv, nuv);
  prob->cnstr[i].assumption = assumption;
  prob->cnstr[i].guarantee = guarantee;
  prob->num_cnstr = i+1;

  ef_prob_add_evars(prob, ev, nev);
  ef_prob_add_uvars(prob, uv, nuv);
}


/*
 * Size of vectors
 */
uint32_t ef_prob_num_evars(ef_prob_t *prob) {
  return iv_len(prob->all_evars);
}

uint32_t ef_prob_num_uvars(ef_prob_t *prob) {
  return iv_len(prob->all_uvars);
}

uint32_t ef_prob_num_conditions(ef_prob_t *prob) {
  return iv_len(prob->conditions);
}

uint32_t ef_constraint_num_evars(ef_cnstr_t *cnstr) {
  return iv_len(cnstr->evars);
}

uint32_t ef_constraint_num_uvars(ef_cnstr_t *cnstr) {
  return iv_len(cnstr->uvars);
}



