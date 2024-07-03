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

/*
 * Solver for systems of linear diophantine equations
 */

#include <assert.h>
#include <stdio.h>

#include "solvers/simplex/diophantine_systems.h"
#include "terms/poly_buffer.h"
#include "utils/int_bags.h"
#include "utils/memalloc.h"
#include "utils/ptr_queues.h"


/*
 * Set TRACE to 1 to enable tracing
 */
#define TRACE 0

#if TRACE
#include <stdio.h>
#include <inttypes.h>

#include "solvers/simplex/dsolver_printer.h"
#include "utils/cputime.h"
#endif



/**********************************
 *  OPERATIONS ON COLUMN VECTORS  *
 *********************************/

/*
 * Allocate a new vector of size n for variable x
 * - negative x means constant or auxiliary column
 * - if n == 0, the default size is used
 * - the vector is initialized to 0
 */
static dcolumn_t *new_column(uint32_t n, int32_t x) {
  dcolumn_t *tmp;
  uint32_t i;

  if (n == 0) {
    n = DEF_DCOLUMN_SIZE;
  }

  if (n >= MAX_DCOLUMN_SIZE) {
    out_of_memory();
  }

  tmp = (dcolumn_t *) safe_malloc(sizeof(dcolumn_t) + n * sizeof(dcol_elem_t));
  tmp->active = -1;
  tmp->var = x;
  tmp->size = n;
  tmp->nelems = 0;
  tmp->data[0].r_idx = max_idx; // end marker
  for (i=0; i<n; i++) {
    q_init(&tmp->data[i].coeff);
  }

  return tmp;
}


/*
 * Delete column c
 */
static void delete_column(dcolumn_t *c) {
  uint32_t i, n;

  n = c->size;
  for (i=0; i<n; i++) {
    q_clear(&c->data[i].coeff);
  }

  safe_free(c);
}


/*
 * Realloc: make c 50% larger
 */
static dcolumn_t *extend_column(dcolumn_t *c) {
  uint32_t i, n;

  n = c->size + 1;
  n += n>>1;
  if (n >= MAX_DCOLUMN_SIZE) {
    out_of_memory();
  }

  c = (dcolumn_t *) safe_realloc(c, sizeof(dcolumn_t) + n * sizeof(dcol_elem_t));
  for (i=c->size; i<n; i++) {
    q_init(&c->data[i].coeff);
  }
  c->size = n;

  return c;
}



/*
 * Clear c (make it a zero column)
 */
static void clear_column(dcolumn_t *c) {
  c->nelems = 0;
  c->active = -1;
  c->data[0].r_idx = max_idx;
}


/*
 * Reset: like clear but it also frees the mpq_t objects
 * used by the column.
 */
static void reset_column(dcolumn_t *c) {
  uint32_t i, n;

  n = c->size;
  for (i=0; i<n; i++) {
    q_clear(&c->data[i].coeff);
  }
  clear_column(c);
}



/*
 * Search for an element with r_idx == i in the column
 * - return the index k of that element if it's found
 * - return -1 otherwise
 */
static int32_t find_row(dcolumn_t *c, int32_t i) {
  uint32_t l, h, k;

  l = 0;
  h = c->nelems;
  if (h == 0) return -1;

  // binary search
  for (;;) {
    k = (l + h)/2;
    assert(l <= k && k < h);
    if (k == l) break;
    if (c->data[k].r_idx > i) {
      h = k;
    } else {
      l = k;
    }
  }

  if (c->data[k].r_idx == i) {
    return k;
  } else {
    return -1;
  }
}





/*
 * ACTIVE ROW/COEFFICIENT
 */

static inline int32_t active_elem(dcolumn_t *c) {
  return c->active;
}

static inline int32_t active_row(dcolumn_t *c) {
  assert(0 <= c->active && c->active < c->nelems);
  return c->data[c->active].r_idx;
}

static inline rational_t *active_coeff(dcolumn_t *c) {
  assert(0 <= c->active && c->active < c->nelems);
  return &c->data[c->active].coeff;
}





/*
 * SUPPORT FOR BUILDING EQUATIONS.
 *
 * Equations are built by adding new elements at the end of columns or by
 * modifying the last element. This is done using the following operations.
 */

/*
 * Add coefficient c[i] := a at the end of the column and make i the active row
 * - i must be larger than all other row indices in c
 * - return the updated column
 */
static dcolumn_t *column_new_row_elem(dcolumn_t *c, rational_t *a, int32_t i) {
  uint32_t n;

  assert(c->nelems == 0 || c->data[c->nelems - 1].r_idx < i);

  n = c->nelems;
  if (n+1 == c->size) {
    c = extend_column(c);
  }
  assert(n+1 < c->size);
  // new element at index n = [a, i]
  c->active = n;
  c->data[n].r_idx = i;
  q_set(&c->data[n].coeff, a);
  // move the end marker
  n ++;
  c->data[n].r_idx = max_idx;
  c->nelems = n;

  return c;
}

/*
 * Add constant a to c[i]: create c[i] if there's no such row in the column
 * otherwise add a to c[i]
 * - c must have an active element with r_idx == i
 * - return the updated column
 */
static dcolumn_t *column_add_row_elem(dcolumn_t *c, rational_t *a, int32_t i) {
  int32_t k;

  k = c->active;
  if (k >= 0) {
    assert(active_row(c) == i);
    q_add(&c->data[k].coeff, a);
  } else {
    c = column_new_row_elem(c, a, i);
  }

  return c;
}


/*
 * Add a*b to c[i]
 * - if c has an active element then i must be the active row
 */
static dcolumn_t *column_addmul_row_elem(dcolumn_t *c, rational_t *a, rational_t *b, int32_t i) {
  int32_t k;

  k = c->active;
  if (k >= 0) {
    assert(active_row(c) == i);
    q_addmul(&c->data[k].coeff, a, b);
  } else {
    c = column_new_row_elem(c, a, i);
    k = c->active;
    assert(k >= 0 && active_row(c) == i);
    q_mul(&c->data[k].coeff, b);
  }

  return c;
}


/*
 * Multiply coeff c[i] by a where i = active row of c
 */
static void column_mul_row_elem(dcolumn_t *c, rational_t *a) {
  int32_t k;

  k = c->active;
  assert(k >= 0);
  q_mul(&c->data[k].coeff, a);
}



/*
 * Remove the active coefficient
 * - the active coefficient must be zero and must be
 *   the last element in the column
 * - this removes the last element of the column
 * - it also resets the active index to -1
 */
static void remove_zero_row_elem(dcolumn_t *c) {
  int32_t k;

  k = c->active;
  assert(k >= 0 && k == c->nelems - 1 && q_is_zero(&c->data[k].coeff));
  c->data[k].r_idx = max_idx;
  c->nelems = k;
  c->active = -1;
}



/*
 * SUPPORT FOR ROSSER'S ALGORITHM
 */

/*
 * Add coefficient 1 for row i to column c with r_ptr = k
 * - i must be larger than all other row indices in c
 * - return the updated column
 */
static dcolumn_t *column_add_unit(dcolumn_t *c, int32_t i, int32_t k) {
  uint32_t n;

  assert(c->nelems == 0 || c->data[c->nelems - 1].r_idx < i);

  n = c->nelems;
  if (n+1 == c->size) {
    c = extend_column(c);
  }
  assert(n+1 < c->size);
  c->data[n].r_idx = i;
  c->data[n].r_ptr = k;
  q_set_one(&c->data[n].coeff);

  n ++;
  c->data[n].r_idx = max_idx;
  c->nelems = n;

  return c;
}



/*
 * Store quotient of c1[i] divided by c2[i] into a
 * - i must be the active row of both c1 and c2
 */
static void column_reduce_factor(rational_t *a, dcolumn_t *c1, dcolumn_t *c2) {
  assert(active_row(c1) == active_row(c2));
  q_set(a, active_coeff(c1));
  q_normalize(active_coeff(c2));
  q_integer_div(a, active_coeff(c2));

#if 0
  printf("---> column_reduce_factor: (row = %"PRIu32")\n", active_row(c1));
  printf("   act[c1] = ");
  q_print(stdout, active_coeff(c1));
  printf("\n");
  printf("   act[c2] = ");
  q_print(stdout, active_coeff(c2));
  printf("\n");
  printf("   f = ");
  q_print(stdout, a);
  printf("\n");
#endif

}



/*
 * ELEMENTARY COLUMN OPERATION
 */

/*
 * Negate all coefficients in column c
 */
static void negate_column(dcolumn_t *c) {
  uint32_t i, n;

  n = c->nelems;
  for (i=0; i<n; i++) {
    q_neg(&c->data[i].coeff);
  }
}



/*
 * Compute d := c1 - a * c2
 * - d must be empty
 * - a must be non-zero (and should be an integer)
 * - if c1 has an active row i and that row does not cancel out, then
 *   i is also set as active row in d
 * - d's variable is copied from c1's variable
 * - return the updated d
 */
static dcolumn_t *column_submul(dcolumn_t *d, dcolumn_t *c1, rational_t *a, dcolumn_t *c2) {
  dcol_elem_t *e1, *e2;
  uint32_t k, n;
  int32_t i1, i2, i;

  assert(d->nelems == 0 && d->size > 0 && q_is_nonzero(a));

  d->var = c1->var; // copy the variable
  d->active = -1;   // clear active element
  i = -1;
  if (c1->active >= 0) {
    i = active_row(c1); // i<0 if c1 has no active row
  }

  n = d->size - 1; // max number of elements in d before resizing is required
  k = 0;
  e1 = c1->data;
  e2 = c2->data;
  i1 = e1->r_idx;
  i2 = e2->r_idx;
  while (i1 < max_idx || i2 < max_idx) {
    // d->data[k] will be the new element in column d
    if (k == n) {
      d = extend_column(d);
      n = d->size - 1;
    }

    if (i1 == i2) {
      // d[k] is [row i1, e1->coeff - a * e2->coeff]
      d->data[k].r_idx = i1;
      q_set(&d->data[k].coeff, &e1->coeff);
      q_submul(&d->data[k].coeff, a, &e2->coeff);
      e1 ++;
      e2 ++;
      i1 = e1->r_idx;
      i2 = e2->r_idx;
      if (q_is_zero(&d->data[k].coeff)) continue;

    } else if (i1 < i2) {
      // d[k] := [row i1, e1->coeff]
      d->data[k].r_idx = i1;
      q_set(&d->data[k].coeff, &e1->coeff);
      e1 ++;
      i1 = e1->r_idx;

    } else {
      // d[k] := [row i2, - a * e2->coeff]
      d->data[k].r_idx = i2;
      q_set_neg(&d->data[k].coeff, &e2->coeff);
      q_mul(&d->data[k].coeff, a);
      e2 ++;
      i2 = e2->r_idx;
    }
    // check whether k should be the active element
    if (d->data[k].r_idx == i) {
      d->active = k;
    }
    k ++;
  }

  // add the end marker in d
  assert(k < d->size);
  d->data[k].r_idx = max_idx;
  d->nelems = k;

  return d;
}


/*
 * Special case: compute d := c1 - c2
 * - d must be empty
 * - if c1 has an active row i and that row does not cancel out, then
 *   it's also set as active row in d
 * - c1's variable is copied into d's variable
 * - return the updated d
 */
static dcolumn_t *column_sub(dcolumn_t *d, dcolumn_t *c1, dcolumn_t *c2) {
  dcol_elem_t *e1, *e2;
  uint32_t k, n;
  int32_t i1, i2, i;

  assert(d->nelems == 0 && d->size > 0);

  d->var = c1->var;
  d->active = -1;     // clear active element
  i = -1;
  if (c1->active >= 0) {
   i = active_row(c1);
  }

  n = d->size - 1; // max number of elements in d before resizing is required
  k = 0;
  e1 = c1->data;
  e2 = c2->data;
  i1 = e1->r_idx;
  i2 = e2->r_idx;
  while (i1 < max_idx || i2 < max_idx) {
    // d->data[k] will be the new element in column d
    if (k == n) {
      d = extend_column(d);
      n = d->size - 1;
    }

    if (i1 == i2) {
      // d[k] is [row i1, e1->coeff - e2->coeff]
      d->data[k].r_idx = i1;
      q_set(&d->data[k].coeff, &e1->coeff);
      q_sub(&d->data[k].coeff, &e2->coeff);
      e1 ++;
      e2 ++;
      i1 = e1->r_idx;
      i2 = e2->r_idx;
      if (q_is_zero(&d->data[k].coeff)) continue;

    } else if (i1 < i2) {
      // d[k] := [row i1, e1->coeff]
      d->data[k].r_idx = i1;
      q_set(&d->data[k].coeff, &e1->coeff);
      e1 ++;
      i1 = e1->r_idx;

    } else {
      // d[k] := [row i2, - e2->coeff]
      d->data[k].r_idx = i2;
      q_set_neg(&d->data[k].coeff, &e2->coeff);
      e2 ++;
      i2 = e2->r_idx;
    }
    // check whether k should be the active element
    if (d->data[k].r_idx == i) {
      d->active = k;
    }

    k ++;
  }

  // add the end marker in d
  assert(k < d->size);
  d->data[k].r_idx = max_idx;
  d->nelems = k;

  return d;
}




/*************************
 *   ELIMINATION VECTOR  *
 ************************/

/*
 * Initialize a vector of size n
 * - if n == 0, nothing is allocated yet
 * - the data array is allocated on the first add operation
 */
static void init_elim_vector(delim_vector_t *v, uint32_t n) {
  v->size = n;
  v->nelems = 0;
  v->data = NULL;

  if (n > 0) {
    if (n >= MAX_DELIMVECTOR_SIZE) {
      out_of_memory();
    }
    v->data = (delim_record_t *) safe_malloc(n * sizeof(delim_record_t));
  }
}


/*
 * Make the vector 50% larger or if its size is zero
 * allocate an array of default size
 */
static void extend_elim_vector(delim_vector_t *v) {
  uint32_t n;

  n = v->size;
  if (n == 0) {
    // first allocation: use the default size
    assert(v->data == NULL);
    n = DEF_DELIMVECTOR_SIZE;
  } else {
    // increase the size by 50%
    n ++;
    n <<= 1;
  }

  if (n >= MAX_DELIMVECTOR_SIZE) {
    out_of_memory();
  }

  v->data = (delim_record_t *) safe_realloc(v->data, n * sizeof(delim_record_t));
  v->size = n;
}


/*
 * Delete the vector
 */
static void delete_elim_vector(delim_vector_t *v) {
  uint32_t i, n;

  n = v->nelems;
  for (i=0; i<n; i++) {
    free_polynomial(v->data[i].poly);
  }
  safe_free(v->data);
  v->data = NULL;
}


/*
 * Empty the vector: delete all polynomials
 */
static void reset_elim_vector(delim_vector_t *v) {
  uint32_t i, n;

  n = v->nelems;
  for (i=0; i<n; i++) {
    free_polynomial(v->data[i].poly);
  }
  v->nelems = 0;
}


/*
 * Allocate an elimination record and store the pair (x, p) into it
 * - r = row source of the elimination
 * - return the record index
 */
static int32_t alloc_elim_record(delim_vector_t *v, int32_t x, polynomial_t *p, int32_t r) {
  uint32_t i;

  i = v->nelems;
  if (i == v->size) {
    extend_elim_vector(v);
  }
  assert(i < v->size);
  v->data[i].var = x;
  v->data[i].source = r;
  v->data[i].poly = p;
  v->nelems = i+1;

  return i;
}





/*****************
 *  FULL SOLVER  *
 ****************/

/*
 * Comparison order for the heap of columns (active columns)
 * - all columns in the heap should have the same active row i
 * - c1 should precede c2 in c1[i] > c2[i]
 */
static bool active_columns_compare(dcolumn_t *c1, dcolumn_t *c2) {
  assert(active_row(c1) == active_row(c2));
  return q_ge(active_coeff(c1), active_coeff(c2));
}

/*
 * Comparison function for the row heap
 * - i and j are distinct row indices (between 0 and nrows)
 * - both solver->row[i] and solver->row[j] must be non NULL
 * - return true if i should be processed before j
 *   (i.e., row i has fewer non-zero elements than row j)
 */
static bool active_rows_compare(dsolver_t *solver, int32_t i, int32_t j) {
  assert(0 <= i && i < solver->nrows && 0 <= j && j < solver->nrows &&
         solver->row[i] != NULL && solver->row[j] != NULL);
  return ibag_nelems(solver->row[i]) < ibag_nelems(solver->row[j]);
}


/*
 * Initialization: prepare empty solver
 * - n = initial rsize (if n = 0, the default size is used)
 * - m = initial vsize (if m = 0, the default size is used)
 * - p = initial csize (if p = 0, the default size is used)
 */
void init_dsolver(dsolver_t *solver, uint32_t n, uint32_t m, uint32_t p) {
  if (n == 0) n = DEF_DSOLVER_RSIZE;
  if (m == 0) m = DEF_DSOLVER_VSIZE;
  if (p == 0) p = DEF_DSOLVER_CSIZE;

  if (n >= MAX_DSOLVER_RSIZE || m >= MAX_DSOLVER_VSIZE || p >= MAX_DSOLVER_CSIZE) {
    out_of_memory();
  }

  solver->rsize = n;
  solver->vsize = m;
  solver->csize = p;
  solver->nvars = 0;
  solver->nrows = 0;
  solver->ncolumns = 0;

  solver->nsolved = 0;
  solver->main_rows = 0;
  solver->active_row = -1;
  solver->status = DSOLVER_READY;
  solver->unsat_row = -1;

  solver->all_coeffs_integer = true;

  // variable-indexed arrays
  solver->col_idx = (int32_t *) safe_malloc(m * sizeof(int32_t));
  solver->sol_row = (int32_t *) safe_malloc(m * sizeof(int32_t));

  // rows
  solver->row_id = (int32_t *) safe_malloc(n * sizeof(int32_t));
  solver->row = (int32_t **) safe_malloc(n * sizeof(int32_t *));

  // columns
  solver->column = (dcolumn_t **) safe_malloc(p * sizeof(dcolumn_t *));
  solver->constant_column = new_column(0, -1);
  solver->aux_column = new_column(0, -1);

  // auxiliary structures
  init_elim_vector(&solver->elim, 0);
  solver->solved_columns = NULL;
  init_ptr_heap(&solver->active_columns, 0, (ptr_heap_cmp_fun_t) active_columns_compare);
  init_generic_heap(&solver->rows_to_process, 0, 0, (heap_cmp_fun_t) active_rows_compare, solver);

  q_init(&solver->reduce_factor);
  q_init(&solver->lcm);
  q_init(&solver->gcd);
  init_ivector(&solver->aux_vector, DEF_DSOLVER_AUXSIZE);

  // solution arrays are not allocated yet
  solver->base_sol = NULL;
  solver->gen_sol = NULL;
  solver->param_id = NULL;
  solver->num_params = 0;

  // explanation objects are not allocated yet
  solver->aux_buffer2 = NULL;
  solver->aux_buffer = NULL;
  solver->aux_heap = NULL;
}



/*
 * Empty the heap of active columns and delete them
 */
static void flush_column_heap(ptr_heap_t *heap) {
  dcolumn_t *c;

  while (! ptr_heap_is_empty(heap)) {
    c = ptr_heap_get_elem(heap);
    delete_column(c);
  }
}



/*
 * Reset to the empty solver
 * - delete all columns in the matrix
 * - reset the constant and aux columns to empty
 * - empty the heaps and elim vector
 * - delete all arrays created at solving time
 */
void reset_dsolver(dsolver_t *solver) {
  uint32_t i, n;

  // delete the rows
  n = solver->nrows;
  for (i=0; i<n; i++) {
    ibag_delete(solver->row[i]);
  }

  // delete all columns in the matrix
  n = solver->ncolumns;
  for (i=0; i<n; i++) {
    if (solver->column[i] != NULL) {
      delete_column(solver->column[i]);
    }
  }

  // delete the solved_columns vector
  n = solver->nsolved;
  for (i=0; i<n; i++) {
    delete_column(solver->solved_columns[i]);
  }
  safe_free(solver->solved_columns);
  solver->solved_columns = NULL;

  reset_column(solver->constant_column);
  reset_column(solver->aux_column);

  // empty the heaps and elim vector
  reset_elim_vector(&solver->elim);
  flush_column_heap(&solver->active_columns);
  reset_generic_heap(&solver->rows_to_process);

  q_clear(&solver->reduce_factor);
  q_clear(&solver->lcm);
  q_clear(&solver->gcd);
  ivector_reset(&solver->aux_vector);

  // delete base_sol if it exists
  if (solver->base_sol != NULL) {
    n = solver->nvars;
    for (i=0; i<n; i++) {
      q_clear(solver->base_sol + i);
    }
    safe_free(solver->base_sol);
    solver->base_sol = NULL;
  }

  // delete gen_sol if it exists
  if (solver->gen_sol != NULL) {
    n = solver->nvars;
    for (i=0; i<n; i++) {
      if (solver->gen_sol[i] != NULL) {
        free_polynomial(solver->gen_sol[i]);
      }
    }
    safe_free(solver->gen_sol);
    solver->gen_sol = NULL;
  }

  safe_free(solver->param_id);
  solver->param_id = NULL;

  // reset aux buffers and heap if they exist
  if (solver->aux_buffer2 != NULL) {
    reset_poly_buffer(solver->aux_buffer2);
  }

  if (solver->aux_buffer != NULL) {
    reset_poly_buffer(solver->aux_buffer);
  }

  if (solver->aux_heap != NULL) {
    reset_int_heap2(solver->aux_heap);
  }


  // reset everything to the empty solver
  solver->nvars = 0;
  solver->nrows = 0;
  solver->ncolumns = 0;

  solver->nsolved = 0;
  solver->main_rows = 0;
  solver->active_row = -1;
  solver->status = DSOLVER_READY;
  solver->unsat_row = -1;

}



/*
 * Delete solver
 */
void delete_dsolver(dsolver_t *solver) {
  uint32_t i, n;

  // variable arrays
  safe_free(solver->col_idx);
  safe_free(solver->sol_row);

  // rows
  safe_free(solver->row_id);
  n = solver->nrows;
  for (i=0; i<n; i++) {
    ibag_delete(solver->row[i]);
  }
  safe_free(solver->row);

  // columns in the matrix
  n = solver->ncolumns;
  for (i=0; i<n; i++) {
    if (solver->column[i] != NULL) {
      delete_column(solver->column[i]);
    }
  }
  safe_free(solver->column);

  // solved columns if any
  n = solver->nsolved;
  for (i=0; i<n; i++) {
    delete_column(solver->solved_columns[i]);
  }

  safe_free(solver->solved_columns);
  delete_column(solver->constant_column);
  delete_column(solver->aux_column);

  delete_elim_vector(&solver->elim);
  delete_ptr_heap(&solver->active_columns);
  delete_generic_heap(&solver->rows_to_process);

  q_clear(&solver->reduce_factor);
  q_clear(&solver->lcm);
  q_clear(&solver->gcd);
  delete_ivector(&solver->aux_vector);


  // delete base_sol if it exists
  if (solver->base_sol != NULL) {
    n = solver->nvars;
    for (i=0; i<n; i++) {
      q_clear(solver->base_sol + i);
    }
    safe_free(solver->base_sol);
    solver->base_sol = NULL;
  }

  // delete gen_sol if it exists
  if (solver->gen_sol != NULL) {
    n = solver->nvars;
    for (i=0; i<n; i++) {
      if (solver->gen_sol[i] != NULL) {
        free_polynomial(solver->gen_sol[i]);
      }
    }
    safe_free(solver->gen_sol);
    solver->gen_sol = NULL;
  }

  safe_free(solver->param_id);
  solver->param_id = NULL;

  // delete aux buffers and heap if they exist
  if (solver->aux_buffer2 != NULL) {
    delete_poly_buffer(solver->aux_buffer2);
    safe_free(solver->aux_buffer2);
    solver->aux_buffer2 = NULL;
  }

  if (solver->aux_buffer != NULL) {
    delete_poly_buffer(solver->aux_buffer);
    safe_free(solver->aux_buffer);
    solver->aux_buffer = NULL;
  }

  if (solver->aux_heap != NULL) {
    delete_int_heap2(solver->aux_heap);
    safe_free(solver->aux_heap);
    solver->aux_heap = NULL;
  }


  solver->col_idx = NULL;
  solver->sol_row = NULL;
  solver->row_id = NULL;
  solver->row = NULL;
  solver->column = NULL;
  solver->constant_column = NULL;
  solver->aux_column = NULL;
  solver->solved_columns = NULL;
}




/*****************************************
 *   ADDITION OF ROWS/COLUMNS/VARIABLES  *
 ****************************************/

/*
 * Increase row size by 50%
 */
static void dsolver_increase_row_size(dsolver_t *solver) {
  uint32_t n;

  n = solver->rsize + 1;
  n += n >> 1;
  if (n >= MAX_DSOLVER_RSIZE) {
    out_of_memory();
  }

  solver->rsize = n;
  solver->row_id = (int32_t *) safe_realloc(solver->row_id, n * sizeof(int32_t));
  solver->row = (int32_t **) safe_realloc(solver->row, n * sizeof(int32_t *));
}


/*
 * Increase csize by 50& and make columns array larger
 */
static void dsolver_increase_column_size(dsolver_t *solver) {
  uint32_t n;

  n = solver->csize + 1;
  n += n>>1;
  if (n >= MAX_DSOLVER_CSIZE) {
    out_of_memory();
  }

  solver->csize = n;
  solver->column = (dcolumn_t **) safe_realloc(solver->column, n * sizeof(dcolumn_t *));
}


/*
 * Increase the number of variables to n (do nothing if nvars >= n already)
 * - increase vsize and extend the arrays col_idx and sol_row if needed
 * - initialize col_idx[x] and sol_row[x] to -1 for all new variable x
 */
static void dsolver_set_nvars(dsolver_t *solver, uint32_t n) {
  uint32_t i, vsize;

  if (n > solver->nvars) {
    vsize = solver->vsize;
    if (vsize < n) {
      // increase vsize to old vsize + 50% or n, whichever is larger
      vsize += vsize >> 1;
      if (vsize < n) {
        vsize = n;
      }

      if (vsize >= MAX_DSOLVER_VSIZE) {
        out_of_memory();
      }

      solver->col_idx = (int32_t *) safe_realloc(solver->col_idx, vsize * sizeof(int32_t));
      solver->sol_row = (int32_t *) safe_realloc(solver->sol_row, vsize * sizeof(int32_t));
      solver->vsize = vsize;
    }

    // initialize col_idx and sol_row for the new variables
    for (i = solver->nvars; i<n; i++) {
      solver->col_idx[i] = -1;
      solver->sol_row[i] = -1;
    }
    solver->nvars = n;
  }
}


/*
 * Allocate and initialize a new row (initially empty)
 * - set row_id to id
 * - return its index
 */
static uint32_t dsolver_alloc_row(dsolver_t *solver, int32_t id) {
  uint32_t i;

  i = solver->nrows;
  if (i == solver->rsize) {
    dsolver_increase_row_size(solver);
  }
  assert(i < solver->rsize);

  solver->row_id[i] = id;
  solver->row[i] = NULL; // initial index array
  solver->nrows = i+1;

  return i;
}


/*
 * ROW ADDITION
 */

/*
 * Row-addition starts with a call to open and ends with a call to close.
 * Row elements are added using add_mono, add_constant, addmul_constant.
 * The following invariants are maintained:
 * - solver->active_row = index of the row being constructed
 * - solver->aux_vector = index of all columns occurring in the active row
 * - if i occurs in aux_vector then solver->column[i] has an active element
 *   and that element is (a, k) where k = solver->active_row.
 * - if all_coeffs_integer is true then all the coefficients in the new row
 *   are integers (not counting the constant).
 *
 * The row is simplified and checked for consistency in close. If the row
 * is inconsistent, the solver status and unsat_row are updated. For testing,
 * we allow rows to be added even though the solver is already in an unsat
 * state (i.e., either GCD_UNSAT or TRIV_UNSAT).
 */

/*
 * Prepare for a new equation (i.e., a new row)
 * - id = the external row id
 * - return the internal index for that row
 * The new row is initially empty (constant = 0, no monomials).
 */
int32_t dsolver_row_open(dsolver_t *solver, int32_t id) {
  uint32_t i;

  assert(solver->active_row < 0 && solver->status < DSOLVER_SIMPLIFIED);

  i = dsolver_alloc_row(solver, id);
  solver->active_row = i;
  solver->all_coeffs_integer = true;
  assert(solver->aux_vector.size == 0);

  return i;
}


/*
 * Add monomial a.x to the current row (i.e., the one initialized
 * by the previous call to row_open).
 * - a = coefficient (can be rational)
 * - x = variable (x must be positive)
 * If the current row contains a monomial b.x with the same variable,
 * then it's replaced by (a+b).x
 */
void dsolver_row_add_mono(dsolver_t *solver, rational_t *a, int32_t x) {
  dcolumn_t *c;
  int32_t c_idx, i;

  i = solver->active_row;
  assert(i >= 0 && i == solver->nrows - 1 && x > 0 && solver->status < DSOLVER_SIMPLIFIED);

  if (solver->all_coeffs_integer) {
    solver->all_coeffs_integer = q_is_integer(a);
  }

  dsolver_set_nvars(solver, x+1);
  c_idx = solver->col_idx[x];
  if (c_idx < 0) {
    // create a column for variable x and add c[i] := a as coefficient in c
    c = new_column(0, x);
    c = column_new_row_elem(c, a, i);

    // store c as a new column
    c_idx = solver->ncolumns;
    if (c_idx == solver->csize) {
      dsolver_increase_column_size(solver);
    }
    assert(c_idx < solver->csize);
    // store c at index c_idx
    solver->column[c_idx] = c;
    solver->col_idx[x] = c_idx;
    solver->ncolumns = c_idx+1;

    // add c_idx in aux_vector
    ivector_push(&solver->aux_vector, c_idx);

  } else {
    assert(c_idx < solver->ncolumns);
    c = solver->column[c_idx];
    assert(c->var == x);
    if (active_elem(c) < 0) {
      ivector_push(&solver->aux_vector, c_idx);
    }
    solver->column[c_idx] = column_add_row_elem(c, a, i);;
  }

}


/*
 * Add constant a to the current row constant
 */
void dsolver_row_add_constant(dsolver_t *solver, rational_t *a) {
  int32_t i;

  i = solver->active_row;
  assert(i >= 0 && i == solver->nrows - 1 && solver->status < DSOLVER_SIMPLIFIED);
  solver->constant_column = column_add_row_elem(solver->constant_column, a, i);
}

/*
 * Add constant a * b to the current row constant
 */
void dsolver_row_addmul_constant(dsolver_t *solver, rational_t *a, rational_t *b) {
  int32_t i;

  i = solver->active_row;
  assert(i >= 0 && i == solver->nrows - 1 && solver->status < DSOLVER_SIMPLIFIED);
  solver->constant_column = column_addmul_row_elem(solver->constant_column, a, b, i);

}




/*
 * ROW NORMALIZATION
 */

/*
 * Remove the zero coefficients in the new row
 */
static void dsolver_remove_zeros(dsolver_t *solver) {
  ivector_t *v;
  dcolumn_t *c;
  uint32_t i, j, n;
  int32_t c_idx;

  assert(solver->active_row >= 0 && solver->active_row == solver->nrows - 1);

  v = &solver->aux_vector;
  n = v->size;
  j = 0;
  for (i=0; i<n; i++) {
    c_idx = v->data[i];
    c = solver->column[c_idx];
    if (q_is_zero(active_coeff(c))) {
      remove_zero_row_elem(c);
    } else {
      // keep c_idx in vector v
      v->data[j] = c_idx;
      j ++;
    }
  }
  ivector_shrink(v, j);

  c = solver->constant_column;
  if (active_elem(c) >= 0 && q_is_zero(active_coeff(c))) {
    remove_zero_row_elem(c);
  }
}


/*
 * Scale the new row: multiply all coefficients by d
 */
static void dsolver_scale_new_row(dsolver_t *solver, rational_t *d) {
  ivector_t *v;
  dcolumn_t *c;
  uint32_t i, n;
  int32_t c_idx;

  assert(solver->active_row >= 0 && solver->active_row == solver->nrows - 1);

  v = &solver->aux_vector;
  n = v->size;
  for (i=0; i<n; i++) {
    c_idx = v->data[i];
    c = solver->column[c_idx];
    column_mul_row_elem(c, d);
  }

  c = solver->constant_column;
  if (active_elem(c) >= 0) {
    column_mul_row_elem(c, d);
  }
}


/*
 * Add the active row to the matrix. If i is the active row index,
 * then row[i] is initialized here by copying the aux_vector content.
 * - set the r_ptr indices in each column's active element
 * - reset the active pointers
 */
static void dsolver_store_new_row(dsolver_t *solver) {
  ivector_t *v;
  dcolumn_t *c;
  uint32_t i, n;
  int32_t c_idx, r_idx, k;

  r_idx = solver->active_row;
  assert(r_idx >= 0 && r_idx == solver->nrows - 1);

  v = &solver->aux_vector;
  n = v->size;
  for (i=0; i<n; i++) {
    c_idx = v->data[i];
    c = solver->column[c_idx];
    assert(active_row(c) == r_idx && q_is_nonzero(active_coeff(c)));

    // add the dependencies: row[r_idx][j] = c_idx and c->data[k].r_ptr = j
    k = c->active;
    c->data[k].r_ptr = ibag_add(solver->row + r_idx, c_idx);

    c->active = -1;
  }

  c = solver->constant_column;
  if (active_elem(c) >= 0) {
    assert(active_row(c) == solver->active_row && q_is_nonzero(active_coeff(c)));
    c->active = -1;
  }

  ivector_reset(v);
  solver->active_row = -1;
}


/*
 * Normalize the new row:
 * - the row is a[0]/b[0] x_0 + ... + a[n]/b[n] x_n + b = 0
 * - a[0] ... a[n] must be non-zero
 * - compute L = lcm(b[0], ..., b[n]) and D = gcd(a[0],...,a[n])
 * - then multiply everything by L/D, including b
 */
static void dsolver_normalize_new_row(dsolver_t *solver) {
  ivector_t *v;
  dcolumn_t *c;
  rational_t *l, *d, *aux;
  uint32_t i, n;
  int32_t c_idx;

  assert(solver->active_row >= 0 && solver->status < DSOLVER_SIMPLIFIED);

  // v = all columns present in the new row
  v = &solver->aux_vector;
  n = v->size;
  assert(n > 0);

  // first column
  c_idx = v->data[0];
  c = solver->column[c_idx];
  assert(q_is_nonzero(active_coeff(c)));

  l = &solver->lcm;
  d = &solver->gcd;
  aux = &solver->reduce_factor;

  if (solver->all_coeffs_integer) {
    // L = 1, D = gcd of numerators
    q_set_one(l);
    q_get_num(d, active_coeff(c));
    for (i=1; i<n; i++) {
      c_idx = v->data[i];
      c = solver->column[c_idx];
      assert(q_is_nonzero(active_coeff(c)));
      q_get_num(aux, active_coeff(c));
      q_gcd(d, aux);
    }

  } else {

    q_get_den(l, active_coeff(c));
    q_get_num(d, active_coeff(c));
    for (i=1; i<n; i++) {
      c_idx = v->data[i];
      c = solver->column[c_idx];
      assert(q_is_nonzero(active_coeff(c)));
      q_get_den(aux, active_coeff(c));
      q_lcm(l, aux);
      q_get_num(aux, active_coeff(c));
      q_gcd(d, aux);
    }
  }

  // multiply the whole row by (L/D)
  // both l and d are positive
  q_div(l, d);
  if (! q_is_one(l)) {
    dsolver_scale_new_row(solver, l);
  }
}




/*
 * Close:
 * - normalize then add the new row
 * - apply the GCD test
 */
bool dsolver_row_close(dsolver_t *solver) {
  dcolumn_t *c;
  bool feasible;

#if 0
  printf("---> dsolver_row_close:\n");
  dsolver_print_active_row(stdout, solver);
  if (solver->all_coeffs_integer) {
    printf("  integer row\n");
  }
#endif

  feasible = true;
  dsolver_remove_zeros(solver);

#if 0
  printf("  after removing zeros:\n");
  dsolver_print_active_row(stdout, solver);
#endif

  if (solver->aux_vector.size > 0) {
    // non-zero row
    dsolver_normalize_new_row(solver);

#if 0
    printf("  after normalization:\n");
    dsolver_print_active_row(stdout, solver);
#endif

    c = solver->constant_column;
    if (active_elem(c) >= 0 && !q_is_integer(active_coeff(c))) {
      // GCD test fails
      feasible = false;
      solver->status = DSOLVER_GCD_UNSAT;
      solver->unsat_row = solver->active_row;
#if 0
      printf("  infeasible by GCD test\n");
#endif
    }
  } else {
    c = solver->constant_column;
    if (active_elem(c) >= 0) {
      assert(q_is_nonzero(active_coeff(c)));
      solver->status = DSOLVER_TRIV_UNSAT;
      solver->unsat_row = solver->active_row;
      feasible = false;
#if 0
      printf("  infeasible\n");
#endif
    }
  }

  dsolver_store_new_row(solver);

  return feasible;
}








/**********************************************
 *   SIMPLIFICATION: ELIMINATE ROWS/COLUMNS   *
 *********************************************/

/*
 * During simplification, we clear individual coefficients in a column.
 * After all simplifications are done, we cleanup the columns by removing
 * the zero elements.
 *
 * HACK: during simplification, we use c->active as a counter to store
 * the number of non-zero coefficient in column c.
 */

/*
 * Remove all zero elements in c and reset c->active to -1
 */
static void remove_cleared_elements(dcolumn_t *c) {
  dcol_elem_t *e;
  uint32_t j, k, n;

  n = c->nelems;
  if (c->active < c->nelems) {
    // some elements have been cleared
    e = c->data;
    k = 0;
    for (j=0; j<n; j++) {
      if (q_is_nonzero(&e[j].coeff)) {
        if (k < j) {
          // copy c->data[j] into c->data[k]
          q_copy_and_clear(&e[k].coeff, &e[j].coeff);
          e[k].r_idx = e[j].r_idx;
          e[k].r_ptr = e[j].r_ptr;
        }
        k ++;
      }
    }

    // add the end marker
    e[k].r_idx = max_idx;
    c->nelems = k;
  }

  c->active = -1;
}



/*
 * Check whether column c can be eliminated, i.e.,
 * - c contains a unique non-zero element c[i] equal to +1 or -1
 */
static bool column_can_be_eliminated(dcolumn_t *c) {
  uint32_t i;

  assert(c->active >= 0 && c->active <= c->nelems);

  if (c->active == 1) {
    i = 0;
    while (q_is_zero(&c->data[i].coeff)) {
      i ++;
      assert(i < c->nelems);
    }
    return (q_is_one(&c->data[i].coeff) || q_is_minus_one(&c->data[i].coeff));
  }

  return false;
}



/*
 * Eliminate column c and a row r
 * - add to the queue all columns that can be eliminated as a result of
 *   removing row r.
 * - build an elimination record [x := p] for the eliminated variable x == c->var
 */
static void eliminate_column(dsolver_t *solver, dcolumn_t *c, ptr_queue_t *queue) {
  dcolumn_t *d;
  int32_t *row;
  polynomial_t *p;
  bool negate;
  int32_t r, j, k;
  uint32_t i, n, t;

  assert(c->active == 0 || c->active == 1);

  /*
   * When c was added to the queue, it was a singleton column with a
   * coefficient equal to +1 or -1 in a row r.  Row r may have been
   * eliminated via another column than c, so c may now be an empty
   * column. If c is empty, we don't eliminate it because c->var occurs
   * in an elimination record.
   */
  if (c->active == 1) {
    /*
     * Find the non-zero element in column c
     */
    j = 0;
    while (q_is_zero(&c->data[j].coeff)) {
      j ++;
      assert(j < c->nelems);
    }

    /*
     * c->data[j] = unique non-zero element in c
     * and c->data[j].coeff is +1 or -1
     */
    negate = q_is_one(&c->data[j].coeff);
    assert(negate || q_is_minus_one(&c->data[j].coeff));

    r = c->data[j].r_idx; // row to eliminate
    j = c->data[j].r_ptr; // row[r][j] = column index for c
    row = solver->row[r];
    assert(row != NULL && 0 <= j && j < ibag_size(row));

    /*
     * At this point we have
     * - c->var = variable to eliminate
     * - r = index of the row to eliminate
     * - row = array of all column indices where row r occurs
     */
    n = ibag_nelems(row);

    /*
     * Check the constant for row r
     * Allocate a polynomial of the right size
     */
    d = solver->constant_column;
    k = find_row(d, r);
    if (k >= 0) {
      assert(q_is_nonzero(&d->data[k].coeff) && d->active > 0);
      // copy the constant in p and remove it from the constant column
      p = alloc_raw_polynomial(n);
      p->mono[0].var = const_idx;
      q_copy_and_clear(&p->mono[0].coeff, &d->data[k].coeff);
      d->active --;
      t = 1;
    } else {
      // no constant part in the p
      p = alloc_raw_polynomial(n - 1); // to keep the substitution
      t = 0;
    }

    // scan the row, copy its content into p->mono[t ... p->nterms - 1]
    n = ibag_size(row);
    for (i=0; i<n; i++) {
      if (i != j) {
        k = row[i];
        if (k >= 0) {
          d = solver->column[k];
          assert(d != NULL && d != c);
          k = find_row(d, r); // d->data[k] = element for row r in column d
          assert(k >= 0 && q_is_nonzero(&d->data[k].coeff) && d->active > 0);

          // copy the coefficient in p and clear it in d
          p->mono[t].var = d->var;
          q_copy_and_clear(&p->mono[t].coeff, &d->data[k].coeff);
          t ++;

          // check whether d can be eliminated, if so add it to the queue
          d->active --;
          if (column_can_be_eliminated(d)) {
            ptr_queue_push(queue, d);
          }
        }
      }
    }

    /*
     * Sort p and negate its coefficients if needed
     */
    assert(t == p->nterms);
    sort_monarray(p->mono, p->nterms);
    if (negate) {
      in_place_negate_monarray(p->mono);
    }

    /*
     * Store the substitution x := p into a new elimination record
     * - record that the substitution is equivalent to original row r
     * - keep index of the elimination record in sol_row[x]
     */
    j = c->var; // that's x
    k = alloc_elim_record(&solver->elim, j, p, r);
    solver->sol_row[j] = k;

    /*
     * Delete the row and the column
     */
    ibag_delete(row);
    solver->row[r] = NULL;

    j = solver->col_idx[j];
    assert(solver->column[j] == c);
    delete_column(c);
    solver->column[j] = NULL;
  }

}


/*
 * Full simplification:
 * - solver->status must be READY
 * - remove rows/columns that contain a coefficient equal to +/-1
 *
 * After simplification:
 * - nrows, nvars, ncolumns are unchanged
 * - if column i is removed then solver->column[i] is replaced by NULL
 * - if row j is removed then solver->row[j] is replaced by NULL
 * - there may be other rows with solver->row[j] = NULL (if the user adds
 *   empty rows to the matrix)
 * - an elim record is constructed for each eliminated variable x (i.e.,
 *   eliminated column) and solver->sol_row[x] = the index of that
 *   elimination record.
 */
void dsolver_simplify(dsolver_t *solver) {
  ptr_queue_t queue; // columns to eliminate
  dcolumn_t *c;
  uint32_t i, n;

  assert(solver->status == DSOLVER_READY);

  init_ptr_queue(&queue, 0);

  /*
   * Collect the columns to eliminate
   */
  n = solver->ncolumns;
  for (i=0; i<n; i++) {
    c = solver->column[i];
    c->active = c->nelems; // initialize c->active as counter
    if (column_can_be_eliminated(c)) {
      ptr_queue_push(&queue, c);
    }
  }

  c = solver->constant_column;
  c->active = c->nelems; // use c->active as a counter


  /*
   * process the queue
   */
  while (! ptr_queue_is_empty(&queue)) {
    c = ptr_queue_pop(&queue);
    eliminate_column(solver, c, &queue);
  }


  /*
   * Cleanup the columns that are left.
   * NOTE: some columns may be zero but we keep them.
   * They represent unconstrained variables.
   */
  for (i=0; i<n; i++) {
    c = solver->column[i];
    if (c != NULL) {
      remove_cleared_elements(c);
    }
  }

  /*
   * Cleanup the constant column
   */
  remove_cleared_elements(solver->constant_column);

  delete_ptr_queue(&queue);

  solver->status = DSOLVER_SIMPLIFIED;
}





/************************
 *  ROSSER'S ALGORITHM  *
 ***********************/

/*
 * Column cost = size of its largest element
 */
static uint32_t column_cost(dcolumn_t *c) {
  uint32_t i, n, cost, k;

  cost = 0;
  n = c->nelems;
  for (i=0; i<n; i++) {
    k = q_size(&c->data[i].coeff);
    if (k > cost) {
      cost = k;
    }
  }

  return cost;
}


/*
 * Update the size estimate:
 * - this is used as a heuristic to stop the algorithms if the 
 *   coefficients become too big
 */
static void update_size(dsolver_t *solver, dcolumn_t *c) {
  uint32_t s;

  s = column_cost(c);
  if (s > solver->max_coeff_size) {
    solver->max_coeff_size = s;
  }
  s = c->nelems;
  if (s > solver->max_column_size) {
    solver->max_column_size = s;
  }
}


/*
 * Initialize:
 * - the solver status must be READY or SIMPLIFIED
 * - the indices of non-empty rows are added to the rows_to_process heap
 * - the solved_columns vector is allocated
 * - adjoin the identity matrix to the columns (this adds m new rows
 *   if m is the number of non-null columns)
 */
static void dsolver_rosser_init(dsolver_t *solver) {
  int32_t *row;
  dcolumn_t *c;
  uint32_t i, n;
  int32_t k, k_ptr;

  assert(generic_heap_is_empty(&solver->rows_to_process));

  n = solver->nrows;
  
  // initialize the counters (we must do this before adding the identity matrix)
  solver->main_rows = n;
  solver->nsolved = 0;

  // collect the rows to process
  for (i=0; i<n; i++) {
    row = solver->row[i];
    /*
     * Invariant we expect here: if the row is NULL then it does not
     * occur in the constant vector. Otherwise, the solver status should
     * be trivially unsat.
     */
    assert(row != NULL || find_row(solver->constant_column, i) < 0);
    if (row != NULL) {
      generic_heap_add(&solver->rows_to_process, i);
    }
  }

  // allocate the solved_columns vector (size = number of rows to process)
  n = generic_heap_nelems(&solver->rows_to_process);
  solver->solved_columns = (dcolumn_t **) safe_malloc(n * sizeof(dcolumn_t *));

  // adjoin the identity matrix
  n = solver->ncolumns;
  for (i=0; i<n; i++) {
    c = solver->column[i];
    if (c != NULL) {
      // start a new row
      k = dsolver_alloc_row(solver, -1);   // use -1 as row_id
      k_ptr = ibag_add(solver->row + k, i);

      // record that row k is where variable x is solved (where x = c->var)
      assert(1 <= c->var && c->var < solver->nvars);
      solver->sol_row[c->var] = k;

      // add the unit for row k in column c
      solver->column[i] = column_add_unit(c, k, k_ptr);
    }
  }
}


/*
 * Prepare column c for activation
 * - r = index of the row being processed
 * Effect:
 * - remove c from the column vector
 * - detach c from all row vectors except r
 * - remove all rows of c except r from the heap of rows to process
 *   and copy them into aux_vector
 * - activate the element corresponding to row r in c
 * - negate c if that coefficient is negative
 */
static void dsolver_activate_column(dsolver_t *solver, dcolumn_t *c, int32_t r) {
  uint32_t i, n;
  int32_t k, k_ptr;

  assert(c->active < 0);

  // remove c from solver->columns
  k = solver->col_idx[c->var];
  assert(0 <= k && k < solver->ncolumns && solver->column[k] == c);
  solver->column[k] = NULL;

  // detach c from the row vectors
  n = c->nelems;
  for (i=0; i<n; i++) {
    assert(q_is_nonzero(&c->data[i].coeff));
    k = c->data[i].r_idx;
    if (k == r) {
      c->active = i;
    } else {
      // detach row c form row k
      k_ptr = c->data[i].r_ptr;
      assert(0 <= k && k < solver->nrows);
      ibag_clear_elem(solver->row[k], k_ptr);
      // remove k from the rows to process
      if (generic_heap_member(&solver->rows_to_process, k)) {
        generic_heap_remove(&solver->rows_to_process, k);
        ivector_push(&solver->aux_vector, k);
      }
    }
  }

  if (q_is_neg(active_coeff(c))) {
    negate_column(c);
  }

  assert(active_row(c) == r && q_is_pos(active_coeff(c)));
}


/*
 * Put back all rows of aux_vector into the rows-to-process heap
 */
static void dsolver_restore_rows_to_process(dsolver_t *solver) {
  ivector_t *v;
  uint32_t i, n;

  v = &solver->aux_vector;
  n = v->size;
  for (i=0; i<n; i++) {
    generic_heap_add(&solver->rows_to_process, v->data[i]);
  }
  ivector_reset(v);
}


/*
 * Deactivate column c:
 * - attach it to the row vectors
 * - put it back into solver->columns
 * - update the size estimate
 */
static void dsolver_deactivate_column(dsolver_t *solver, dcolumn_t *c) {
  uint32_t i, n;
  int32_t k, c_idx;

  update_size(solver, c);

  c_idx = solver->col_idx[c->var];
  assert(0 <= c_idx && c_idx < solver->ncolumns && solver->column[c_idx] == NULL);
  solver->column[c_idx] = c;

  n = c->nelems;
  for (i=0; i<n; i++) {
    assert(q_is_nonzero(&c->data[i].coeff));
    k = c->data[i].r_idx;
    assert(0 <= k && k < solver->nrows);
    c->data[i].r_ptr = ibag_add(solver->row + k, c_idx);
  }
}


/*
 * Empty the heap of active columns after interrupt:
 * - put back all the columns into the columns vector
 */
static void flush_active_columns(dsolver_t *solver) {
  dcolumn_t *c;

  for (;;) {
    c = ptr_heap_get_elem(&solver->active_columns);
    if (c == NULL) break;
    dsolver_deactivate_column(solver, c);
  }
}


/*
 * Heuristic to stop reduce_columns
 * - stop if either dsolver_stop_search was called
 *   or the problem looks too expensive
 * - side effect: sets status to DSOLVER_UNSOLVED
 */
static bool dsolver_should_stop(dsolver_t *solver) {
  uint64_t tmp;

  switch (solver->status) {
  case DSOLVER_INTERRUPTED:
    // dsolver_stop_search was called
    return true;

  case DSOLVER_SEARCHING:
    // to estimate the cost, we use max_coeff_size and max_column_size
    tmp = (uint64_t) solver->max_coeff_size * solver->max_column_size;
    if (tmp > (uint64_t) 64000) {
#if 0
      printf("stopped dsolver: coeff size = %"PRIu32", column size = %"PRIu32", reduce_ops = %"PRIu32"\n",
	     solver->max_coeff_size, solver->max_column_size, solver->num_reduce_ops);
      fflush(stdout);
#endif
      solver->status = DSOLVER_UNSOLVED;
      return true;
    }

#if 0
    if ((solver->num_reduce_ops & 0x3FFF) == 0) {
      printf("dsolver: nrows = %"PRIu32", ncolumns = %"PRIu32", coeff size = %"PRIu32", column size = %"PRIu32", reduce_ops = %"PRIu32"\n",
	     solver->nrows, solver->ncolumns, solver->max_coeff_size, solver->max_column_size, solver->num_reduce_ops);
      fflush(stdout);
    }
#endif
    // fall-through intended

  default:
    return false;
  }
}

/*
 * Reduce the columns in active_columns until only one is left
 * - r = index of the active row
 * - active_columns must be non-empty
 * - reduce the constant column using the left column
 * - store that column as the next solved column
 */
static void dsolver_reduce_columns(dsolver_t *solver, int32_t r) {
  ptr_heap_t *heap;
  dcolumn_t *c1, *c2, *aux;
  rational_t *f;
  int32_t k;

  aux = solver->aux_column;
  f = &solver->reduce_factor;
  heap = &solver->active_columns;

  c1 = ptr_heap_get_min(heap);
  assert(active_row(c1) == r);

  while (! ptr_heap_is_empty(heap)) {
    /*
     * NOTE: it helps a lot to reduce the constant vector inside this loop
     * to prevent the constant coefficient from blowing up.
     */
    c2 = solver->constant_column;
    k = find_row(c2, r);
    if (k >= 0) {
      q_set(f, &c2->data[k].coeff);
      q_normalize(active_coeff(c1));
      q_integer_div(f, active_coeff(c1));
      if (q_is_nonzero(f)) {
        if (q_is_one(f)) {
          aux = column_sub(aux, c2, c1);
        } else {
          aux = column_submul(aux, c2, f, c1);
        }
        solver->constant_column = aux;
        aux = c2;
        clear_column(aux);
      }
    }

    solver->num_reduce_ops ++;

    c2 = ptr_heap_get_min(heap);
    assert(active_row(c2) == r);
    column_reduce_factor(f, c1, c2);
    assert(q_is_pos(f));

    // aux := c1 - f * c2
    if (q_is_one(f)) {
      aux = column_sub(aux, c1, c2);
    } else {
      aux = column_submul(aux, c1, f, c2);
    }

    if (aux->active < 0) {
      // coefficient aux[r] is zero
      dsolver_deactivate_column(solver, aux);
    } else {
      // aux is still active: put it back into the heap
      assert(active_row(aux) == r);
      ptr_heap_add(heap, aux);
    }

    // prepare for next round
    aux = c1;
    c1 = c2;
    clear_column(aux);

    // Check for abort in this loop
    if (dsolver_should_stop(solver)) {
      // clean up to avoid memory leak
      solver->aux_column = aux;
      dsolver_deactivate_column(solver, c1);
      flush_active_columns(solver);
      return;
    }

  }

  // c1 is the new solved column
  k = solver->nsolved;
  solver->solved_columns[k] = c1;
  solver->nsolved ++;

  // reduce the constant column
  c2 = solver->constant_column;
  k = find_row(c2, r);
  if (k >= 0) {
    q_set(f, &c2->data[k].coeff);
    q_normalize(active_coeff(c1));
    q_integer_div(f, active_coeff(c1));
    if (q_is_nonzero(f)) {
      if (q_is_one(f)) {
        aux = column_sub(aux, c2, c1);
      } else {
        aux = column_submul(aux, c2, f, c1);
      }
      solver->constant_column = aux;
      aux = c2;
    }
  }

  // restore the auxiliary column
  clear_column(aux);
  solver->aux_column = aux;
}



/*
 * Process row r
 * - return false if the system is unsat: the constant of row r
 *   is not reduced to 0. So the row is of the form 
 * - return true if the constant for row r can be reduced to 0
 * - return false otherwise (means the whole system is unsat)
 */
static bool dsolver_process_row(dsolver_t *solver, int32_t r) {
  int32_t *row;
  dcolumn_t *c;
  int32_t k;
  uint32_t i, n;

#if TRACE
  printf("---> Rosser: process row %"PRId32"\n", r);
#endif

  row = solver->row[r];
  assert(row != NULL && ptr_heap_is_empty(&solver->active_columns) &&
         solver->aux_vector.size == 0);

  solver->num_process_rows ++;

  /*
   * if nelems == 0, the row is already reduced, we just need to check
   * whether the constant is zero
   */
  if (ibag_nelems(row) > 0) {
    n = ibag_size(row);
    for (i=0; i<n; i++) {
      k = row[i];
      if (k >= 0) {
        c = solver->column[k];
        dsolver_activate_column(solver, c, r);
        ptr_heap_add(&solver->active_columns, c);
      }
    }

    // empty row[r] then process the columns
    ibag_reset(row);
    dsolver_reduce_columns(solver, r);

    // restore the rows
    dsolver_restore_rows_to_process(solver);

    // Check for abort
    if (solver->status != DSOLVER_SEARCHING) {
      assert(solver->status == DSOLVER_INTERRUPTED ||
	     solver->status == DSOLVER_UNSOLVED);
      return true;
    }
  }

#if TRACE
  printf("After processing row %"PRId32"\n", r);
  //  dsolver_print_main_rows(stdout, solver);
  //  dsolver_print_sol_rows(stdout, solver);
  //  dsolver_print_elim_rows(stdout, solver);
  //  dsolver_print_rows_to_process(stdout, solver);
  
#endif


  /*
   * Check whether the constant is zero after reduction
   */
  c = solver->constant_column;
  k = find_row(c, r);
  assert(k < 0 || q_is_nonzero(&c->data[k].coeff));
  // k < 0 means that the constant is zero
  return k < 0;
}


/*
 * Solve the system using Rosser's algorithm
 * - return true if the system is satisfiable
 * - return false otherwise
 */
dsolver_status_t dsolver_is_feasible(dsolver_t *solver) {
  generic_heap_t *to_process;
  int32_t i;

  assert(solver->status == DSOLVER_READY || solver->status == DSOLVER_SIMPLIFIED);
  dsolver_rosser_init(solver);

#if TRACE
  printf("After Rosser-Init\n");
  dsolver_print_status(stdout, solver);
  printf("nvars = %"PRIu32"\n", solver->nvars);
  printf("ncolumns = %"PRIu32"\n", solver->ncolumns);
  printf("number of eliminated rows = %"PRIu32"\n", solver->elim.nelems);
  dsolver_print_main_rows(stdout, solver);
  dsolver_print_sol_rows(stdout, solver);
  dsolver_print_elim_rows(stdout, solver);
  printf("\n");
  dsolver_print_rows_to_process(stdout, solver);
  fflush(stdout);
#endif

  solver->num_process_rows = 0;
  solver->num_reduce_ops = 0;
  solver->max_coeff_size = 0;
  solver->max_column_size = 0;
  solver->status = DSOLVER_SEARCHING;  // to detect interruptions

  to_process = &solver->rows_to_process;
  while (! generic_heap_is_empty(to_process)) {
    i = generic_heap_get_min(to_process);
    if (! dsolver_process_row(solver, i)) {
      solver->status = DSOLVER_SOLVED_UNSAT;
      solver->unsat_row = i;
      reset_generic_heap(to_process);

#if TRACE
      dsolver_print_status(stdout, solver);
#endif

#if 0
      printf("dsolver done: nrows = %"PRIu32", ncolumns = %"PRIu32", coeff size = %"PRIu32", column size = %"PRIu32", reduce_ops = %"PRIu32"\n",
	     solver->nrows, solver->ncolumns, solver->max_coeff_size, solver->max_column_size, solver->num_reduce_ops);
      fflush(stdout);
#endif
      goto done;
    }

    if (solver->status != DSOLVER_SEARCHING) {
      assert(solver->status == DSOLVER_INTERRUPTED ||
	     solver->status == DSOLVER_UNSOLVED);
      goto done;
    }
  }

#if 0
  printf("dsolver done: nrows = %"PRIu32", ncolumns = %"PRIu32", coeff size = %"PRIu32", column size = %"PRIu32", reduce_ops = %"PRIu32"\n",
	 solver->nrows, solver->ncolumns, solver->max_coeff_size, solver->max_column_size, solver->num_reduce_ops);
  fflush(stdout);
#endif

  solver->status = DSOLVER_SOLVED_SAT;

 done:
  return solver->status;
}



/*************************
 *  BUILD BASE SOLUTION  *
 ************************/

/*
 * Allocate the base_sol array and initialize all elements to zero
 * - except that base_sol[0] = base_sol[const_idx] = 1
 */
static void alloc_base_solutions(dsolver_t *solver) {
  rational_t *a;
  uint32_t i, n;

  assert(solver->base_sol == NULL);

  n = solver->nvars;
  if (n > 0) {
    a = (rational_t *) safe_malloc(n * sizeof(rational_t));
    for (i=0; i<n; i++) {
      q_init(a + i);
    }
    q_set_one(a); // a[0] := 1
    solver->base_sol = a;
  }
}


/*
 * Set the base solution for all non-eliminated variables
 */
static void dsolver_build_base_sol_row(dsolver_t *solver) {
  dcolumn_t *c;
  uint32_t i, n;
  int32_t k;

  c = solver->constant_column;
  n = solver->nvars;
  for (i=0; i<n; i++) {
    k = solver->sol_row[i];
    if (k >= (int32_t) solver->main_rows) {
      k = find_row(c, k);
      if (k >= 0) {
        q_set(solver->base_sol + i, &c->data[k].coeff);
      }
    }
  }
}


/*
 * Compute the solution for a variable x := p
 * - the solution for all variables occurring in p must be computed first
 */
static void dsolver_build_sol_elim(dsolver_t *solver, int32_t x, polynomial_t *p) {
  rational_t *s;
  uint32_t i, n;
  int32_t y;

  assert(0 < x && x < solver->nvars && solver->base_sol != NULL && q_is_one(solver->base_sol + 0));
  s = solver->base_sol + x;
  assert(q_is_zero(s));
  n = p->nterms;
  for (i=0; i<n; i++) {
    y = p->mono[i].var;
    assert(0 <= y && y < solver->nvars);
    q_addmul(s, &p->mono[i].coeff, solver->base_sol + y);
  }
}

/*
 * Build the solution (as a mapping from variables to rationals)
 * - the solver status must be SOLVED_SAT
 */
void dsolver_build_solution(dsolver_t *solver) {
  delim_vector_t *v;
  uint32_t n;

  assert(solver->status == DSOLVER_SOLVED_SAT);

  alloc_base_solutions(solver);
  dsolver_build_base_sol_row(solver);

  v = &solver->elim;
  n = v->nelems;
  while (n > 0) {
    n --;
    dsolver_build_sol_elim(solver, v->data[n].var, v->data[n].poly);
  }
}




/****************************
 *  BUILD GENERIC SOLUTION  *
 ***************************/

/*
 * Allocate the gen_sol array and initialize all elements to NULL
 * except gen_sol[0] = constant polynomial 1.
 */
static void alloc_general_solutions(dsolver_t *solver) {
  polynomial_t **a;
  polynomial_t *p;
  uint32_t i, n;

  assert(solver->gen_sol == NULL);

  n = solver->nvars;
  if (n > 0) {
    a = (polynomial_t **) safe_malloc(n * sizeof(polynomial_t *));
    for (i=0; i<n; i++) {
      a[i] = NULL;
    }
    // initialize a[0] = polynomial 1
    p = alloc_raw_polynomial(1);
    p->mono[0].var = const_idx;
    q_set_one(&p->mono[0].coeff);
    a[0] = p;
    solver->gen_sol = a;
  }
}


/*
 * Allocate the param_id array and assign a parameter index to
 * each non NULL column. Also set num_params.
 */
static void init_parameter_indices(dsolver_t *solver) {
  int32_t *id;
  uint32_t i, n;
  int32_t k;

  assert(solver->param_id == NULL);

  n = solver->ncolumns;
  k = solver->nvars;
  if (n > 0) {
    id = (int32_t *) safe_malloc(n * sizeof(int32_t));
    for (i=0; i<n; i++) {
      id[i] = -1;
      if (solver->column[i] != NULL) {
        id[i] = k;
        k++;
      }
    }
    solver->param_id = id;
  }
  solver->num_params = k - solver->nvars;
}


/*
 * Convert row r into a polynomial
 */
static polynomial_t *dsolver_gen_sol_row(dsolver_t *solver, int32_t r) {
  polynomial_t *p;
  int32_t *row;
  dcolumn_t *c;
  uint32_t i, t, n;
  int32_t k, x;

  assert(0 <= r && r < solver->nrows);
  row = solver->row[r];
  n = ibag_nelems(row);

  /*
   * check whether the constant for row r is nonzero
   * and allocate a polynomial of the right size
   */
  c = solver->constant_column;
  k = find_row(c, r);
  if (k >= 0) {
    assert(q_is_nonzero(&c->data[k].coeff));
    p = alloc_raw_polynomial(n + 1);
    p->mono[0].var = const_idx;
    q_set(&p->mono[0].coeff, &c->data[k].coeff);
    t = 1;
  } else {
    p = alloc_raw_polynomial(n);
    t = 0;
  }

  // scan the row and copy its content in p->mono[t ... p->nterms - 1]
  // use param_id[k] as variable index for column k
  n = ibag_size(row);
  for (i=0; i<n; i++) {
    k = row[i];
    if (k >= 0) {
      c = solver->column[k];
      x = solver->param_id[k];
      assert(c != NULL && 0 <= x && solver->nvars <= x);
      k = find_row(c, r);
      assert(k >= 0 && q_is_nonzero(&c->data[k].coeff));
      p->mono[t].var = x;
      q_set(&p->mono[t].coeff, &c->data[k].coeff);
      t ++;
    }
  }

  return p;
}


/*
 * Set the generic solution for all non-eliminated variables
 */
static void dsolver_build_gen_sol_row(dsolver_t *solver) {
  uint32_t i, n;
  int32_t k;

  n = solver->nvars;
  for (i=0; i<n; i++) {
    k = solver->sol_row[i];
    if (k >= (int32_t) solver->main_rows) {
      solver->gen_sol[i] = dsolver_gen_sol_row(solver, k);
    }
  }
}


/*
 * Substitute the existing generic solution for all variables into p
 * - buffer must be an empty buffer (it's being used for the computation)
 * - the generic solution for all variables occurring in p must be computed first
 */
static polynomial_t *dsolver_subst_gen_sol(dsolver_t *solver, polynomial_t *p, poly_buffer_t *buffer) {
  uint32_t i, n;
  int32_t x;

  assert(poly_buffer_is_zero(buffer));
  n = p->nterms;
  for (i=0; i<n; i++) {
    x = p->mono[i].var;
    assert(0 <= x && x < solver->nvars && solver->gen_sol[x] != NULL);
    poly_buffer_addmul_poly(buffer, solver->gen_sol[x], &p->mono[i].coeff);
  }
  normalize_poly_buffer(buffer);
  return poly_buffer_get_poly(buffer);
}


/*
 * Compute the generic solution for all eliminated variables
 */
static void dsolver_build_gen_sol_elim(dsolver_t *solver) {
  poly_buffer_t buffer;
  delim_vector_t *v;
  uint32_t n;
  int32_t x;

  v = &solver->elim;
  n = v->nelems;
  if (n > 0) {
    init_poly_buffer(&buffer);
    do {
      n --;
      x = v->data[n].var;
      solver->gen_sol[x] = dsolver_subst_gen_sol(solver, v->data[n].poly, &buffer);
    } while (n > 0);
    delete_poly_buffer(&buffer);
  }
}


/*
 * Build the generic solution (as a mapping from variables to polynomials)
 * - the solver status must be SOLVED_SAT
 */
void dsolver_build_general_solution(dsolver_t *solver) {
  assert(solver->status == DSOLVER_SOLVED_SAT);
  alloc_general_solutions(solver);
  init_parameter_indices(solver);
  dsolver_build_gen_sol_row(solver);
  dsolver_build_gen_sol_elim(solver);
}






/************************
 *  UNSAT EXPLANATIONS  *
 ***********************/

/*
 * The solved part of the matrix (defined by nsolved and array solved_columns)
 * is in echelon form. The algorithm essentially builds (then solve) a
 * triangular system of equations:
 *
 *   a_11 x_1 + b_1 = 0
 *   a_21 x_1 + a_22 x_2 + b_2 = 0
 *    ...
 *   a_k1 x_1 + .... +  a_kk x_k + b_k = 0
 *
 * It's equivalent to look at these as variable substitutions:
 *   x_1 := - b_1/a_11
 *   x_2 := - b_2/a_22 - a_21/a_22 x_1
 *    ....
 *   x_k := - b_k/a_kk - a_k1/a_kk x_1 - a_k2/a_kk x_2 ....
 *
 * Rosser's algorithm applies these substitutions in the forward order from
 * row 1 to row (k-1).  Row k is unsat because the right-hand side expression in the
 * last row reduces to a non-integer constant after the substitutions are applied.
 *
 * To generate a minimal explanation, we search for a subset of the substitutions
 * that are enough to reduce
 *    - b_k/a_kk - a_k1/a_kk x_1 - a_k2/a_kk x_2 ... - a_k{k-1}/a_kk x_{k-1}
 * to a constant. For example, the first substitution may be ignored if
 * x_1 cancels out after applying other substitutions.
 *
 * All this is equivalent to finding a set of substitutions that reduce
 *      a_k1 x_1 + a_k2 x_2 + ... + a_k{k-1} x_{k-1}
 * to a constant, i.e., b_k and a_kk can be ignored.
 * We do this by applying the substitutions backward as needed,
 * from row (k-1) to row 1:
 * - start with E_0 = a_k1 x_1 + ... + a_k{k-1} x_{k-1}.
 * - if a_k{k-1} is non-zero,
 *     row (k-1) must be  part of the explanation
 *     we replace x_{k-1} by the right hand-side of row k-1,
 *     this gives a new expression E_1 in variables x_1, ..., x_{k-2}.
 * - if a_k{k-1} is zero,
 *     row (k-1) is not part of the explanation
 *     we set E_1 = E_0
 * - then we iterate this process with E_1 and x_{k-2}, E_2 and x_{k-3} and so forth,
 *   until we reach and expression E_t that does not contain any variable.
 *
 * Other trick: the exact values of the constant b_1, ..., b_{k-1} are not relevant,
 * which is good because they are not available in the solver when the explanation
 * is generated.
 */


/*
 * Add the external id of row i to vector v
 */
static inline void ivector_push_row_id(dsolver_t *solver, ivector_t *v, int32_t i) {
  assert(0 <= i && i < solver->main_rows);
  ivector_push(v, solver->row_id[i]);
}

/*
 * Comparison function for aux_heap when used to substitute solved columns
 * - last solved column must be returned first
 *   so i precedes j if i>j
 * - data is not used
 */
static bool solved_column_compare(void *data, int32_t i, int32_t j) {
  return i>j;
}


/*
 * Allocate and initialize the aux_heap and aux_buffer
 * - do nothing if they already exist
 */
static void dsolver_prepare_for_explanation(dsolver_t *solver) {
  if (solver->aux_buffer == NULL) {
    solver->aux_buffer = (poly_buffer_t *) safe_malloc(sizeof(poly_buffer_t));
    init_poly_buffer(solver->aux_buffer);
  }
  if (solver->aux_heap == NULL) {
    solver->aux_heap = (int_heap2_t *) safe_malloc(sizeof(int_heap2_t));
    init_int_heap2(solver->aux_heap, 0, solved_column_compare, NULL);
  }
}



/*
 * Store all monomials of the unsat row, except the last one,
 * into aux_buffer. The unsat row is extracted from the solved columns.
 * If solved_columns[j] = c and c has coefficient a in the unsat row
 * then we copy (a * j) into aux_buffer and j into aux_heap.
 *
 * HACK: we do this even if j == 0, which is normally reserved for constants.
 *
 * Invariant we want to ensure:
 * - heap contains the set of all j such that a * j occurs in buffer
 */
static void dsolver_expl_store_unsat_row(dsolver_t *solver) {
  poly_buffer_t *buffer;
  int_heap2_t *heap;
  dcolumn_t *c;
  int32_t i, j, k;
  uint32_t n;

  n = solver->nsolved;
  i = solver->unsat_row;
  buffer = solver->aux_buffer;
  heap = solver->aux_heap;

  assert(0 <= i && i < solver->main_rows && n > 0 && buffer != NULL && heap != NULL);

  // we skip the last solved column, where the unsatisfiability was found
  n --;
  for (j=0; j<n; j++) {
    c = solver->solved_columns[j];
    k = find_row(c, i);
    if (k >= 0) {
      poly_buffer_add_monomial(buffer, j, &c->data[k].coeff);
      int_heap2_add(heap, j);
    }
  }
}



/*
 * Apply the substitution induced by solved column j to aux_buffer
 * - column has an active element (a, i)
 * - then row i is of the form
 *      a_1 x_1 + ... + a_n x_n
 *   and x_n does not occur in rows i-1, i-2, ..., 0.
 * - the corresponding substitution is
 *      x_n := -1/a_n (a_1 x_1 + ... + a_{n-1} x_{n-1})
 * So if x_n has coefficient c in aux_buffer, we subtract (c/a_n) * row i
 * from the buffer.
 * - the function returns the index i (of the row)
 */
static int32_t dsolver_expl_apply_row_subst(dsolver_t *solver, int32_t j) {
  poly_buffer_t *buffer;
  int_heap2_t *heap;
  dcolumn_t *c;
  rational_t *factor;
  int32_t i, k, l;

  assert(0 <= j && j < solver->nsolved);
  c = solver->solved_columns[j];
  i = active_row(c);

  buffer = solver->aux_buffer;
  heap = solver->aux_heap;
  factor = &solver->reduce_factor;

  poly_buffer_copy_var_coeff(buffer, factor, j); // coeff of x_n in buffer
  q_div(factor, active_coeff(c));               // factor = (c/a_n)

  poly_buffer_clear_monomial(buffer, j);   // clear coeff of x_n in buffer


  /*
   * TODO: check whether factor is 1 or -1 and use cheaper operations
   */

  // rest of row i = elements of index i in solved columns 0 ... j-1
  for (l=0; l<j; l++) {
    c = solver->solved_columns[l];
    k = find_row(c, i);
    if (k >= 0) {
      // add l to the heap if it's not already present
      if (! poly_buffer_has_var(buffer, l)) {
        int_heap2_add(heap, l);
      }
      poly_buffer_submul_monomial(buffer, l, factor, &c->data[k].coeff);
    }
  }

  return i;
}


/*
 * Store the set of relevant rows into vector v
 */
static void dsolver_build_unsat_set(dsolver_t *solver, ivector_t *v) {
  poly_buffer_t *buffer;
  int_heap2_t *heap;
  int32_t j, i;

  // the unsat row is always part of the explanation
  ivector_push_row_id(solver, v, solver->unsat_row);

  if (solver->nsolved == 0) {
    // this should not happen, but it's safe to check anyway
    return;
  }

  dsolver_prepare_for_explanation(solver);
  heap = solver->aux_heap;
  int_heap2_reset_order(heap, solved_column_compare, NULL);
  dsolver_expl_store_unsat_row(solver);
  buffer = solver->aux_buffer;

  while (! int_heap2_is_empty(heap)) {
    j = int_heap2_get_min(heap);
    assert(poly_buffer_has_var(buffer, j));
    if (q_is_nonzero(poly_buffer_var_coeff(buffer, j))) {
      i = dsolver_expl_apply_row_subst(solver, j);
      ivector_push_row_id(solver, v, i);
    }
  }

  // empty aux_buffer
  reset_poly_buffer(buffer);
}





/*
 * Compute an inconsistent set of rows
 * - the solver status must be either TRIV_UNSAT, GCD_UNSAT, or SOLVED_UNSAT
 * - the external ids of the rows in this set are added to vector v
 *   (v is not reset first)
 */
void dsolver_unsat_rows(dsolver_t *solver, ivector_t *v) {
  switch (solver->status) {
  case DSOLVER_READY:
  case DSOLVER_SIMPLIFIED:
  case DSOLVER_SEARCHING:
  case DSOLVER_SOLVED_SAT:
  case DSOLVER_UNSOLVED:
  case DSOLVER_INTERRUPTED:
    break;
  case DSOLVER_TRIV_UNSAT:
  case DSOLVER_GCD_UNSAT:
    // the unsat row is unsatisfiable by itself
    ivector_push_row_id(solver, v, solver->unsat_row);
    break;
  case DSOLVER_SOLVED_UNSAT:
    // need to construct the explanation
    dsolver_build_unsat_set(solver, v);
    break;
  }
}




/******************************************
 *   EXPLANATION FOR A VARIABLE SOLUTION  *
 *****************************************/

/*
 * Add the external id of elim row i to vector v
 * - the id is stored in the source field of elim record number i
 */
static inline void ivector_push_elim_row(dsolver_t *solver, ivector_t *v, int32_t i) {
  assert(0 <= i && i < solver->elim.nelems);
  ivector_push_row_id(solver, v, solver->elim.data[i].source);
}


/*
 * To apply the substitutions defined by the elimination records, we
 * use aux_buffer and aux_heap, but we use a different ordering for
 * aux_heap:
 * - x is before y in this ordering if sol_row[x] < sol_row[y]
 */
static bool elim_var_compare(dsolver_t *solver, int32_t x, int32_t y) {
  assert(0 <= x && x < solver->nvars && 0 <= y && y < solver->nvars
         && 0 <= solver->sol_row[x] && solver->sol_row[x] < solver->main_rows
         && 0 <= solver->sol_row[y] && solver->sol_row[y] < solver->main_rows);
  return solver->sol_row[x] < solver->sol_row[y];
}



/*
 * Store the right-hand side of elimination record i into aux_buffer2
 * - aux_buffer2 and aux_heap must be empty
 * - let p = polynomial in rhs of elim record
 *   then every variable of p that's in an eliminated record is added to aux_heap
 * - skip the constant of p if any
 */
static void dsolver_expl_store_elim_record(dsolver_t *solver, int32_t i) {
  poly_buffer_t *buffer;
  int_heap2_t *heap;
  polynomial_t *p;
  uint32_t j, n;
  int32_t x;

  assert(0 <= i && i < solver->elim.nelems);

  buffer = solver->aux_buffer2;
  heap = solver->aux_heap;
  p = solver->elim.data[i].poly;
  n = p->nterms;
  for (j=0; j<n; j++) {
    x = p->mono[j].var;
    if (x != const_idx) {
      poly_buffer_add_monomial(buffer, x, &p->mono[j].coeff);
      assert(0 <= solver->sol_row[x]);
      if (solver->sol_row[x] < solver->main_rows) {
        int_heap2_add(heap, x);
      }
    }
  }
}



/*
 * Substitute variable x by its definition in aux_buffer2
 * - x must have non-zero coefficient in aux_buffer2
 * - x must occur in an elimination record
 * - return the source id of the elimination record for x
 */
static int32_t dsolver_expl_eliminate_variable(dsolver_t *solver, int32_t x) {
  poly_buffer_t *buffer;
  int_heap2_t *heap;
  polynomial_t *p;
  rational_t *factor;
  int32_t i, j, n;

  buffer = solver->aux_buffer2;
  heap = solver->aux_heap;
  factor = &solver->reduce_factor;

  assert(0 <= x && x < solver->nvars && poly_buffer_has_var(buffer, x));
  i = solver->sol_row[x];
  assert(0 <= i && i < solver->elim.nelems && solver->elim.data[i].var == x);

  poly_buffer_copy_var_coeff(buffer, factor, x); // coeff of x in buffer
  poly_buffer_clear_monomial(buffer, x);         // clear coeff of x in buffer
  p = solver->elim.data[i].poly;                 // definition for x

  /*
   * add factor * p to buffer
   * skip the constant of p if any
   * also add any variable to eliminate into aux_heap
   */
  n = p->nterms;
  for (j=0; j<n; j++) {
    x = p->mono[j].var;
    if (x != const_idx) {
      assert(0 <= solver->sol_row[x]);
      if (solver->sol_row[x] < solver->main_rows && ! poly_buffer_has_var(buffer, x)) {
        int_heap2_add(heap, x);
      }
      poly_buffer_addmul_monomial(buffer, x, factor, &p->mono[j].coeff);
    }
  }

  return i;
}



/*
 * First phase of explanation for variables that have been eliminated
 * during simplification. Construct a polynomial from elimination
 * record i, then apply substitution until that polynomial does not
 * contain any variable that can be eliminated.
 * - i = index of the original elimination record
 * - the resulting polynomial is stored in solver->aux_buffer2
 *   and solver->aux_buffer2 is normalized.
 * - the row id of every substitution applied is added to vector v
 */
static void dsolver_expl_remove_eliminated_vars(dsolver_t *solver, int32_t i, ivector_t *v) {
  poly_buffer_t *buffer;
  int_heap2_t *heap;
  int32_t x, j;

  buffer = solver->aux_buffer2;
  heap = solver->aux_heap;
  ivector_push_elim_row(solver, v, i);
  dsolver_expl_store_elim_record(solver, i);

  while (! int_heap2_is_empty(heap)) {
    x = int_heap2_get_min(heap);
    j = dsolver_expl_eliminate_variable(solver, x);
    ivector_push_elim_row(solver, v, j);
  }

  normalize_poly_buffer(buffer);
}


/*
 * Add a times row i to aux_buffer
 * - row i is interpreted as a linear expression with variables i_1 ... i_n
 * - every eliminated column id i_k is added to aux_heap
 */
static void dsolver_expl_addmul_row(dsolver_t *solver, rational_t *a, int32_t i) {
  poly_buffer_t *buffer;
  int_heap2_t *heap;
  dcolumn_t *c;
  uint32_t j, n;
  int32_t k;

  buffer = solver->aux_buffer;
  heap = solver->aux_heap;
  n = solver->nsolved;

  assert(0 <= i && i < solver->nrows);

  for (j=0; j<n; j++) {
    c = solver->solved_columns[j];
    k = find_row(c, i);
    if (k >= 0) {
      if (! poly_buffer_has_var(buffer, j)) {
        int_heap2_add(heap, j);
      }
      poly_buffer_addmul_monomial(buffer, j, a, &c->data[k].coeff);
    }
  }
}


/*
 * Second phase of explanation: collect eliminated columns
 * - aux_buffer2 must be normalized and contain a polynomial in variables x_1, ..., x_n
 * - a substitution for x_j is defined by sol_row[x_j] = one row of the unimodular matrix U
 * - that row is of the form a_1 c_1 + ... + a_n c_n where c_1, ..., c_n are column indices
 * - we collect the column indices c_i1, ..., c_ik that correspond to eliminated columns
 * - we replace b_j x_j by the polynomial b_j (a_i1 c_i1 + ... + a_ik c_ik)
 * - the result is stored into aux_buffer
 * - every variable c_ij that occurs in aux_buffer is also added to aux_heap
 */
static void dsolver_expl_collect_solved_columns(dsolver_t *solver) {
  poly_buffer_t *buffer;
  monomial_t *p;
  uint32_t i, n;
  int32_t x, k;

  buffer = solver->aux_buffer2;
  n = poly_buffer_nterms(buffer);
  p = poly_buffer_mono(buffer);
  for (i=0; i<n; i++) {
    x = p[i].var;
    assert(0 <= x && x < solver->nvars);
    k = solver->sol_row[x];
    assert(solver->main_rows <= k && k < solver->nrows);
    dsolver_expl_addmul_row(solver, &p[i].coeff, k);
  }
}


/*
 * Store the eliminated columns of row i into aux_buffer
 * - row is interpreted as a linear expression in variables i_1 ... i_m
 *   (same as the column indices)
 * - every variable i_j is added to solver->aux_heap
 */
static void dsolver_expl_store_solution_row(dsolver_t *solver, int32_t i) {
  poly_buffer_t *buffer;
  int_heap2_t *heap;
  dcolumn_t *c;
  uint32_t j, n;
  int32_t k;

  buffer = solver->aux_buffer;
  heap = solver->aux_heap;
  assert(solver->main_rows <= i && i < solver->nrows);
  n = solver->nsolved;

  for (j=0; j<n; j++) {
    c = solver->solved_columns[j];
    k = find_row(c, i);
    if (k >= 0) {
      poly_buffer_add_monomial(buffer, j, &c->data[k].coeff);
      int_heap2_add(heap, j);
    }
  }
}


/*
 * Allocate and initialize aux_buffer2 if it's not allocated already
 */
static void dsolver_prepare_aux_buffer2(dsolver_t *solver) {
  if (solver->aux_buffer2 == NULL) {
    solver->aux_buffer2 = (poly_buffer_t *) safe_malloc(sizeof(poly_buffer_t));
    init_poly_buffer(solver->aux_buffer2);
  }
}


/*
 * Generate an explanation of the solution computed for x
 * - the explanation is stored as a set of row ids into vector v
 */
void dsolver_explain_solution(dsolver_t *solver, int32_t x, ivector_t *v) {
  poly_buffer_t *buffer;
  int_heap2_t *heap;
  int32_t i, j;

  assert(solver->status == DSOLVER_SOLVED_SAT);
  dsolver_prepare_for_explanation(solver); // allocate buffer and heap (if needed)
  heap = solver->aux_heap;

  assert(0 <= x && x < solver->nvars);
  i = solver->sol_row[x];
  assert(i >= 0);
  if (i < solver->main_rows) {
    /*
     * x is in an elimination record number i
     */
    dsolver_prepare_aux_buffer2(solver);
    int_heap2_reset_order(heap, (int_heap_cmp_fun_t) elim_var_compare, solver);
    dsolver_expl_remove_eliminated_vars(solver, i, v);
    int_heap2_reset_order(heap, solved_column_compare, NULL);
    dsolver_expl_collect_solved_columns(solver);
    reset_poly_buffer(solver->aux_buffer2);

  } else {
    /*
     * x is defined by solution row i
     */
    int_heap2_reset_order(heap, solved_column_compare, NULL);
    dsolver_expl_store_solution_row(solver, i);
  }

  // Final phase: eliminate the solved columns from aux_buffer
  buffer = solver->aux_buffer;
  while (! int_heap2_is_empty(heap)) {
    j = int_heap2_get_min(heap);
    assert(poly_buffer_has_var(buffer, j));
    if (q_is_nonzero(poly_buffer_var_coeff(buffer, j))) {
      i = dsolver_expl_apply_row_subst(solver, j);
      ivector_push_row_id(solver, v, i);
    }
  }

  // empty aux_buffer
  reset_poly_buffer(buffer);
}




/******************
 *  FOR TESTING   *
 *****************/

/*
 * Make a copy of the constant column then clear it.
 * the resulting system is always satisfiable.
 * - return the copy
 */
dcolumn_t *dsolver_save_and_clear_constant_column(dsolver_t *solver) {
  dcolumn_t *c;

  c = solver->constant_column;
  solver->constant_column = new_column(0, -1);
  return c;
}

/*
 * Restore the constant column to c
 * - must be the column returned by the previous operation
 */
void dsolver_restore_constant_column(dsolver_t *solver, dcolumn_t *c) {
  delete_column(solver->constant_column);
  solver->constant_column = c;
}


/*
 * Put back the solved columns into the whole system
 * (after solving).
 */
void dsolver_restore_solved_columns(dsolver_t *solver) {
  uint32_t i, n;

  n = solver->nsolved;
  for (i=0; i<n; i++) {
    dsolver_deactivate_column(solver, solver->solved_columns[i]);
  }
  solver->nsolved = 0;
}



