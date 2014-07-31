/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TABLE OF ROWS FOR SIMPLEX PROPAGATION
 */

#include <assert.h>
#include <float.h>

#include "utils/prng.h"
#include "utils/memalloc.h"
#include "utils/index_vectors.h"
#include "solvers/simplex/simplex_prop_table.h"


/*
 * PROP ROWS
 */

/*
 * Allocate a propagation row of size n = nterms
 * - initialize lock and nterms
 */
static prop_row_t *new_prop_row(uint32_t n) {
  prop_row_t *tmp;

  if (n >= MAX_PROP_ROW_SIZE) {
    out_of_memory();
  }
  tmp = (prop_row_t *) safe_malloc(sizeof(prop_row_t) + (n + 1) * sizeof(monomial_t));
  tmp->lock = null_literal;
  tmp->nterms = n;
  return tmp;
}


/*
 * Delete p (clear all the rational coefficients first)
 */
static void delete_prop_row(prop_row_t *p) {
  uint32_t i, n;

  n = p->nterms;
  for (i=0; i<n; i++) {
    q_clear(&p->mono[i].coeff);
  }
  safe_free(p);
}




/*
 * PROPAGATION TABLE
 */

/*
 * Initialization:
 * - n = initial row capacity (if n=0, the default size is used)
 * - m = initial column capacity (if m=0, the default size is used)
 */
void init_prop_table(prop_table_t *table, uint32_t n, uint32_t m) {
  if (n == 0) n = DEF_PROPTABLE_ROW_SIZE;
  if (m == 0) m = DEF_PROPTABLE_VAR_SIZE;

  if (n >= MAX_PROPTABLE_ROW_SIZE || m >= MAX_PROPTABLE_VAR_SIZE) {
    out_of_memory();
  }

  table->nrows = 0;
  table->nvars = 0;
  table->row_size = n;
  table->var_size = n;

  table->row = (prop_row_t **) safe_malloc(n * sizeof(prop_row_t *));
  table->mark = allocate_bitvector(n);
  table->col = (int32_t **) safe_malloc(m * sizeof(int32_t *));

  table->act_increment = PROPTABLE_ACT_INCREMENT;
  table->inv_act_decay = 1/PROPTABLE_DECAY_FACTOR;

  init_ivector(&table->free_rows, PROPTABLE_FREE_ROWS_SIZE);
}


/*
 * Increase the row capacity by 50%
 */
static void prop_table_increase_row_size(prop_table_t *table) {
  uint32_t n;

  n = table->row_size + 1;
  n += n>>1;
  if (n >= MAX_PROPTABLE_ROW_SIZE) {
    out_of_memory();
  }
  table->row = (prop_row_t **) safe_realloc(table->row, n * sizeof(prop_row_t *));
  table->mark = extend_bitvector(table->mark, n);
  table->row_size = n;
}


/*
 * Allocate a new row index
 * - take it from free_rows vector if possible
 * - increase nrows otherwise
 */
static uint32_t prop_table_alloc_row(prop_table_t *table) {
  ivector_t *v;
  uint32_t i;

  v = &table->free_rows;
  i = v->size;
  if (i > 0) {
    // get the last element of v
    i --;
    v->size = i;
    return v->data[i];
  }

  i = table->nrows;
  if (i == table->row_size) {
    prop_table_increase_row_size(table);
  }
  assert(i < table->row_size);
  table->nrows = i+1;

  return i;
}


/*
 * Set the number of variables to m
 * - no changes if prop->nvars >= m
 * - otherwise, the column vector is made large enough for m variables
 * - for all new variables, col[x] is initialized to NULL
 */
void prop_table_set_numvars(prop_table_t *table, uint32_t m) {
  uint32_t i, n;

  if (m > table->nvars) {
    n = table->var_size;
    if (n < m) {
      // new var size = max(m, old size + 50%)
      n += n>>1;
      if (n < m) {
        n = m;
      }

      if (n >= MAX_PROPTABLE_VAR_SIZE) {
        out_of_memory();
      }

      table->col = (int32_t **) safe_realloc(table->col, n * sizeof(int32_t *));
      table->var_size  = n;
    }

    // initialize newly allocated columns
    assert(m <= table->var_size);
    for (i=table->nvars; i<m; i++) {
      table->col[i] = NULL;
    }

    table->nvars = m;
  }
}



/*
 * Delete the table
 */
void delete_prop_table(prop_table_t *table) {
  prop_row_t *p;
  uint32_t i, n;

  // free all the rows
  n = table->nrows;
  for (i=0; i<n; i++) {
    p = table->row[i];
    if (p != NULL) {
      delete_prop_row(p);
    }
  }
  safe_free(table->row);
  delete_bitvector(table->mark);

  // free all the columns
  n = table->nvars;
  for (i=0; i<n; i++) {
    delete_index_vector(table->col[i]);
  }
  safe_free(table->col);

  delete_ivector(&table->free_rows);

  table->row = NULL;
  table->mark = NULL;
  table->col = NULL;
}



/*
 * Empty the table: delete all rows and columns
 * - reset nvars and nrows to 0
 * - do not delete arrays row, mark, and col
 */
void reset_prop_table(prop_table_t *table) {
  prop_row_t *p;
  uint32_t i, n;

  // free all the rows
  n = table->nrows;
  for (i=0; i<n; i++) {
    p = table->row[i];
    if (p != NULL) {
      delete_prop_row(p);
    }
  }

  // free all the columns
  n = table->nvars;
  for (i=0; i<n; i++) {
    delete_index_vector(table->col[i]);
  }

  ivector_reset(&table->free_rows);

  table->nrows = 0;
  table->nvars = 0;
}




/*
 * ROW ADDITION
 */

/*
 * Add row p of index i to the column vectors
 */
static void attach_row(prop_table_t *table, prop_row_t *p, uint32_t i) {
  uint32_t j, n;
  int32_t x, idx;

  n = p->nterms;
  for (j=0; j<n; j++) {
    x = p->mono[j].var;
    if (q_is_pos(&p->mono[j].coeff)) {
      idx = pos_row_idx(i);
    } else {
      assert(q_is_neg(&p->mono[j].coeff));
      idx = neg_row_idx(i);
    }
    add_index_to_vector(table->col + x, idx);
  }
}


/*
 * Copy row (from a matrix) into table
 * - the table is resized if necessary (to add variables)
 * - the row is added to the column vector of all its variables
 * - its activity is set to table->act_increment
 */
void prop_table_add_row(prop_table_t *table, row_t *row) {
  prop_row_t *p;
  uint32_t i, j, n;
  int32_t x, max_x;

  assert(row->nelems >= 2);

  n = row->nelems;
  p = new_prop_row(n);
  p->activity = table->act_increment;

  // copy row into p
  j = 0;
  max_x = -1;
  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      p->mono[j].var = x;
      q_init(&p->mono[j].coeff);
      q_set(&p->mono[j].coeff, &row->data[i].coeff);
      assert(q_is_nonzero(&p->mono[j].coeff));
      j ++;
      if (x >= max_x) {
        max_x = x;
      }
    }
  }

  // add the end marker to p
  assert(j == p->nterms);
  p->mono[j].var = max_idx;
  q_init(&p->mono[j].coeff); // could be skipped

  i = prop_table_alloc_row(table);
  table->row[i] = p;
  clr_bit(table->mark, i);

  // resize the table for at least max_x variables
  prop_table_set_numvars(table, max_x + 1);

  // add p to the columns
  attach_row(table, p, i);
}



/*
 * Divide all activities by ACT_THRESHOLD (1e20)
 */
static void prop_table_rescale_activities(prop_table_t *table) {
  prop_row_t *p;
  uint32_t i, n;

  n = table->nrows;
  for (i=0; i<n; i++) {
    p = table->row[i];
    if (p != NULL) {
      p->activity *= PROPTABLE_INV_ACT_THRESHOLD;
    }
  }
  table->act_increment *= PROPTABLE_INV_ACT_THRESHOLD;
}



/*
 * Increase activity of row i
 * - rescale all row activities if that goes above the max activity threshold
 */
void prop_table_increase_row_activity(prop_table_t *table, uint32_t i) {
  prop_row_t *p;

  assert(i < table->nrows && table->row[i] != NULL);
  p = table->row[i];
  p->activity += table->act_increment;
  if (p->activity > PROPTABLE_ACT_THRESHOLD) {
    prop_table_rescale_activities(table);
  }
}


/*
 * Support for row deletion: find the median of an array of floats
 * - a must be an array of size n+1 with a[n] larger than a[0 ... n-1]
 *   (e.g., a[n] = FLT_MAX)
 * - n must be positive
 */
static float median(float *a, uint32_t n) {
  uint32_t low, high, i, j, half;
  float pivot, aux;

  assert(n > 0);

  half = n/2;
  low = 0;
  high = n;

  do {
    // pick a random pivot in a[low ... half - 1]
    i = low + random_uint(half - low);
    pivot = a[i];

    // swap a[i] and a[low]
    a[i] = a[low];
    a[low] = pivot;

    i = low;
    j = high;
    for (;;) {
      do { j --; } while (a[j] > pivot);
      do { i ++; } while (a[i] < pivot);

      if (i >= j) break;

      aux = a[i];
      a[i] = a[j];
      a[j] = aux;
    }

    // swap a[low] (pivot) and a[j]
    a[low] = a[j];
    a[j] = pivot;

    /*
     * At this point:
     * - a[0 ... j-1] <= pivot
     * - a[j] = pivot
     * - a[j+1 ... n-1] >= pivot
     * low <= j < high and low <= half < high
     */
    if (j < half) {
      low = j+1;
    } else {
      high = j;
    }
  } while (j != half);

  return a[half];
}


/*
 * Reduce the table:
 * - remove half of the rows (unless they are marked)
 * - keep all the marked rows
 */
void prop_table_reduce(prop_table_t *table) {
  float *a;   // auxiliary array for copying activities
  prop_row_t *p;
  float threshold;
  uint32_t i, j, n;


  n = num_prop_rows(table);
  if (n == 0) return;

  threshold = FLT_MIN; // if malloc fails we can still do something

  a = (float *) malloc((n + 1) * sizeof(float));
  if (a != NULL) {
    // copy activities in array a
    j = 0;
    n = table->nrows;
    for (i=0; i<n; i++) {
      p = table->row[i];
      if (p != NULL) {
        a[j] = p->activity;
        j ++;
      }
    }
    // add end-marker
    assert(j == num_prop_rows(table));
    a[j] = FLT_MAX;

    // get median activity
    threshold = median(a, j);
    free(a);
  }

  // reset all the column vectors
  n = table->nvars;
  for (i=0; i<n; i++) {
    reset_index_vector(table->col[i]);
  }

  // make sure any row with activity < act_increment/n is deleted
  n = table->nrows;
  if (threshold < table->act_increment/n) {
    threshold = table->act_increment/n;
  }

  // delete all rows of activity < threshold that are not locked
  for (i=0; i<n; i++) {
    p = table->row[i];
    if (p != NULL){
      if (p->activity < threshold && p->lock != null_literal) {
	delete_prop_row(p);
	table->row[i] = NULL;
	ivector_push(&table->free_rows, i);
      } else {
	attach_row(table, p, i);
      }
    }
  }
}
