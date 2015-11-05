/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST OF MATRICES/PIVOTING ETC.
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "solvers/simplex/matrices.h"
#include "terms/polynomials.h"
#include "terms/rationals.h"



#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

#endif


#if 0
/*
 * Table for selection of random rational coefficients (not used)
 */
// rational numbers
#define MAX_NUMERATOR (INT32_MAX>>1)
#define MIN_NUMERATOR (INT32_MIN>>1)
#define MAX_DENOMINATOR MAX_NUMERATOR

static int32_t num[12] = {
  1, 1, -1, 0, 120, -120, -120, 120, INT32_MAX, INT32_MIN, MIN_NUMERATOR, MAX_NUMERATOR
};

static uint32_t den[12] = {
  1, 10, 200, 72, 400, 999, INT32_MAX, MAX_DENOMINATOR, 1000, 120, 168, MAX_DENOMINATOR + 2
};

#endif


/*
 * 6 predefined variables + the constant
 */
#define NUMVARS 7

static char *name[NUMVARS] = { "1", "x", "y", "z", "t", "u", "v"};

/*
 * Array for building monomials/polynomials
 */
#define MAXMONOMIALS 30

static monomial_t monarray[MAXMONOMIALS];

// array of small coefficients
static int32_t coeffs[NUMVARS];

/*
 * Global matrix
 */
static matrix_t matrix;



/*
 * Print a variable
 */
static void print_arith_var(FILE *f, int32_t v) {
  if (0 <= v && v < NUMVARS) {
    fprintf(f, "%s", name[v]);
  } else {
    fprintf(f, "z!%"PRId32, v);
  }
}


/*
 * Print a monomial a.v
 * - if first is true, this is the first monomial of a polynomial or row
 */
static void print_monomial(FILE *f, rational_t *c, int32_t v, bool first) {
  bool negative, abs_one;

  negative = q_is_neg(c);
  if (negative) {
    abs_one = q_is_minus_one(c);
    if (first) {
      if (abs_one && v != const_idx) {
	fprintf(f, "- ");
      } else {
	fprintf(f, "-");
      }
    } else {
      fprintf(f, " - ");
    }
  } else {
    if (! first) {
      fprintf(f, " + ");
    }
    abs_one = q_is_one(c);
  }

  if (v == const_idx) {
    q_print_abs(f, c);
  } else {
    if (! abs_one) {
      q_print_abs(f, c);
      fprintf(f, " * ");
    }
    print_arith_var(f, v);
  }
}


#if 0

/*
 * Print polynomial p (not used)
 */
static void print_polynomial(FILE *f, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  if (n == 0) {
    fprintf(f, "0");
  } else {
    for (i=0; i<n; i++) {
      print_monomial(f, &p->mono[i].coeff, p->mono[i].var, i == 0);
    }
  }
}

#endif


/*
 * Print matrix row
 */
static void print_row(FILE *f, row_t *row) {
  uint32_t i, n;
  int32_t v;
  bool first;

  first = true;
  n = row->size;
  for (i=0; i<n; i++) {
    v = row->data[i].c_idx;
    if (v >= 0) {
      print_monomial(f, &row->data[i].coeff, v, first);
      first = false;
    }
  }

  if (first) {
    fprintf(f, "0");
  }

  fprintf(f, " == 0");
}



/*
 * Print matrix m
 */
static void print_matrix(FILE *f, matrix_t *m) {
  uint32_t i, n;

  n = m->nrows;
  for (i=0; i<n; i++) {
    fprintf(f, "  row[%"PRIu32"]:  ", i);
    print_row(f, m->row[i]);
    fputc('\n', f);
  }
  fputc('\n', f);

  if (m->base_var != NULL) {
    fprintf(f, "basic vars:");
    n = m->nrows;
    for (i=0; i<n; i++) {
      if (m->base_var[i] >= 0) {
	fprintf(f, " ");
	print_arith_var(f, m->base_var[i]);
      }
    }
    fprintf(f, "\n\n");
  }
}


#if 0

/*
 * Set a to a randomly picked rational (not used)
 */
static void random_rational(rational_t *a) {
  q_set_int32(a, num[random() % 12], den[random() %12]);
}

#endif

/*
 * Initialize monarray using the global coeff array
 * - return the number of monomials = non-zero coefficients
 */
static uint32_t make_poly(void) {
  uint32_t i, j;

  j = 0;
  for (i=0; i<NUMVARS; i++) {
    if (coeffs[i] != 0) {
      monarray[j].var = i;
      q_set32(&monarray[j].coeff, coeffs[i]);
      j ++;
    }
  }
  // add the end marker
  monarray[j].var = max_idx;

  return j;
}


/*
 * Make a polynomial with coefficients +/-1
 * - m = number of variables
 * - d = number of non-zero coefficients
 * The polynomial is stored in monarray
 */
static uint32_t make_random_poly(uint32_t m, uint32_t d) {
  uint32_t i;

  assert(d < m && d < MAXMONOMIALS);

  for (i=0; i<d; i++) {
    monarray[i].var = random() % m; // random variable
    if ((random() & 0xffff) > 0x7fff) {
      q_set_one(&monarray[i].coeff);
    } else {
      q_set_minus_one(&monarray[i].coeff);
    }
  }
  // end-marker
  monarray[i].var = max_idx;

  // normalize
  sort_monarray(monarray, i);
  return normalize_monarray(monarray, i);
}


/*
 * Matrix test1:
 *  x + 2 y + 3 z = 0
 *  x - 2 y - z = 0
 *  -x + t = 0
 *  4x - u = 0
 */
static void init_matrix1(matrix_t *m) {
  uint32_t i, n;

  init_matrix(m, 0, 0);
  matrix_add_columns(m, NUMVARS);


  // x + 2y + 3 z
  for (i=0; i<NUMVARS; i++) {
    coeffs[i] = 0;
  }
  coeffs[1] = 1;
  coeffs[2] = 2;
  coeffs[3] = 3;
  n = make_poly();
  matrix_add_row(m, monarray, n);

  // x - 2y - z
  for (i=0; i<NUMVARS; i++) {
    coeffs[i] = 0;
  }
  coeffs[1] = 1;
  coeffs[2] = -2;
  coeffs[3] = -1;
  n = make_poly();
  matrix_add_row(m, monarray, n);

  // - x + t
  for (i=0; i<NUMVARS; i++) {
    coeffs[i] = 0;
  }
  coeffs[1] = -1;
  coeffs[4] = 1;
  n = make_poly();
  matrix_add_row(m, monarray, n);

  // 4 x - u
  for (i=0; i<NUMVARS; i++) {
    coeffs[i] = 0;
  }
  coeffs[1] = 4;
  coeffs[5] = -1;
  n = make_poly();
  matrix_add_row(m, monarray, n);
}


/*
 * Random matrix:
 * - n = number of rows
 * - m = number of columns
 * - d = number of non-zeros per row
 * coefficients are +/-1
 */
static void init_random_matrix(matrix_t *matrix, uint32_t n, uint32_t m, uint32_t d) {
  uint32_t i, k;

  init_matrix(matrix, 0, 0);
  matrix_add_columns(matrix, m);

  for (i=0; i<n; i++) {
    k = make_random_poly(m, d);
    matrix_add_row(matrix, monarray, k);
  }
}

/*
 * Apply a random pivot
 */
static void random_pivot(matrix_t *matrix) {
  uint32_t i, n, r, j, k;
  int32_t c;
  row_t *row;

  // select a random row
  r = (uint32_t) (random() % matrix->nrows);
  row = matrix->row[r];
  assert(row != NULL);

  k = (uint32_t) (random() % row->nelems);
  n = row->size;
  j = 0;
  for (i=0; i<n; i++) {
    c = row->data[i].c_idx;
    if (c >= 0 && c != const_idx) {
      if (j == k) {
	printf("\n==== Pivot ");
	print_arith_var(stdout, c);
	printf(" in row %"PRIu32" ====\n", r);
	matrix_pivot(matrix, r, i);
	return;
      }
      j ++;
    }
  }
}


int main(void) {
  uint32_t i;

  init_rationals();
  for (i=0; i<MAXMONOMIALS; i++) {
    q_init(&monarray[i].coeff);
  }

  init_matrix1(&matrix);
  printf("\n==== MATRIX 1 ====\n");
  print_matrix(stdout, &matrix);

  // pivot: x basic in row 2
  matrix_pivot(&matrix, 2, 0);
  printf("\n==== PIVOT ====\n");
  print_matrix(stdout, &matrix);

  // pivot: y basic in row 1
  matrix_pivot(&matrix, 1, 1);
  printf("\n==== PIVOT ====\n");
  print_matrix(stdout, &matrix);

  for (i=0; i<100; i++) {
    random_pivot(&matrix);
    //    print_matrix(stdout, &matrix);
  }

  reset_matrix(&matrix);
  delete_matrix(&matrix);

  init_random_matrix(&matrix, 300, 500, 5);
  printf("\n==== RANDOM MATRIX ====\n");
  print_matrix(stdout, &matrix);
  for (i=0; i<100; i++) {
    random_pivot(&matrix);
    print_matrix(stdout, &matrix);
  }

  delete_matrix(&matrix);
  for (i=0; i<MAXMONOMIALS; i++) {
    q_clear(&monarray[i].coeff);
  }
  cleanup_rationals();

  return 0;
}
