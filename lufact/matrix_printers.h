/*
 * Output functions for matrix-related data structures
 *
 * Created 2006/02/16.
 * Based on print functions in vectors.h and matrices.h
 */

#ifndef __MATRICE_PRINTERS_H
#define __MATRICE_PRINTERS_H


#ifdef PRINT

#include <stdio.h>
#include "matrix_types.h"





/*
 * Print array of vector elements v
 * n = length of the array
 */
extern void print_vectelem(FILE *f, vector_elem_t *v, int n, char *name);


/*
 * Print details of vector *v
 */
extern void print_vector(FILE *f, vector_t *v, char *name);


/*
 * Print buffer as a vector
 */
extern void print_buffer(FILE *f, buffer_t *buffer, char *name);


/*
 * Print a list (doubly-linked list used for row/column permutations)
 */
extern void print_list(FILE *f, list_t *list);


/*
 * Print a list in reverse order
 */
extern void print_reverse_list(FILE *f, list_t *list);



/*
 * Print the detailed structure of a matrix m
 */
extern void print_matrix_details(FILE *f, matrix_t *m);


/*
 * Print matrix m:
 * - for each row, print the row vector as a list of triples
 * - for each column, print the column vector as a list of pairs
 */
extern void print_matrix(FILE *f, matrix_t *m);


/*
 * Print rows of m
 * - for each row, print the row vector as a list of pairs <column-index, coeff>
 */
extern void print_matrix_rows(FILE *f, matrix_t *m);


/*
 * Print matrix m:
 * - print each row as a linear term a_1 x_1 + ... + a_k x_k
 */
extern void print_matrix_poly(FILE *f, matrix_t *m);


/*
 * Print column dependency data for matrix m:
 * - for each variable x_i print the columns where x_i
 * occurs with non-zero coefficient.
 */
extern void print_matrix_columns_poly(FILE *f, matrix_t *m);



/*
 * Print the list of eliminated rows in matrix m
 */
extern void print_elim_rows(FILE *f, gauss_matrix_t *m);


/*
 * Print the list of eliminated columns in matrix m
 */
extern void print_elim_columns(FILE *f, gauss_matrix_t *m);



/*
 * Print column or row positions:
 * - for an eliminated column i: col_position[i] = 
 *   index of i in the list of eliminated columns
 * - for an eliminated row i: row_position[i] = 
 *   index of i in the list of eliminated rows
 * - for non-eliminated rows or columns index is -1
 */
extern void print_column_positions(FILE *f, gauss_matrix_t *m);
extern void print_row_positions(FILE *f, gauss_matrix_t *m);



/*
 * Print equation m x = a
 */
extern void print_equation(FILE *f, matrix_t *m, buffer_t *a);


/*
 * Print equation x m = b
 */
extern void print_colequation(FILE *f, matrix_t *m, buffer_t *b);


/*
 * Print buffer as a solution vector
 */
extern void print_solution(FILE *f, buffer_t *buffer);



/*
 * Print a compact matrix
 */
extern void print_compact_matrix(FILE *f, compact_matrix_t *m);


/*
 * Print a triangular matrix 
 */
extern void print_triangular_matrix(FILE *f, triangular_matrix_t *m);


/*
 * Print a triangular matrix as equations
 */
extern void print_triangular_matrix_poly(FILE *f, triangular_matrix_t *m);

/*
 * Eta file f
 */
extern void print_eta_file(FILE *f, eta_file_t *e);

#endif /* PRINT */

#endif
