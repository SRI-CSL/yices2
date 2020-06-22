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
 * INCREMENTAL FORM OF THE FLOYD-WARSHALL ALGORITHM
 */


/*
 * We assume that -d-1 gives the right value for any 32bit signed
 * integer d, including when d is (-2^31) = INT32_MIN.  This is true
 * if signed integer operations are done modulo 2^32.  The C standard
 * does not require this, but this can be considered safe (see the
 * autoconf documentation).
 */


#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "solvers/floyd_warshall/idl_floyd_warshall.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"


#define TRACE 0

#if TRACE || !defined(NDEBUG)

#include <stdio.h>
#include <inttypes.h>

#include "solvers/floyd_warshall/idl_fw_printer.h"

#endif



/****************
 *  EDGE STACK  *
 ***************/

/*
 * Initialize the stack
 * - n = initial size
 */
static void init_edge_stack(edge_stack_t *stack, uint32_t n) {
  assert(n < MAX_IDL_EDGE_STACK_SIZE);

  stack->data = (idl_edge_t *) safe_malloc(n * sizeof(idl_edge_t));
  stack->lit = (literal_t *) safe_malloc(n * sizeof(literal_t));
  stack->size = n;
  stack->top = 0;
}


/*
 * Make the stack 50% larger
 */
static void extend_edge_stack(edge_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n>>1;
  if (n >= MAX_IDL_EDGE_STACK_SIZE) {
    out_of_memory();
  }

  stack->data = (idl_edge_t *) safe_realloc(stack->data, n * sizeof(idl_edge_t));
  stack->lit = (literal_t *) safe_realloc(stack->lit, n * sizeof(literal_t));
  stack->size = n;
}


/*
 * Add an edge to the stack
 * - x = source, y = target, c = cost, l = literal attached
 */
static void push_edge(edge_stack_t *stack, int32_t x, int32_t y, int32_t c, literal_t l) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_edge_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i].source = x;
  stack->data[i].target = y;
#ifndef NDEBUG
  stack->data[i].cost = c;
#endif
  stack->lit[i] = l;
  stack->top = i+1;
}


/*
 * Empty the stack
 */
static inline void reset_edge_stack(edge_stack_t *stack) {
  stack->top = 0;
}


/*
 * Delete the stack
 */
static inline void delete_edge_stack(edge_stack_t *stack) {
  safe_free(stack->data);
  safe_free(stack->lit);
  stack->data = NULL;
  stack->lit = NULL;
}




/************
 *  MATRIX  *
 ***********/

/*
 * Initialize the matrix: size is 0
 */
static void init_idl_matrix(idl_matrix_t *matrix) {
  matrix->size = 0;
  matrix->dim = 0;
  matrix->data = NULL;
}



/*
 * Resize to an (n * n) matrix
 * - if n > matrix->dim then new cells are initialized as follows:
 * - for new x, M[x, x].id = 0, M[x, x].dist = 0
 *   for new x and y with x != y, M[x, y].id = null_idl_edge
 * If n < matrix->dim, then some cells are lost
 */
static void resize_idl_matrix(idl_matrix_t *matrix, uint32_t n) {
  uint64_t new_size;
  uint32_t i, j, d;
  idl_cell_t *src, *dst;

  // d = current dimension, n = new dimension
  d = matrix->dim;
  matrix->dim = n;
  if (d == n) return;

  // extend the data array if it's too small
  if (n > matrix->size) {
    new_size = ((uint64_t) n * n) * sizeof(idl_cell_t);
    if (n >= MAX_IDL_MATRIX_DIMENSION || new_size >= SIZE_MAX) {
      out_of_memory();
    }
    matrix->data = (idl_cell_t *) safe_realloc(matrix->data, new_size);
    matrix->size = n;
  }

  if (d < n) {
    // move existing cells
    i = d;
    while (i > 0) {
      i --;
      src = matrix->data + d * i;  // start of current row i
      dst = matrix->data + n * i;  // start of new row i
      j = d;
      while (j > 0) {
        j --;
        dst[j] = src[j];
      }
    }

    // initialize cells [d ... n-1] in rows 0 to d-1
    dst = matrix->data;
    for (i=0; i<d; i++) {
      for (j=d; j<n; j++) {
        dst[j].id = null_idl_edge;
      }
      dst += n;
    }

    // initialize cells [0 ... n-1] in rows d to n-1
    while (i<n) {
      for (j=0; j<n; j++) {
        dst[j].id = null_idl_edge;
      }
      i ++;
      dst += n;
    }

    // initialize diagonal: cell i of row i, for i=d to n-1
    for (i=d; i<n; i++) {
      dst = matrix->data + n * i + i;
      dst->id = 0;
      dst->dist = 0;
    }

  } else {
    assert(n < d);

    // move existing cells
    for (i=0; i<n; i++) {
      src = matrix->data + d * i;
      dst = matrix->data + n * i;
      for (j=0; j<n; j++) {
        dst[j] = src[j];
      }
    }
  }
}


/*
 * Reset to the empty matrix
 */
static inline void reset_idl_matrix(idl_matrix_t *matrix) {
  matrix->dim = 0;
}


/*
 * Delete the matrix
 */
static inline void delete_idl_matrix(idl_matrix_t *matrix) {
  safe_free(matrix->data);
  matrix->data = NULL;
}


/*
 * Pointer to cell x, y
 */
static inline idl_cell_t *idl_cell(idl_matrix_t *m, uint32_t x, uint32_t y) {
  assert(0 <= x && x < m->dim && 0 <= y && y < m->dim);
  return m->data + x * m->dim + y;
}

/*
 * Pointer to the start of row x
 */
static inline idl_cell_t *idl_row(idl_matrix_t *m, uint32_t x) {
  assert(0 <= x && x < m->dim);
  return m->data + x * m->dim;
}


/*
 * Distance from x to y
 */
#ifndef NDEBUG
static inline int32_t idl_dist(idl_matrix_t *m, uint32_t x, uint32_t y) {
  return idl_cell(m, x, y)->dist;
}
#endif

/*
 * Edge id for path from x to y
 */
static inline int32_t idl_edge_id(idl_matrix_t *m, uint32_t x, uint32_t y) {
  return idl_cell(m, x, y)->id;
}




/*****************
 *  SAVED CELLS  *
 ****************/

/*
 * Initialize the stack
 * - n = initial size
 */
static void init_cell_stack(cell_stack_t *stack, uint32_t n) {
  assert(n < MAX_IDL_CELL_STACK_SIZE);

  stack->data = (saved_cell_t *) safe_malloc(n * sizeof(saved_cell_t));
  stack->size = n;
  stack->top = 0;
}


/*
 * Make the stack 50% larger
 */
static void extend_cell_stack(cell_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n>>1;
  if (n >= MAX_IDL_CELL_STACK_SIZE) {
    out_of_memory();
  }

  stack->data = (saved_cell_t *) safe_realloc(stack->data, n * sizeof(saved_cell_t));
  stack->size = n;
}


/*
 * Save cell c on top of the stack
 * - k = index of c in the matrix
 */
static void save_cell(cell_stack_t *stack, uint32_t k, idl_cell_t *c) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_cell_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i].index = k;
  stack->data[i].saved = *c;
  stack->top = i+1;
}


/*
 * Empty the stack
 */
static inline void reset_cell_stack(cell_stack_t *stack) {
  stack->top = 0;
}


/*
 * Delete the stack
 */
static inline void delete_cell_stack(cell_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}





/***********
 *  GRAPH  *
 **********/

/*
 * Initialize graph: use default sizes
 * - store edge 0 (used as a marker for path from x to x)
 */
static void init_idl_graph(idl_graph_t *graph) {
  init_idl_matrix(&graph->matrix);
  init_edge_stack(&graph->edges, DEFAULT_IDL_EDGE_STACK_SIZE);
  init_cell_stack(&graph->cstack, DEFAULT_IDL_CELL_STACK_SIZE);
  init_ivector(&graph->buffer, DEFAULT_IDL_BUFFER_SIZE);

  push_edge(&graph->edges, null_idl_vertex, null_idl_vertex, 0, true_literal);
}

/*
 * Delete all
 */
static void delete_idl_graph(idl_graph_t *graph) {
  delete_cell_stack(&graph->cstack);
  delete_edge_stack(&graph->edges);
  delete_idl_matrix(&graph->matrix);
  delete_ivector(&graph->buffer);
}

/*
 * Reset: empty graph
 */
static void reset_idl_graph(idl_graph_t *graph) {
  reset_idl_matrix(&graph->matrix);
  reset_edge_stack(&graph->edges);
  reset_cell_stack(&graph->cstack);
  ivector_reset(&graph->buffer);

  push_edge(&graph->edges, null_idl_vertex, null_idl_vertex, 0, true_literal);
}


/*
 * Resize: n = number of vertices
 * - extend and initialize the matrix appropriately
 */
static inline void resize_idl_graph(idl_graph_t *graph, uint32_t n) {
  resize_idl_matrix(&graph->matrix, n);
}


/*
 * Get number of edges and saved cells
 */
static inline uint32_t idl_graph_num_edges(idl_graph_t *graph) {
  return graph->edges.top;
}

static inline uint32_t idl_graph_num_cells(idl_graph_t *graph) {
  return graph->cstack.top;
}


/*
 * Auxiliary function: save cell r onto the saved cell stack
 */
static inline void idl_graph_save_cell(idl_graph_t *graph, idl_cell_t *r) {
  save_cell(&graph->cstack, r - graph->matrix.data, r);
}


/*
 * Add new edge to the graph and update the matrix
 * Save any modified cell onto the saved-cell stack
 * - x = source vertex
 * - y = target vertex
 * - c = cost
 * - l = literal for explanations
 * - k = limit on edge ids: if a cell is modified, it is saved for backtracking
 *   only if its edge index is less than k.
 * Preconditions:
 * - x and y must be valid vertices, and x must be different from y
 * - the new edge must not introduce a negative circuit
 */
static void idl_graph_add_edge(idl_graph_t *graph, int32_t x, int32_t y, int32_t c, literal_t l, int32_t k) {
  int32_t id, z, w, d;
  idl_cell_t *r, *s;
  ivector_t *v;
  idl_matrix_t *m;
  int32_t *aux;
  uint32_t i, n;

#if TRACE
  printf("---> IDL: adding edge: ");
  print_idl_vertex(stdout, x);
  printf(" ---> ");
  print_idl_vertex(stdout, y);
  printf(" cost: %"PRId32"\n", c);
#endif

  m = &graph->matrix;
  assert(0 <= x && x < m->dim && 0 <= y && y < m->dim && x != y);

  id = graph->edges.top; // index of the new edge
  push_edge(&graph->edges, x, y, c, l);

  /*
   * collect relevant vertices in vector v:
   * vertex z is relevant if there's a path from y to z and
   *    c + dist(y, z) < dist(x, z)
   * if z is not relevant then, for any vertex w, the new edge
   * cannot reduce dist(w, z)
   */
  v = &graph->buffer;
  ivector_reset(v);
  r = idl_row(m, y);  // start of row y
  s = idl_row(m, x);  // start of row x
  for (z=0; z<m->dim; z++, r++, s++) {
    // r --> cell[y, z] and s --> cell[x, z]
    if (r->id >= 0 && (s->id < 0 || c + r->dist < s->dist)) {
      ivector_push(v, z);
    }
  }

  n = v->size;
  aux = v->data;

  /*
   * Scan relevant vertices with respect to x:
   * vertex w is relevant if there's a path from w to x and
   *   dist(w, x) + c < dist(w, y)
   */
  r = idl_row(m, 0);
  for (w=0; w<m->dim; w++, r += m->dim) {
    // r[x] == cell[w, x] and r[y] == cell[w, y]
    if (r[x].id >= 0 && (r[y].id < 0 || c + r[x].dist < r[y].dist)) {
      // w is relevant: check D[w, z] for all z in vector v
      for (i=0; i<n; i++) {
        z = aux[i];
        if (w != z) {
          // r[z] == cell[w, z] and s --> cell[y, z]
          s = idl_cell(m, y, z);
          d = r[x].dist + c + s->dist; // distance w ---> x -> y ---> z
          if (r[z].id < 0 || d < r[z].dist) {
            // save then update cell[w, z]
            if (r[z].id < k) {
              idl_graph_save_cell(graph, r + z);
            }
            r[z].id = id;
            r[z].dist = d;
          }
        }
      }
    }
  }

}


/*
 * Backtrack: remove edges and restore the matrix
 * - e = first edge to remove (edges of index i ... top-1) are removed
 * - c = pointer into the saved cell stack
 */
static void idl_graph_remove_edges(idl_graph_t *graph, int32_t e, uint32_t c) {
  saved_cell_t *saved;
  idl_cell_t *m;
  uint32_t i, k;

  // restore the edge stack
  assert(e > 0);
  graph->edges.top = e;

  // restore the matrix: copy saved cells back
  i = graph->cstack.top;
  saved = graph->cstack.data;
  m = graph->matrix.data;
  while (i > c) {
    i --;
    k = saved[i].index;
    m[k] = saved[i].saved;
  }
  graph->cstack.top = c;
}




/*
 * Build explanation: get all literals appearing along the shortest path from x to y
 * - the literals are stored in vector v
 */
static void idl_graph_explain_path(idl_graph_t *graph, int32_t x, int32_t y, ivector_t *v) {
  int32_t i;
  literal_t l;

  if (x != y) {
    i = idl_edge_id(&graph->matrix, x, y);
    assert(1 <= i && i < graph->edges.top);
    /*
     * The shortest path from x to y is x ---> s -> t ---> y
     * where s = source of edge i and t = target of edge i.
     */
    idl_graph_explain_path(graph, x, graph->edges.data[i].source, v);
    l = graph->edges.lit[i];
    if (l != true_literal) {
      ivector_push(v, l);
    }
    idl_graph_explain_path(graph, graph->edges.data[i].target, y, v);
  }
}


#ifndef NDEBUG

/*
 * For debugging: check consistency of the matrix
 * - cell[x, x].id must be zero and cell[x, x].val must be 0
 * For all x != y:
 * - cell[x, y].id must be -1 or between 1 and number of edges -1
 * - if cell[x, y].id == i and i != 1 then
 *   let u = source of edge i and v = target of edge i
 *   we must have
 *      cell[x, u].id != 1 and cell[x, u].id < i
 *      cell[v, y].id != 1 and cell[v, y].id < i
 *      cell[x, y].dist = cell[x, u].dist + cost of edge i + cell[v, y].dist
 */
static bool valid_idl_graph(idl_graph_t *graph) {
  idl_matrix_t *m;
  idl_edge_t *e;
  int32_t x, y, i;
  int32_t u, v;

  m = &graph->matrix;
  for (x=0; x<m->dim; x++) {
    for (y=0; y<m->dim; y++) {
      i = idl_edge_id(m, x, y);
      if (i == null_idl_edge) {
        if (x == y) return false;
      } else if (i == 0) {
        if (x != y || idl_dist(m, x, y) != 0) return false;
      } else {
        if (x == y || i >= idl_graph_num_edges(graph)) return false;

        e = graph->edges.data + i;
        u = e->source;
        v = e->target;

        if (idl_edge_id(m, x, u) == null_idl_edge || idl_edge_id(m, x, u) >= i ||
            idl_edge_id(m, v, y) == null_idl_edge || idl_edge_id(m, v, y) >= i ||
            idl_dist(m, x, y) != idl_dist(m, x, u) + e->cost + idl_dist(m, v, y)) {
          return false;
        }
      }
    }
  }

  return true;
}

#endif



/****************
 *  ATOM TABLE  *
 ***************/

/*
 * Initialize the table
 * - n = initial size
 */
static void init_idl_atbl(idl_atbl_t *table, uint32_t n) {
  idl_listelem_t *tmp;

  assert(n < MAX_IDL_ATBL_SIZE);

  table->size = n;
  table->natoms = 0;
  table->atoms = (idl_atom_t *) safe_malloc(n * sizeof(idl_atom_t));
  table->mark = allocate_bitvector(n);

  // table->free_list[-1] is the list header
  // the list is initially empty
  tmp = (idl_listelem_t *) safe_malloc((n+1) * sizeof(idl_listelem_t));
  tmp[0].pre = -1;
  tmp[0].next = -1;
  table->free_list = tmp + 1;
}


/*
 * Make the table 50% larger
 */
static void extend_idl_atbl(idl_atbl_t *table) {
  uint32_t n;
  idl_listelem_t *tmp;

  n = table->size + 1;
  n += n>>1;
  if (n >= MAX_IDL_ATBL_SIZE) {
    out_of_memory();
  }

  table->size = n;
  table->atoms = (idl_atom_t *) safe_realloc(table->atoms, n * sizeof(idl_atom_t));
  table->mark = extend_bitvector(table->mark, n);

  tmp = (idl_listelem_t *) safe_realloc(table->free_list - 1, (n+1) * sizeof(idl_listelem_t));
  table->free_list = tmp + 1;
}



/*
 * Add element i last into the free list
 */
static inline void idlatom_add_last(idl_listelem_t *list, int32_t i) {
  int32_t k;

  k = list[-1].pre; // last element
  list[k].next = i;
  list[i].pre = k;
  list[i].next = -1;
  list[-1].pre = i;
}

/*
 * Remove element i from the free list
 * - keep list[i].next and list[i].pre unchanged so that i can be put back
 */
static inline void idlatom_remove(idl_listelem_t *list, int32_t i) {
  int32_t j, k;

  j = list[i].next;
  k = list[i].pre;
  assert(list[j].pre == i && list[k].next == i);
  list[j].pre = k;
  list[k].next = j;
}

/*
 * Put element i back into the list
 */
static inline void idlatom_putback(idl_listelem_t *list, int32_t i) {
  int32_t j, k;

  j = list[i].next;
  k = list[i].pre;
  assert(list[j].pre == k && list[k].next == j);
  list[j].pre = i;
  list[k].next = i;
}


/*
 * Empty the list
 */
static inline void reset_idlatom_list(idl_listelem_t *list) {
  list[-1].next = -1;
  list[-1].pre = -1;
}


/*
 * First element of the list (-1 if the list is empty)
 */
static inline int32_t first_in_list(idl_listelem_t *list) {
  return list[-1].next;
}

/*
 * Successor of i in the list (-1 if i is the last element)
 */
static inline int32_t next_in_list(idl_listelem_t *list, int32_t i) {
  return list[i].next;
}



/*
 * Create a new atom: (x - y <= c)
 * returned value = the atom id
 * boolvar is initialized to null_bvar
 * the mark is cleared and the atom id is added to the free list
 */
static int32_t new_idl_atom(idl_atbl_t *table, int32_t x, int32_t y, int32_t c) {
  uint32_t i;

  i = table->natoms;
  if (i == table->size) {
    extend_idl_atbl(table);
  }
  assert(i < table->size);
  table->atoms[i].source = x;
  table->atoms[i].target = y;
  table->atoms[i].cost = c;
  table->atoms[i].boolvar = null_bvar;

  clr_bit(table->mark, i);
  idlatom_add_last(table->free_list, i);
  table->natoms ++;

  return i;
}


/*
 * Get atom descriptor for atom i
 */
static inline idl_atom_t *get_idl_atom(idl_atbl_t *table, int32_t i) {
  assert(0 <= i && i < table->natoms);
  return table->atoms + i;
}


/*
 * Check whether atom i is assigned (i.e., marked)
 */
static inline bool idl_atom_is_assigned(idl_atbl_t *table, int32_t i) {
  assert(0 <= i && i < table->natoms);
  return tst_bit(table->mark, i);
}


/*
 * Record that atom i is assigned: mark it, remove it from the free list
 * - i must not be marked
 */
static void mark_atom_assigned(idl_atbl_t *table, int32_t i) {
  assert(0 <= i && i < table->natoms && ! tst_bit(table->mark, i));
  set_bit(table->mark, i);
  idlatom_remove(table->free_list, i);
}


/*
 * Record that atom i is no longer assigned: clear its mark,
 * put it back into the free list
 */
static void mark_atom_unassigned(idl_atbl_t *table, int32_t i) {
  assert(0 <= i && i < table->natoms && tst_bit(table->mark, i));
  clr_bit(table->mark, i);
  idlatom_putback(table->free_list, i);
}




/*
 * Get the index of the first unassigned atom (-1 if all atoms are assigned)
 */
static inline int32_t first_unassigned_atom(idl_atbl_t *table) {
  return first_in_list(table->free_list);
}

/*
 * Next unassigned atom (-1 if i has no successor)
 *
 * Removing i from the list does not change its successor,
 * so we can do things like
 *   mark_atom_assigned(table, i);       // remove i from the list
 *   i = next_unassigned_atom(table, i); // still fine.
 */
static inline int32_t next_unassigned_atom(idl_atbl_t *table, int32_t i) {
  return next_in_list(table->free_list, i);
}


/*
 * Remove all atoms of index >= n
 */
static void restore_idl_atbl(idl_atbl_t *table, uint32_t n) {
  uint32_t i;

  assert(n <= table->natoms);

  // remove atoms from the free list
  for (i=n; i<table->natoms; i++) {
    if (! tst_bit(table->mark, i)) {
      idlatom_remove(table->free_list, i);
    }
  }
  table->natoms = n;
}


/*
 * Empty the table
 */
static inline void reset_idl_atbl(idl_atbl_t *table) {
  table->natoms = 0;
  reset_idlatom_list(table->free_list);
}


/*
 * Delete the table
 */
static inline void delete_idl_atbl(idl_atbl_t *table) {
  safe_free(table->atoms);
  safe_free(table->free_list - 1);
  delete_bitvector(table->mark);
  table->atoms = NULL;
  table->free_list = NULL;
  table->mark = NULL;
}




/**********************************
 *  ATOM STACK/PROPAGATION QUEUE  *
 *********************************/

/*
 * Initialize: n = initial size
 */
static void init_idl_astack(idl_astack_t *stack, uint32_t n) {
  assert(n < MAX_IDL_ASTACK_SIZE);
  stack->size = n;
  stack->top = 0;
  stack->prop_ptr = 0;
  stack->data = (int32_t *) safe_malloc(n * sizeof(int32_t));
}

/*
 * Make the stack 50% larger
 */
static void extend_idl_astack(idl_astack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n>>1;
  if (n >= MAX_IDL_ASTACK_SIZE) {
    out_of_memory();
  }

  stack->data = (int32_t *) safe_realloc(stack->data, n * sizeof(int32_t));
  stack->size = n;
}


/*
 * Usual encoding: atom id + sign bit are packed into a 32 bit integer index
 * - the sign is 0 for positive, 1 for negative
 * - pos_index(i) in the queue means that atom i is true
 * - neg_index(i) in the queue means that atom i is false
 */
static inline int32_t pos_index(int32_t id) {
  return id << 1;
}

static inline int32_t neg_index(int32_t id) {
  return (id<<1) | 1;
}

static inline int32_t mk_index(int32_t id, uint32_t sign) {
  assert(sign == 0 || sign == 1);
  return (id<<1) | sign;
}

static inline int32_t atom_of_index(int32_t idx) {
  return idx>>1;
}

static inline uint32_t sign_of_index(int32_t idx) {
  return ((uint32_t) idx) & 1;
}

static inline bool is_pos_index(int32_t idx) {
  return sign_of_index(idx) == 0;
}



/*
 * Push atom index k on top of the stack
 */
static void push_atom_index(idl_astack_t *stack, int32_t k) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_idl_astack(stack);
  }
  assert(i < stack->size);
  stack->data[i] = k;
  stack->top = i+1;
}


/*
 * Empty the stack
 */
static inline void reset_idl_astack(idl_astack_t *stack) {
  stack->top = 0;
  stack->prop_ptr = 0;
}


/*
 * Delete the stack
 */
static inline void delete_idl_astack(idl_astack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}



/****************
 *  UNDO STACK  *
 ***************/

/*
 * There's an undo record for each decision level. The record stores
 * - edge_id = first edge created at the decision level
 * - nsaved = number of saved cells in the graph when the decision
 *   level was entered
 * - natoms = number of atoms in the propagation queue when the
 *   decision level was entered.
 *
 * The records are stored in stack->data[0 ... top-1] so top should
 * always be equal to decision_level + 1.
 *
 * The initial record for decision level 0 must be initialized with
 * - number of edges = -1
 * - number of saved cells = 0
 * - number of atoms = 0
 */

/*
 * Initialize: n = size
 */
static void init_idl_undo_stack(idl_undo_stack_t *stack, uint32_t n) {
  assert(n < MAX_IDL_UNDO_STACK_SIZE);

  stack->size = n;
  stack->top = 0;
  stack->data = (idl_undo_record_t *) safe_malloc(n * sizeof(idl_undo_record_t));
}

/*
 * Extend the stack: make it 50% larger
 */
static void extend_idl_undo_stack(idl_undo_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n>>1;
  if (n >= MAX_IDL_UNDO_STACK_SIZE) {
    out_of_memory();
  }
  stack->size = n;
  stack->data = (idl_undo_record_t *) safe_realloc(stack->data, n * sizeof(idl_undo_record_t));
}


/*
 * Push record (e, c, a) on top of the stack
 * - e = top edge id
 * - c = top of the saved cell stack
 * - a = top of the atom stack
 */
static void push_undo_record(idl_undo_stack_t *stack, int32_t e, uint32_t c, uint32_t a) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_idl_undo_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i].edge_id = e;
  stack->data[i].nsaved = c;
  stack->data[i].natoms = a;
  stack->top = i+1;
}


/*
 * Get the top record
 */
static inline idl_undo_record_t *idl_undo_stack_top(idl_undo_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}


/*
 * Empty the stack
 */
static inline void reset_idl_undo_stack(idl_undo_stack_t *stack) {
  stack->top = 0;
}

/*
 * Delete the stack
 */
static inline void delete_idl_undo_stack(idl_undo_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}



/********************
 *  PUSH/POP STACK  *
 *******************/

/*
 * Initialize: size = 0;
 */
static void init_idl_trail_stack(idl_trail_stack_t *stack) {
  stack->size = 0;
  stack->top = 0;
  stack->data = NULL;
}


/*
 * Save data for the current base_level:
 * - nv = number of vertices
 * - na = number of atoms
 */
static void idl_trail_stack_save(idl_trail_stack_t *stack, uint32_t nv, uint32_t na) {
  uint32_t i, n;

  i = stack->top;
  n = stack->size;
  if (i == n) {
    if (n == 0) {
      n = DEFAULT_IDL_TRAIL_SIZE;
    } else {
      n += n>>1; // 50% larger
      if (n >= MAX_IDL_TRAIL_SIZE) {
        out_of_memory();
      }
    }
    stack->data = (idl_trail_t *) safe_realloc(stack->data, n * sizeof(idl_trail_t));
    stack->size = n;
  }
  assert(i < n);
  stack->data[i].nvertices = nv;
  stack->data[i].natoms = na;
  stack->top = i+1;
}


/*
 * Get the top record
 */
static inline idl_trail_t *idl_trail_stack_top(idl_trail_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}


/*
 * Remove the top record
 */
static inline void idl_trail_stack_pop(idl_trail_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}


/*
 * Empty the stack
 */
static inline void reset_idl_trail_stack(idl_trail_stack_t *stack) {
  stack->top = 0;
}


/*
 * Delete the stack
 */
static inline void delete_idl_trail_stack(idl_trail_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}




/*********************
 *  VERTEX CREATION  *
 ********************/

/*
 * Create a new vertex and return its index
 */
int32_t idl_new_vertex(idl_solver_t *solver) {
  uint32_t n;

  n = solver->nvertices;
  if (n >= MAX_IDL_VERTICES) {
    return null_idl_vertex;
  }
  solver->nvertices = n + 1;
  return n;
}


/*
 * Get the zero vertex (create a new vertex if needed)
 */
int32_t idl_zero_vertex(idl_solver_t *solver) {
  int32_t z;

  z = solver->zero_vertex;
  if (z == null_idl_vertex) {
    z = idl_new_vertex(solver);
    solver->zero_vertex = z;
  }
  return z;
}





/***************************
 *  HASH-CONSING OF ATOMS  *
 **************************/

/*
 * Hash code for atom (x - y <= d)
 */
static inline uint32_t hash_idl_atom(int32_t x, int32_t y, int32_t d) {
  return jenkins_hash_triple(x, y, d, 0xa27def15);
}


/*
 * Hash consing object for interfacing with int_hash_table
 */
typedef struct idlatom_hobj_s {
  int_hobj_t m;     // methods
  idl_atbl_t *atbl; // atom table
  int32_t source, target, cost; // atom components
} idlatom_hobj_t;


/*
 * Functions for int_hash_table
 */
static uint32_t hash_atom(idlatom_hobj_t *p) {
  return hash_idl_atom(p->source, p->target, p->cost);
}

static bool equal_atom(idlatom_hobj_t *p, int32_t id) {
  idl_atom_t *atm;

  atm = get_idl_atom(p->atbl, id);
  return atm->source == p->source && atm->target == p->target && atm->cost == p->cost;
}

static int32_t build_atom(idlatom_hobj_t *p) {
  return new_idl_atom(p->atbl, p->source, p->target, p->cost);
}

/*
 * Atom constructor: use hash consing
 * - if the atom is new, create a fresh boolean variable v
 *   and the atom index to v in the core
 */
static bvar_t bvar_for_atom(idl_solver_t *solver, int32_t x, int32_t y, int32_t d) {
  int32_t id;
  idl_atom_t *atm;
  bvar_t v;
  idlatom_hobj_t atom_hobj;

  atom_hobj.m.hash = (hobj_hash_t) hash_atom;
  atom_hobj.m.eq = (hobj_eq_t) equal_atom;
  atom_hobj.m.build = (hobj_build_t) build_atom;
  atom_hobj.atbl = &solver->atoms;
  atom_hobj.source = x;
  atom_hobj.target = y;
  atom_hobj.cost = d;
  id = int_htbl_get_obj(&solver->htbl, (int_hobj_t *) &atom_hobj);
  atm = get_idl_atom(&solver->atoms, id);
  v = atm->boolvar;
  if (v == null_bvar) {
    v = create_boolean_variable(solver->core);
    atm->boolvar = v;
    attach_atom_to_bvar(solver->core, v, index2atom(id));
  }
  return v;
}


/*
 * Get literal for atom (x - y <= d): simplify and normalize first
 */
literal_t idl_make_atom(idl_solver_t *solver, int32_t x, int32_t y, int32_t d) {
  assert(0 <= x && x < solver->nvertices && 0 <= y && y < solver->nvertices);

#if TRACE
  printf("---> IDL: creating atom: ");
  print_idl_vertex(stdout, x);
  printf(" - ");
  print_idl_vertex(stdout, y);
  printf(" <= %"PRId32"\n", d);
  if (x == y) {
    if (d >= 0) {
      printf("---> true atom\n");
    } else {
      printf("---> false atom\n");
    }
  }
#endif

  if (x == y) {
    return (d >= 0) ? true_literal : false_literal;
  }

  // EXPERIMENTAL
  if (solver->base_level == solver->decision_level &&
      x < solver->graph.matrix.dim && y < solver->graph.matrix.dim) {
    idl_cell_t *cell;

    cell = idl_cell(&solver->graph.matrix, x, y);
    if (cell->id >= 0 && cell->dist <= d) {
#if TRACE
      printf("---> true atom: dist[");
      print_idl_vertex(stdout, x);
      printf(", ");
      print_idl_vertex(stdout, y);
      printf("] = %"PRId32"\n",  cell->dist);
#endif
      return true_literal;
    }
    cell = idl_cell(&solver->graph.matrix, y, x);
    if (cell->id >= 0 && cell->dist < -d) {
#if TRACE
      printf("---> false atom: dist[");
      print_idl_vertex(stdout, y);
      printf(", ");
      print_idl_vertex(stdout, x);
      printf("] = %"PRId32"\n",  cell->dist);
#endif
      return false_literal;
    }
  }

  return pos_lit(bvar_for_atom(solver, x, y, d));

#if 0
  if (x < y) {
    return pos_lit(bvar_for_atom(solver, x, y, d));
  } else {
    // (x - y <= d) <==> (not [y - x <= -d-1])
    return neg_lit(bvar_for_atom(solver, y, x, - d - 1));
  }
#endif

}









/****************
 *  ASSERTIONS  *
 ***************/

/*
 * Assert (x - y <= d) as an axiom:
 * - attach true_literal to the edge
 */
void idl_add_axiom_edge(idl_solver_t *solver, int32_t x, int32_t y, int32_t d) {
  idl_cell_t *cell;
  int32_t k;

  assert(0 <= x && x < solver->nvertices && 0 <= y && y < solver->nvertices);
  assert(solver->decision_level == solver->base_level);

  // do nothing if the solver is already in an inconsistent state
  if (solver->unsat_before_search) return;

  resize_idl_graph(&solver->graph, solver->nvertices);

  // check whether adding the edge x--->y forms a negative circuit
  cell = idl_cell(&solver->graph.matrix, y, x);
  if (cell->id >= 0 && cell->dist + d < 0) {
    solver->unsat_before_search = true;
    return;
  }

  // check whether the new axiom is redundant
  cell = idl_cell(&solver->graph.matrix, x, y);
  if (cell->id >= 0 && cell->dist <= d) {
    return;
  }

  /*
   * save limit for add_edge:
   * k = top edge id stored in the top record of the undo stack
   * if base level == 0, k = -1, so nothing will be saved
   */
  assert(solver->stack.top == solver->decision_level + 1);
  k = idl_undo_stack_top(&solver->stack)->edge_id;

  // add the edge
  idl_graph_add_edge(&solver->graph, x, y, d, true_literal, k);
}


/*
 * Assert (x - y == d) as an axiom: (x - y <= d && y - x <= -d)
 */
void idl_add_axiom_eq(idl_solver_t *solver, int32_t x, int32_t y, int32_t d) {
  idl_add_axiom_edge(solver, x, y, d);
  idl_add_axiom_edge(solver, y, x, -d);
}


/*
 * Try to assert (x - y <= d) with explanation l
 * - if that causes a conflict, generate the conflict explanation and return false
 * - return true if the edge does not cause a conflict
 * The graph matrix must have dimension == solver->nvertices
 */
static bool idl_add_edge(idl_solver_t *solver, int32_t x, int32_t y, int32_t d, literal_t l) {
  idl_cell_t *cell;
  int32_t k;
  uint32_t i, n;
  ivector_t *v;

  assert(0 <= x && x < solver->nvertices && 0 <= y && y < solver->nvertices);

  // check whether the new edge causes a negative circuit
  cell = idl_cell(&solver->graph.matrix, y, x);
  if (cell->id >= 0 && cell->dist + d < 0) {
    v = &solver->expl_buffer;
    ivector_reset(v);
    idl_graph_explain_path(&solver->graph, y, x, v);
    ivector_push(v, l);
    /*
     * the conflict is not (v[0] ... v[n-1])
     * we need to convert it to a clause and add the end marker
     */
    n = v->size;
    for (i=0; i<n; i++) {
      v->data[i] = not(v->data[i]);
    }
    ivector_push(v, null_literal); // end marker
    record_theory_conflict(solver->core, v->data);

    return false;
  }

  cell = idl_cell(&solver->graph.matrix, x, y);
  if (cell->id < 0 || cell->dist > d) {
    /*
     * The edge is not redundant: add it to the graph
     * backtrack point = number of edges on entry to the current decision level
     * that's stored in the top element in the undo stack
     */
    assert(solver->stack.top == solver->decision_level + 1);
    k = idl_undo_stack_top(&solver->stack)->edge_id;
    idl_graph_add_edge(&solver->graph, x, y, d, l, k);
  }
  return true;
}





/**************************
 *   THEORY PROPAGATION   *
 *************************/

/*
 * Generate a propagation antecedent using the path x --> y
 * - return a pointer to a literal array, terminated by null_literal
 */
static literal_t *gen_idl_prop_antecedent(idl_solver_t *solver, int32_t x, int32_t y) {
  ivector_t *v;
  literal_t *expl;
  uint32_t i, n;

  v = &solver->expl_buffer;
  ivector_reset(v);
  idl_graph_explain_path(&solver->graph, x, y, v);

  // copy v + end marker into the arena
  n = v->size;
  expl = (literal_t *) arena_alloc(&solver->arena, (n + 1) * sizeof(int32_t));
  for (i=0; i<n; i++) {
    expl[i] = v->data[i];
  }
  expl[i] = null_literal;

  return expl;
}


/*
 * Check whether atom i (or its negation) is implied by the graph
 * - if so, propagate the literal to the core
 * - add the atom index to the propagation queue
 *   (this is required for backtracking)
 */
static void check_atom_for_propagation(idl_solver_t *solver, int32_t i) {
  idl_atom_t *a;
  int32_t x, y, d;
  idl_cell_t *cell;
  literal_t *expl;

  assert(! idl_atom_is_assigned(&solver->atoms, i));

  a = get_idl_atom(&solver->atoms, i);
  x = a->source;
  y = a->target;
  d = a->cost;

  cell = idl_cell(&solver->graph.matrix, x, y);
  if (cell->id >= 0 && cell->dist <= d) {
    // d[x, y] <= d so x - y <= d is implied
    expl = gen_idl_prop_antecedent(solver, x, y);
    mark_atom_assigned(&solver->atoms, i);
    push_atom_index(&solver->astack, pos_index(i));
    propagate_literal(solver->core, pos_lit(a->boolvar), expl);
#if TRACE
    printf("---> IDL propagation: ");
    print_idl_atom(stdout, a);
    printf(" is true: dist[");
    print_idl_vertex(stdout, x);
    printf(", ");
    print_idl_vertex(stdout, y);
    printf("] = %"PRId32"\n", cell->dist);
#endif
    return;
  }

  cell = idl_cell(&solver->graph.matrix, y, x);
  if (cell->id >= 0 && cell->dist < -d) {
    // we have y - x <= d[y, x] < -d so x - y > d is implied
    expl = gen_idl_prop_antecedent(solver, y, x);
    mark_atom_assigned(&solver->atoms, i);
    push_atom_index(&solver->astack, neg_index(i));
    propagate_literal(solver->core, neg_lit(a->boolvar), expl);
#if TRACE
    printf("---> IDL propagation: ");
    print_idl_atom(stdout, a);
    printf(" is false: dist[");
    print_idl_vertex(stdout, y);
    printf(", ");
    print_idl_vertex(stdout, x);
    printf("] = %"PRId32"\n", cell->dist);
#endif
  }
}



/*
 * Scan all unassigned atoms and check propagation
 * - must be called after all atoms in the queue have been processed
 */
static void idl_atom_propagation(idl_solver_t *solver) {
  idl_atbl_t *tbl;
  int32_t i;

  assert(solver->astack.top == solver->astack.prop_ptr);

  tbl = &solver->atoms;
  for (i=first_unassigned_atom(tbl); i >= 0; i = next_unassigned_atom(tbl, i)) {
    check_atom_for_propagation(solver, i);
  }

  // update prop_ptr to skip all implied atoms in the next
  // call to idl_propagate.
  solver->astack.prop_ptr = solver->astack.top;
}



/********************
 *  SMT OPERATIONS  *
 *******************/

/*
 * Start internalization: do nothing
 */
void idl_start_internalization(idl_solver_t *solver) {
}


/*
 * Start search: if unsat flag is true, force a conflict in the core.
 * Otherwise, do nothing.
 */
void idl_start_search(idl_solver_t *solver) {
  if (solver->unsat_before_search) {
    record_empty_theory_conflict(solver->core);
  }
}


/*
 * Start a new decision level:
 * - save the current number of edges and saved cells,
 *   and the size of the atom queue
 */
void idl_increase_decision_level(idl_solver_t *solver) {
  uint32_t e, c, a;

  assert(! solver->unsat_before_search);
  assert(solver->astack.top == solver->astack.prop_ptr);

  e = idl_graph_num_edges(&solver->graph);
  c = idl_graph_num_cells(&solver->graph);
  a = solver->astack.top;
  push_undo_record(&solver->stack, e, c, a);
  solver->decision_level ++;

  // open new scope in the arena (for storing propagation antecedents)
  arena_push(&solver->arena);
}



/*
 * Assert atom:
 * - a stores the index of an atom attached to a boolean variable v
 * - l is either pos_lit(v) or neg_lit(v)
 * - pos_lit means assert atom (x - y <= c)
 * - neg_lit means assert its negation (y - x <= -c-1)
 * We just push the corresponding atom index onto the propagation queue
 */
bool idl_assert_atom(idl_solver_t *solver, void *a, literal_t l) {
  int32_t k;

  k = atom2index(a);
  assert(var_of(l) == get_idl_atom(&solver->atoms, k)->boolvar);

  if (! idl_atom_is_assigned(&solver->atoms, k)) {
    mark_atom_assigned(&solver->atoms, k);
    push_atom_index(&solver->astack, mk_index(k, sign_of_lit(l)));
  }

  return true;
}


/*
 * Process all asserted atoms then propagate implied atoms to the core
 */
bool idl_propagate(idl_solver_t *solver) {
  uint32_t i, n;
  int32_t k, *a;
  int32_t x, y, d;
  literal_t l;
  idl_atom_t *atom;

  resize_idl_graph(&solver->graph, solver->nvertices);

  a = solver->astack.data;
  n = solver->astack.top;
  for (i=solver->astack.prop_ptr; i<n; i++) {
    k = a[i];
    atom = get_idl_atom(&solver->atoms, atom_of_index(k));
    // turn atom or its negation into (x - y <= d)
    if (is_pos_index(k)) {
      x = atom->source;
      y = atom->target;
      d = atom->cost;
      l = pos_lit(atom->boolvar);
    } else {
      x = atom->target;
      y = atom->source;
      d = - atom->cost - 1;
      l = neg_lit(atom->boolvar);
    }

    if (! idl_add_edge(solver, x, y, d, l)) return false; // conflict
  }

  solver->astack.prop_ptr = n;

  assert(valid_idl_graph(&solver->graph));

  // theory propagation
  idl_atom_propagation(solver);

  return true;
}


/*
 * Final check: do nothing and return SAT
 */
fcheck_code_t idl_final_check(idl_solver_t *solver) {
  return FCHECK_SAT;
}


/*
 * Clear: do nothing
 */
void idl_clear(idl_solver_t *solver) {
}


/*
 * Expand explanation for literal l
 * - l was implied with expl as antecedent
 * - expl is a null-terminated array of literals stored in the arena.
 * - v = vector where the explanation is to be added
 */
void idl_expand_explanation(idl_solver_t *solver, literal_t l, literal_t *expl, ivector_t *v) {
  literal_t x;

  for (;;) {
    x = *expl ++;
    if (x == null_literal) break;
    ivector_push(v, x);
  }
}


/*
 * Backtrack to back_level
 */
void idl_backtrack(idl_solver_t *solver, uint32_t back_level) {
  idl_undo_record_t *undo;
  uint32_t i, n;
  int32_t k, *a;

  assert(solver->base_level <= back_level && back_level < solver->decision_level);

  /*
   * stack->data[back_level+1] = undo record created on entry to back_level + 1
   */
  assert(back_level + 1 < solver->stack.top);
  undo = solver->stack.data + back_level + 1;
  // remove all edges of level >= back_level + 1
  idl_graph_remove_edges(&solver->graph, undo->edge_id, undo->nsaved);

  /*
   * all atoms assigned at levels > back_level must be put back into the free list
   * this must be done in reverse order of atom processing
   */
  n = undo->natoms;
  i = solver->astack.top;
  a = solver->astack.data;
  while (i > n) {
    i --;
    k = atom_of_index(a[i]);
    mark_atom_unassigned(&solver->atoms, k);
  }
  solver->astack.top = n;
  solver->astack.prop_ptr = n;

  /*
   * Delete all temporary data in the arena
   */
  i = solver->decision_level;
  do {
    arena_pop(&solver->arena);
    i --;
  } while (i > back_level);

  /*
   * Restore the undo stack and decision_level
   */
  solver->stack.top = back_level + 1;
  solver->decision_level = back_level;

  assert(valid_idl_graph(&solver->graph));
}





/*
 * Push:
 * - store current number of vertices and atoms on the trail_stack
 * - increment both decision level and base level
 */
void idl_push(idl_solver_t *solver) {
  assert(solver->base_level == solver->decision_level);

  dl_vartable_push(&solver->vtbl);
  idl_trail_stack_save(&solver->trail_stack, solver->nvertices, solver->atoms.natoms);
  solver->base_level ++;
  idl_increase_decision_level(solver);
  assert(solver->decision_level == solver->base_level);
}


/*
 * Pop: remove vertices and atoms created at the current base-level
 */
void idl_pop(idl_solver_t *solver) {
  idl_trail_t *top;
  uint32_t i, h, n, p;
  idl_atom_t *a;

  assert(solver->base_level > 0 && solver->base_level == solver->decision_level);
  top = idl_trail_stack_top(&solver->trail_stack);

  // remove variables
  dl_vartable_pop(&solver->vtbl);

  // remove atoms from the hash table
  p = top->natoms;
  n = solver->atoms.natoms;
  for (i = p; i<n; i++) {
    a = get_idl_atom(&solver->atoms, i);
    h = hash_idl_atom(a->source, a->target, a->cost);
    int_htbl_erase_record(&solver->htbl, h, i);
  }

  // remove atoms from the atom table
  restore_idl_atbl(&solver->atoms, n);

  // restore vertice count
  solver->nvertices = top->nvertices;
  resize_idl_matrix(&solver->graph.matrix, top->nvertices);

  // decrement base_level
  solver->base_level --;
  idl_trail_stack_pop(&solver->trail_stack);

  // backtrack to base_level
  idl_backtrack(solver, solver->base_level);

  assert(valid_idl_graph(&solver->graph));
}


/*
 * Reset
 */
void idl_reset(idl_solver_t *solver) {
  solver->base_level = 0;
  solver->decision_level = 0;
  solver->unsat_before_search = false;

  reset_dl_vartable(&solver->vtbl);

  solver->nvertices = 0;
  solver->zero_vertex = null_idl_vertex;
  reset_idl_graph(&solver->graph);

  reset_idl_atbl(&solver->atoms);
  reset_idl_astack(&solver->astack);
  reset_idl_undo_stack(&solver->stack);
  reset_idl_trail_stack(&solver->trail_stack);

  reset_int_htbl(&solver->htbl);
  arena_reset(&solver->arena);
  ivector_reset(&solver->expl_buffer);
  ivector_reset(&solver->aux_vector);

  solver->triple.target = nil_vertex;
  solver->triple.source = nil_vertex;
  q_clear(&solver->triple.constant);
  reset_poly_buffer(&solver->buffer);

  if (solver->value != NULL) {
    safe_free(solver->value);
    solver->value = NULL;
  }

  // undo record for level 0
  push_undo_record(&solver->stack, -1, 0, 0);

}



/*
 * THEORY-BRANCHING
 */

/*
 * We compute a variable assignment using vertex 0 as a reference
 * using val[x] = - d[0, x].
 * To decide whether to case-split (x - y <= b) = true or false
 * we check whether val[x] - val[y] <= b.
 */
literal_t idl_select_polarity(idl_solver_t *solver, void *a, literal_t l) {
  bvar_t v;
  int32_t id;
  idl_atom_t *atom;
  int32_t x, y;
  idl_cell_t *cell_x, *cell_y;

  v = var_of(l);
  id = atom2index(a);
  atom = get_idl_atom(&solver->atoms, id);
  assert(atom->boolvar == v);

  x = atom->source;
  y = atom->target;
  cell_x = idl_cell(&solver->graph.matrix, 0, x);
  cell_y = idl_cell(&solver->graph.matrix, 0, y);
  if (cell_x->id >= 0 && cell_y->id >= 0) {
    /*
     * d[0, x] and d[0, y] are defined:
     * val[x] - val[y] <= b iff d[0, y] - d[0, x] <= b
     */
    if (cell_y->dist - cell_x->dist <= atom->cost) {
      return pos_lit(v);
    } else {
      return neg_lit(v);
    }
  } else {
    return l;
  }
}



/**********************
 *  INTERNALIZATION   *
 *********************/

/*
 * Raise exception or abort
 */
static __attribute__ ((noreturn)) void idl_exception(idl_solver_t *solver, int code) {
  if (solver->env != NULL) {
    longjmp(*solver->env, code);
  }
  abort();
}


/*
 * Store a triple (x, y, c) into the internal triple
 * create/get the corresponding variable from vtbl.
 * - x = target vertex
 * - y = source vertex
 * - c = constant
 * This returns a variable id whose descriptor is (x - y + c).
 */
static thvar_t idl_var_for_triple(idl_solver_t *solver, int32_t x, int32_t y, int32_t c) {
  dl_triple_t *triple;

  triple = &solver->triple;
  triple->target = x;
  triple->source = y;
  q_set32(&triple->constant, c);

  return get_dl_var(&solver->vtbl, triple);
}



/*
 * Apply renaming and substitution to polynomial p
 * - map is a variable renaming: if p is a_0 t_0 + ... + a_n t_n
 *   then map[i] is the theory variable x_i that replaces t_i.
 * - so the function construct p = a_0 x_0 + ... + a_n x_n
 * The result is stored into solver->buffer.
 */
static void idl_rename_poly(idl_solver_t *solver, polynomial_t *p, thvar_t *map) {
  poly_buffer_t *b;
  monomial_t *mono;
  uint32_t i, n;

  b = &solver->buffer;
  reset_poly_buffer(b);

  n = p->nterms;
  mono = p->mono;

  // deal with p's constant term if any
  if (n > 0 && map[0] == null_thvar) {
    assert(mono[0].var == const_idx);
    poly_buffer_add_const(b, &mono[0].coeff);
    n --;
    map ++;
    mono ++;
  }

  for (i=0; i<n; i++) {
    assert(mono[i].var != const_idx);
    addmul_dl_var_to_buffer(&solver->vtbl, b, map[i], &mono[i].coeff);
  }

  normalize_poly_buffer(b);
}



/*
 * Create the zero_vertex but raise an exception if that fails.
 */
static int32_t idl_get_zero_vertex(idl_solver_t *solver) {
  int32_t z;

  z = idl_zero_vertex(solver);
  if (z < 0) {
    idl_exception(solver, TOO_MANY_ARITH_VARS);
  }
  return z;
}


/*
 * Create the atom (x - y + c) == 0 for d = (x - y + c)
 */
static literal_t idl_eq_from_triple(idl_solver_t *solver, dl_triple_t *d) {
  literal_t l1, l2;
  int32_t c, x, y;

  x = d->target;
  y = d->source;

  /*
   * Check for trivial equality: we do this before attempting
   * to  convert the constant to int32.
   */
  if (x == y) {
    if (q_is_zero(&d->constant)) {
      return true_literal;
    } else {
      return false_literal;
    }
  }

  if (! q_get32(&d->constant, &c)) {
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  /*
   * d is (x - y + c)
   */

  // a nil_vertex in triples denote 'zero'
  if (x < 0) {
    x = idl_get_zero_vertex(solver);
  } else if (y < 0) {
    y = idl_get_zero_vertex(solver);
  }

  // v == 0 is the conjunction of (y - x <= c) and (x - y <= -c)
  if (c == INT32_MIN) {
    // we can't represent -c
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  l1 = idl_make_atom(solver, y, x, c);  // atom (y - x <= c)
  l2 = idl_make_atom(solver, x, y, -c); // atom (x - y <= -c)
  return mk_and_gate2(solver->gate_manager, l1, l2);
}


/*
 * Create the atom (x - y + c) >= 0 for d = (x - y + c)
 */
static literal_t idl_ge_from_triple(idl_solver_t *solver, dl_triple_t *d) {
  int32_t c, x, y;

  x = d->target;
  y = d->source;

  /*
   * Trivial case: don't convert the constant to int32
   */
  if (x == y) {
    if (q_is_nonneg(&d->constant)) {
      return true_literal;
    } else {
      return false_literal;
    }
  }

  if (! q_get32(&d->constant, &c)) {
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  if (x < 0) {
    x = idl_get_zero_vertex(solver);
  } else if (y < 0) {
    y = idl_get_zero_vertex(solver);
  }

  // (x - y + c >= 0) is (y - x <= c)
  return idl_make_atom(solver, y, x, c);
}


/*
 * Assert (x - y + c) == 0 or (x - y + c) != 0, given a triple d = x - y + c
 * - tt true: assert the equality
 * - tt false: assert the disequality
 */
static void idl_assert_triple_eq(idl_solver_t *solver, dl_triple_t *d, bool tt) {
  int32_t x, y, c;
  literal_t l1, l2;

  x = d->target;
  y = d->source;

  if (x == y) {
    // trivial case
    if (q_is_zero(&d->constant) != tt) {
      solver->unsat_before_search = true;
    }
    return;
  }

  if (! q_get32(&d->constant, &c)) {
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  // d is (x - y + c)
  if (x < 0) {
    x = idl_get_zero_vertex(solver);
  } else if (y < 0) {
    y = idl_get_zero_vertex(solver);
  }

  if (tt) {
    // (x - y + c) == 0 is equivalent to y - x == c
    idl_add_axiom_eq(solver, y, x, c);
  } else {
    // (x - y + c) != 0 is equivalent to
    // (not (y - x <= c)) or (not (x - y <= -c))
    if (c == INT32_MIN) {
      idl_exception(solver, ARITHSOLVER_EXCEPTION);
    }

    l1 = idl_make_atom(solver, y, x, c);   // atom (y - x <= c)
    l2 = idl_make_atom(solver, x, y, -c);  // atom (x - y <= -c)
    add_binary_clause(solver->core, not(l1), not(l2));
  }
}


/*
 * Assert (x - y + c) >= 0 or (x - y + c) < 0, given a triple d = x - y + c
 * - tt true: assert  (x - y + c) >= 0
 * - tt false: assert (x - y + c) < 0
 */
static void idl_assert_triple_ge(idl_solver_t *solver, dl_triple_t *d, bool tt) {
  int32_t x, y, c;

  x = d->target;
  y = d->source;

  if (x == y) {
    // trivial case
    if (q_is_nonneg(&d->constant) != tt) {
      solver->unsat_before_search = true;
    }
    return;
  }

  if (! q_get32(&d->constant, &c)) {
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }
  // d is (x - y + c)

  if (x < 0) {
    x = idl_get_zero_vertex(solver);
  } else if (y < 0) {
    y = idl_get_zero_vertex(solver);
  }

  if (tt) {
    // (x - y + c) >= 0 is equivalent to (y - x <= c)
    idl_add_axiom_edge(solver, y, x, c);
  } else {
    // (x - y + c) < 0 is equivalent to (x - y <= -c-1)
    // Note: (-c)-1 gives the right result even if c is INT32_MIN
    idl_add_axiom_edge(solver, x, y, -c-1);
  }
}


/*
 * TERM CONSTRUCTORS
 */

/*
 * Create a new theory variable
 * - is_int indicates whether the variable should be an integer,
 *   so it should always be true for this solver.
 * - raise exception NOT_IDL if is_int is false
 * - raise exception TOO_MANY_VARS if we can't create a new vertex
 *   for that variable
 */
thvar_t idl_create_var(idl_solver_t *solver, bool is_int) {
  int32_t v;

  if (! is_int) {
    idl_exception(solver, FORMULA_NOT_IDL);
  }

  v = idl_new_vertex(solver);
  if (v < 0) {
    idl_exception(solver, TOO_MANY_ARITH_VARS);
  }

  return idl_var_for_triple(solver, v, nil_vertex, 0);
}


/*
 * Create a variable that represents the constant q
 * - fails if q is not an integer
 */
thvar_t idl_create_const(idl_solver_t *solver, rational_t *q) {
  int32_t c;

  if (! q_get32(q, &c)) {
    /*
     * We could do a more precise diagnosis here:
     * There are two possibilities:
     * q is not an integer
     * q is an integer but it doesn't fit in 32bits
     */
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  return idl_var_for_triple(solver, nil_vertex, nil_vertex, c);
}


/*
 * Create a variable for a polynomial p, with variables defined by map:
 * - p is of the form a_0 t_0 + ... + a_n t_n where t_0, ..., t_n
 *   are arithmetic terms.
 * - map[i] is the theory variable x_i for t_i
 *   (with map[0] = null_thvar if t_0 is const_idx)
 * - the function constructs a variable equal to a_0 x_0 + ... + a_n x_n
 *
 * - fails if a_0 x_0 + ... + a_n x_n is not an IDL polynomial
 *   (i.e., not of the form x - y + c)
 */
thvar_t idl_create_poly(idl_solver_t *solver, polynomial_t *p, thvar_t *map) {
  poly_buffer_t *b;
  dl_triple_t *triple;

  // apply renaming and substitutions
  idl_rename_poly(solver, p, map);
  b = &solver->buffer;

  // b contains a_0 x_0 + ... + a_n x_n
  triple = &solver->triple;
  if (! convert_poly_buffer_to_dl_triple(b, triple) ||
      ! q_is_int32(&triple->constant)) {
    /*
     * Exception here: either b is not of the right form
     * or the constant is not an integer
     * or the constant is an integer but it doesn't fit in 32bits
     */
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  return get_dl_var(&solver->vtbl, triple);
}


/*
 * Internalization for a product: always fails with NOT_IDL exception
 */
thvar_t idl_create_pprod(idl_solver_t *solver, pprod_t *p, thvar_t *map) {
  idl_exception(solver, FORMULA_NOT_IDL);
}



/*
 * ATOM CONSTRUCTORS
 */

/*
 * Create the atom v = 0
 */
literal_t idl_create_eq_atom(idl_solver_t *solver, thvar_t v) {
  return idl_eq_from_triple(solver, dl_var_triple(&solver->vtbl, v));
}


/*
 * Create the atom v >= 0
 */
literal_t idl_create_ge_atom(idl_solver_t *solver, thvar_t v) {
  return idl_ge_from_triple(solver, dl_var_triple(&solver->vtbl, v));
}


/*
 * Create the atom (v = w)
 */
literal_t idl_create_vareq_atom(idl_solver_t *solver, thvar_t v, thvar_t w) {
  dl_triple_t *triple;

  triple = &solver->triple;
  if (! diff_dl_vars(&solver->vtbl, v, w, triple)) {
    // v - w is not expressible as (target - source + c)
    idl_exception(solver, FORMULA_NOT_IDL);
  }

  return idl_eq_from_triple(solver, triple);
}


/*
 * Create the atom (p = 0)
 * - map = variable renaming (as in create_poly)
 */
literal_t idl_create_poly_eq_atom(idl_solver_t *solver, polynomial_t *p, thvar_t *map) {
  poly_buffer_t *b;
  dl_triple_t *triple;

  // apply renaming and substitutions
  idl_rename_poly(solver, p, map);

  b = &solver->buffer;
  triple = &solver->triple;
  if (! rescale_poly_buffer_to_dl_triple(b, triple)) {
    // exception: p is not convertible to an IDL polynomial
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  return idl_eq_from_triple(solver, triple);
}



/*
 * Create the atom (p >= 0)
 * - map = variable renaming (as in create_poly)
 */
literal_t idl_create_poly_ge_atom(idl_solver_t *solver, polynomial_t *p, thvar_t *map) {
  poly_buffer_t *b;
  dl_triple_t *triple;

  // apply renaming and substitutions
  idl_rename_poly(solver, p, map);

  b = &solver->buffer;
  triple = &solver->triple;
  if (! rescale_poly_buffer_to_dl_triple(b, triple)) {
    // exception: either p is not convertible to an IDL polynomial
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  return idl_ge_from_triple(solver, triple);
}




/*
 * TOP-LEVEL ASSERTIONS
 */

/*
 * Assert the top-level constraint (v == 0) or (v != 0)
 * - if tt is true: assert v == 0
 * - if tt is false: assert v != 0
 */
void idl_assert_eq_axiom(idl_solver_t *solver, thvar_t v, bool tt) {
  idl_assert_triple_eq(solver, dl_var_triple(&solver->vtbl, v), tt);
}


/*
 * Assert the top-level constraint (v >= 0) or (v < 0)
 * - if tt is true: assert (v >= 0)
 * - if tt is false: assert (v < 0)
 */
void idl_assert_ge_axiom(idl_solver_t *solver, thvar_t v, bool tt) {
  idl_assert_triple_ge(solver, dl_var_triple(&solver->vtbl, v), tt);
}


/*
 * Assert (p == 0) or (p != 0) depending on tt
 */
void idl_assert_poly_eq_axiom(idl_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt) {
  poly_buffer_t *b;
  dl_triple_t *triple;

  // apply renaming and substitutions
  idl_rename_poly(solver, p, map);

  b = &solver->buffer;
  triple = &solver->triple;
  if (! rescale_poly_buffer_to_dl_triple(b, triple)) {
    // exception: p is not convertible to an IDL polynomial
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  idl_assert_triple_eq(solver, triple, tt);
}


/*
 * Assert (p >= 0) or (p < 0) depending on tt
 */
void idl_assert_poly_ge_axiom(idl_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt) {
  poly_buffer_t *b;
  dl_triple_t *triple;

  // apply renaming and substitutions
  idl_rename_poly(solver, p, map);

  b = &solver->buffer;
  triple = &solver->triple;
  if (! rescale_poly_buffer_to_dl_triple(b, triple)) {
    // exception:  p is not convertible to an IDL polynomial
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  idl_assert_triple_ge(solver, triple, tt);
}



/*
 * Assert (v == w) or (v != w)
 * - if tt is true: assert (v == w)
 * - if tt is false: assert (v != w)
 */
void idl_assert_vareq_axiom(idl_solver_t *solver, thvar_t v, thvar_t w, bool tt) {
  dl_triple_t *triple;

  triple = &solver->triple;
  if (! diff_dl_vars(&solver->vtbl, v, w, triple)) {
    idl_exception(solver, FORMULA_NOT_IDL);
  }

  idl_assert_triple_eq(solver, triple, tt);
}




/*
 * Assert (c ==> v == w)
 */
void idl_assert_cond_vareq_axiom(idl_solver_t *solver, literal_t c, thvar_t v, thvar_t w) {
  dl_triple_t *triple;
  int32_t x, y, d;
  literal_t l1, l2;

  triple = &solver->triple;
  if (! diff_dl_vars(&solver->vtbl, v, w, triple)) {
    idl_exception(solver, FORMULA_NOT_IDL);
  }

  x = triple->target;
  y = triple->source;
  // v == w is equivalent to (x - y + triple.constant) == 0

  if (x == y) {
    if (q_is_nonzero(&triple->constant)) {
      // (x - y + constant) == 0 is false
      add_unit_clause(solver->core, not(c));
    }
    return;
  }

  // convert the constant to int32_t d:
  if (! q_get32(&triple->constant, &d)) {
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  if (x < 0) {
    x = idl_get_zero_vertex(solver);
  } else if (y < 0) {
    y = idl_get_zero_vertex(solver);
  }

  /*
   * Assert (c ==> (x - y + d) == 0) as two clauses:
   *  c ==> (y - x <= d)
   *  c ==> (x - y <= -d)
   */
  if (d == INT32_MIN) {
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  l1 = idl_make_atom(solver, y, x, d);  // (y - x <= d)
  l2 = idl_make_atom(solver, x, y, -d); // (x - y <= -d)
  add_binary_clause(solver->core, not(c), l1);
  add_binary_clause(solver->core, not(c), l2);
}



/*
 * Assert (c[0] \/ .... \/ c[n-1] \/ v == w)
 */
void idl_assert_clause_vareq_axiom(idl_solver_t *solver, uint32_t n, literal_t *c, thvar_t v, thvar_t w) {
  dl_triple_t *triple;
  ivector_t *aux;
  int32_t x, y, d;
  literal_t l1, l2;

  triple = &solver->triple;
  if (! diff_dl_vars(&solver->vtbl, v, w, triple)) {
    idl_exception(solver, FORMULA_NOT_IDL);
  }

  x = triple->target;
  y = triple->source;

  // v == w is equivalent to (x - y + constant) == 0
  if (x == y) {
    if (q_is_nonzero(&triple->constant)) {
      // (x - y + d) == 0 is false
      add_clause(solver->core, n, c);
    }
    return;
  }

  // convert constant to a 32bit integer
  if (! q_get32(&triple->constant, &d)) {
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  if (x < 0) {
    x = idl_get_zero_vertex(solver);
  } else if (y < 0) {
    y = idl_get_zero_vertex(solver);
  }

  /*
   * Assert two clauses:
   *  c[0] \/ ... \/ c[n-1] \/ (y - x <= d)
   *  c[0] \/ ... \/ c[n-1] \/ (x - y <= -d)
   */
  if (d == INT32_MIN) {
    idl_exception(solver, ARITHSOLVER_EXCEPTION);
  }

  l1 = idl_make_atom(solver, y, x, d);  // (y - x <= d)
  l2 = idl_make_atom(solver, x, y, -d); // (x - y <= -d)

  aux = &solver->aux_vector;
  assert(aux->size == 0);
  ivector_copy(aux, c, n);

  assert(aux->size == n);
  ivector_push(aux, l1);
  add_clause(solver->core, n+1, aux->data);

  aux->data[n] = l2;
  add_clause(solver->core, n+1, aux->data);

  ivector_reset(aux);
}




/************************
 *  MODEL CONSTRUCTION  *
 ***********************/

/*
 * Set val[x] to vx then extend the model to predecessors of x that are
 * not marked: if y is not marked and there's a path from y to x, set
 *   val[y] := vx + d[y, x] and mark y.
 */
static void set_reference_point(idl_solver_t *solver, int32_t x, int32_t vx, byte_t *mark) {
  idl_matrix_t *m;
  idl_cell_t *cell;
  int32_t y, n;

  assert(solver->value != NULL && 0 <= x && x < solver->nvertices && ! tst_bit(mark, x));

  solver->value[x] = vx;
  set_bit(mark, x);
  m = &solver->graph.matrix;

  n = solver->nvertices;
  for (y=0; y<n; y++) {
    cell = idl_cell(m, y, x);
    if (cell->id > 0 && ! tst_bit(mark, y)) {
      set_bit(mark, y);
      solver->value[y] = vx + cell->dist;
    }
  }
}


/*
 * Compute val[x] for a vertex x in a new strongly connected component.
 * - i.e., there's no path from x to any existing marked vertex y
 * - we can set val[x] to anything larger than v[y] - d[y, x] where y is marked
 *   and a predecessor of x
 */
static int32_t value_of_new_vertex(idl_solver_t *solver, int32_t x, byte_t *mark) {
  idl_matrix_t *m;
  idl_cell_t *cell;
  int32_t y, n, vx, aux;

  vx = 0; // any default will do
  m = &solver->graph.matrix;
  n = solver->nvertices;

  for (y=0; y<n; y++) {
    cell = idl_cell(m, y, x);
    if (cell->id > 0 && tst_bit(mark, y)) {
      aux = solver->value[y] - cell->dist;
      if (aux > vx) {
        vx = aux;
      }
    }
  }

  return vx;
}



#ifndef NDEBUG

/*
 * For debugging: check whether the model is good
 */
static bool good_model(idl_solver_t *solver) {
  idl_matrix_t *m;
  idl_cell_t *cell;
  int32_t *val;
  uint32_t n;
  int32_t x, y;

  m = &solver->graph.matrix;
  val = solver->value;
  n = solver->nvertices;
  for (x=0; x<n; x++) {
    for (y=0; y<n; y++) {
      cell = idl_cell(m, x, y);
      if (cell->id >= 0 && val[x] - val[y] > cell->dist) {
        printf("---> BUG: invalid IDL model\n");
        printf("   val[");
        print_idl_vertex(stdout, x);
        printf("] = %"PRId32"\n", val[x]);
        printf("   val[");
        print_idl_vertex(stdout, y);
        printf("] = %"PRId32"\n", val[y]);
        printf("   dist[");
        print_idl_vertex(stdout, x);
        printf(", ");
        print_idl_vertex(stdout, y);
        printf("] = %"PRId32"\n", cell->dist);
        fflush(stdout);

        return false;
      }
    }
  }

  return true;
}

#endif


/*
 * Build a mapping from vertices to integers
 */
void idl_build_model(idl_solver_t *solver) {
  byte_t *mark;
  uint32_t nvars;
  int32_t x, vx;

  assert(solver->value == NULL);

  nvars = solver->nvertices;
  solver->value = (int32_t *) safe_malloc(nvars * sizeof(int32_t));
  mark = allocate_bitvector0(nvars); // mark[x] = 0 for every vertex x

  // make sure the zero vertex has value 0
  x = solver->zero_vertex;
  if (x >= 0) {
    set_reference_point(solver, x, 0, mark);
  }

  // extend the model (for vertices not connected to x)
  for (x=0; x<nvars; x++) {
    if (! tst_bit(mark, x)) {
      vx = value_of_new_vertex(solver, x, mark);
      set_reference_point(solver, x, vx, mark);
    }
  }

  delete_bitvector(mark);

  assert(good_model(solver));
}


/*
 * Free the model
 */
void idl_free_model(idl_solver_t *solver) {
  assert(solver->value != NULL);
  safe_free(solver->value);
  solver->value = NULL;
}


/*
 * Value of variable x in the model
 * - copy the value in v and return true
 */
bool idl_value_in_model(idl_solver_t *solver, thvar_t x, rational_t *v) {
  dl_triple_t *d;
  int32_t aux;

  assert(solver->value != NULL && 0 <= x && x < solver->vtbl.nvars);
  d = dl_var_triple(&solver->vtbl, x);

  // d is of the form (target - source + constant)
  aux = 0;
  if (d->target >= 0) {
    aux = idl_vertex_value(solver, d->target);
  }
  if (d->source >= 0) {
    aux -= idl_vertex_value(solver, d->source);
  }

  q_set32(v, aux); // aux is the value of (target - source) in the model
  q_add(v, &d->constant);

  return true;
}


/*
 * Interface function: check whether x is an integer variable.
 */
bool idl_var_is_integer(idl_solver_t *solver, thvar_t x) {
  assert(0 <= x && x < solver->vtbl.nvars);
  return true;
}


/***************************
 *  INTERFACE DESCRIPTORS  *
 **************************/

/*
 * Control interface
 */
static th_ctrl_interface_t idl_control = {
  (start_intern_fun_t) idl_start_internalization,
  (start_fun_t) idl_start_search,
  (propagate_fun_t) idl_propagate,
  (final_check_fun_t) idl_final_check,
  (increase_level_fun_t) idl_increase_decision_level,
  (backtrack_fun_t) idl_backtrack,
  (push_fun_t) idl_push,
  (pop_fun_t) idl_pop,
  (reset_fun_t) idl_reset,
  (clear_fun_t) idl_clear,
};


/*
 * SMT interface: delete_atom and end_atom_deletion are not supported.
 */
static th_smt_interface_t idl_smt = {
  (assert_fun_t) idl_assert_atom,
  (expand_expl_fun_t) idl_expand_explanation,
  (select_pol_fun_t) idl_select_polarity,
  NULL,
  NULL,
};



/*
 * Internalization interface
 */
static arith_interface_t idl_intern = {
  (create_arith_var_fun_t) idl_create_var,
  (create_arith_const_fun_t) idl_create_const,
  (create_arith_poly_fun_t) idl_create_poly,
  (create_arith_pprod_fun_t) idl_create_pprod,

  (create_arith_atom_fun_t) idl_create_eq_atom,
  (create_arith_atom_fun_t) idl_create_ge_atom,
  (create_arith_patom_fun_t) idl_create_poly_eq_atom,
  (create_arith_patom_fun_t) idl_create_poly_ge_atom,
  (create_arith_vareq_atom_fun_t) idl_create_vareq_atom,

  (assert_arith_axiom_fun_t) idl_assert_eq_axiom,
  (assert_arith_axiom_fun_t) idl_assert_ge_axiom,
  (assert_arith_paxiom_fun_t) idl_assert_poly_eq_axiom,
  (assert_arith_paxiom_fun_t) idl_assert_poly_ge_axiom,
  (assert_arith_vareq_axiom_fun_t) idl_assert_vareq_axiom,
  (assert_arith_cond_vareq_axiom_fun_t) idl_assert_cond_vareq_axiom,
  (assert_arith_clause_vareq_axiom_fun_t) idl_assert_clause_vareq_axiom,

  NULL, // attach_eterm is not supported
  NULL, // eterm of var is not supported

  (build_model_fun_t) idl_build_model,
  (free_model_fun_t) idl_free_model,
  (arith_val_in_model_fun_t) idl_value_in_model,

  (arith_var_is_int_fun_t) idl_var_is_integer,
};




/*****************
 *  FULL SOLVER  *
 ****************/

/*
 * initialize solver:
 * - core = attached smt_core solver
 * - gates = the attached gate manager
 */
void init_idl_solver(idl_solver_t *solver, smt_core_t *core, gate_manager_t *gates) {
  solver->core = core;
  solver->gate_manager = gates;
  solver->base_level = 0;
  solver->decision_level = 0;
  solver->unsat_before_search = false;

  init_dl_vartable(&solver->vtbl);

  solver->nvertices = 0;
  solver->zero_vertex = null_idl_vertex;
  init_idl_graph(&solver->graph);

  init_idl_atbl(&solver->atoms, DEFAULT_IDL_ATBL_SIZE);
  init_idl_astack(&solver->astack, DEFAULT_IDL_ASTACK_SIZE);
  init_idl_undo_stack(&solver->stack, DEFAULT_IDL_UNDO_STACK_SIZE);
  init_idl_trail_stack(&solver->trail_stack);

  init_int_htbl(&solver->htbl, 0);
  init_arena(&solver->arena);
  init_ivector(&solver->expl_buffer, DEFAULT_IDL_BUFFER_SIZE);
  init_ivector(&solver->aux_vector, DEFAULT_IDL_BUFFER_SIZE);

  // initialize the internal triple + buffer
  solver->triple.target = nil_vertex;
  solver->triple.source = nil_vertex;
  q_init(&solver->triple.constant);
  init_poly_buffer(&solver->buffer);

  // this gets allocated in create_model
  solver->value = NULL;

  // no jump buffer yet
  solver->env = NULL;

  // undo record for level 0
  push_undo_record(&solver->stack, -1, 0, 0);

  assert(valid_idl_graph(&solver->graph));
}


/*
 * Delete solver
 */
void delete_idl_solver(idl_solver_t *solver) {
  delete_dl_vartable(&solver->vtbl);
  delete_idl_graph(&solver->graph);
  delete_idl_atbl(&solver->atoms);
  delete_idl_astack(&solver->astack);
  delete_idl_undo_stack(&solver->stack);
  delete_idl_trail_stack(&solver->trail_stack);

  delete_int_htbl(&solver->htbl);
  delete_arena(&solver->arena);
  delete_ivector(&solver->expl_buffer);
  delete_ivector(&solver->aux_vector);

  q_clear(&solver->triple.constant);
  delete_poly_buffer(&solver->buffer);

  if (solver->value != NULL) {
    safe_free(solver->value);
    solver->value = NULL;
  }
}



/*
 * Attach a jump buffer
 */
void idl_solver_init_jmpbuf(idl_solver_t *solver, jmp_buf *buffer) {
  solver->env = buffer;
}


/*
 * Get the control and smt interfaces
 */
th_ctrl_interface_t *idl_ctrl_interface(idl_solver_t *solver) {
  return &idl_control;
}

th_smt_interface_t *idl_smt_interface(idl_solver_t *solver) {
  return &idl_smt;
}


/*
 * Get the internalization interface
 */
arith_interface_t *idl_arith_interface(idl_solver_t *solver) {
  return &idl_intern;
}
