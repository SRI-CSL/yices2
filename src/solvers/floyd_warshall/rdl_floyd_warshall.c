/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * INCREMENTAL FORM OF THE FLOYD-WARSHALL ALGORITHM FOR REAL DIFFERENCE LOGIC.
 */


#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "solvers/floyd_warshall/rdl_floyd_warshall.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"


#ifndef NDEBUG

#include <stdio.h>

#include "solvers/floyd_warshall/rdl_fw_printer.h"

#endif



/****************
 *  CONSTANTS   *
 ***************/

/*
 * Initialize c to 0.
 * This must be called before any other operation on c.
 */
static inline void init_rdl_const(rdl_const_t *c) {
  q_init(&c->q);
  c->delta = 0;
}

/*
 * Reset c to 0
 */
static inline void reset_rdl_const(rdl_const_t *c) {
  q_clear(&c->q);
  c->delta = 0;
}

/*
 * Clear c: must be called before deleting c
 * to prevent memory leaks.
 */
static inline void clear_rdl_const(rdl_const_t *c) {
  q_clear(&c->q);
}

/*
 * Copy value of c2 into c1
 * - c2 and c1 must be different
 */
static inline void rdl_const_set(rdl_const_t *c1, rdl_const_t *c2) {
  q_set(&c1->q, &c2->q);
  c1->delta = c2->delta;
}

/*
 * Copy rational r into c
 */
static inline void rdl_const_set_rational(rdl_const_t *c, rational_t *r) {
  q_set(&c->q, r);
  c->delta = 0;
}


/*
 * Copy rational - r - delta into c
 */
static inline void rdl_const_set_lt_rational(rdl_const_t *c, rational_t *r) {
  q_set_neg(&c->q, r);
  c->delta = -1;
}

/*
 * Add value of c2 to c1
 * - c1 and c2 must be different pointers
 */
static inline void rdl_const_add(rdl_const_t *c1, rdl_const_t *c2) {
  q_add(&c1->q, &c2->q);
  c1->delta += c2->delta;
}

/*
 * Subtract c2 from c1
 * - they must be different pointers
 */
static inline void rdl_const_sub(rdl_const_t *c1, rdl_const_t *c2) {
  q_sub(&c1->q, &c2->q);
  c1->delta -= c2->delta;
}


/*
 * Replace c by its opposite
 */
static inline void rdl_const_negate(rdl_const_t *c) {
  q_neg(&c->q);
  c->delta = - c->delta;
}

/*
 * Comparisons between c1 and c2
 * - rdl_const_le(c1, c2) tests whether c1 <= c2
 * - rdl_const_lt(c1, c2) tests whether c1 < c2
 * - rdl_const_eq(c1, c2) tests whether c1 == c2
 */
static inline bool rdl_const_le(rdl_const_t *c1, rdl_const_t *c2) {
  return q_lt(&c1->q, &c2->q) || (q_eq(&c1->q, &c2->q) && c1->delta <= c2->delta);
}

static inline bool rdl_const_lt(rdl_const_t *c1, rdl_const_t *c2) {
  return q_lt(&c1->q, &c2->q) || (q_eq(&c1->q, &c2->q) && c1->delta < c2->delta);
}

#ifndef NDEBUG
static inline bool rdl_const_eq(rdl_const_t *c1, rdl_const_t *c2) {
  return q_eq(&c1->q, &c2->q) && c1->delta == c2->delta;
}
#endif

/*
 * Comparisons between c and a rational q
 * - rdl_const_le_q(c, q) tests whether c <= q
 * - rdl_const_lt_q(c, q) tests whether c < q
 * - rdl_const_eq_q(c, q) tests whether c = q (Removed: not used)
 */
static inline bool rdl_const_le_q(rdl_const_t *c, rational_t *q) {
  return q_lt(&c->q, q) || (q_eq(&c->q, q) && c->delta <= 0);
}

#ifndef NDEBUG
static inline bool rdl_const_lt_q(rdl_const_t *c, rational_t *q) {
  return q_lt(&c->q, q) || (q_eq(&c->q, q) && c->delta < 0);
}
#endif



/*
 * Check whether c is zero
 */
#ifndef NDEBUG
static inline bool rdl_const_is_zero(rdl_const_t *c) {
  return q_is_zero(&c->q) && c->delta == 0;
}
#endif

/*
 * Check whether c1 is negative
 */
static inline bool rdl_const_is_neg(rdl_const_t *c) {
  return q_is_neg(&c->q) || (q_is_zero(&c->q) && c->delta < 0);
}







/****************
 *  EDGE STACK  *
 ***************/

/*
 * Initialize the stack
 * - n = initial size
 */
static void init_rdl_edge_stack(rdl_edge_stack_t *stack, uint32_t n) {
  assert(n < MAX_RDL_EDGE_STACK_SIZE);

  stack->data = (rdl_edge_t *) safe_malloc(n * sizeof(rdl_edge_t));
  stack->lit = (literal_t *) safe_malloc(n * sizeof(literal_t));
  stack->size = n;
  stack->top = 0;
}


/*
 * Make the stack 50% larger
 */
static void extend_rdl_edge_stack(rdl_edge_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n>>1;
  if (n >= MAX_RDL_EDGE_STACK_SIZE) {
    out_of_memory();
  }

  stack->data = (rdl_edge_t *) safe_realloc(stack->data, n * sizeof(rdl_edge_t));
  stack->lit = (literal_t *) safe_realloc(stack->lit, n * sizeof(literal_t));
  stack->size = n;
}


/*
 * Add an edge to the stack (the cost is not needed)
 * - x = source, y = target, l = literal attached
 */
static void push_edge(rdl_edge_stack_t *stack, int32_t x, int32_t y, literal_t l) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_rdl_edge_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i].source = x;
  stack->data[i].target = y;
  stack->lit[i] = l;
  stack->top = i+1;
}


/*
 * Empty the stack
 */
static inline void reset_rdl_edge_stack(rdl_edge_stack_t *stack) {
  stack->top = 0;
}


/*
 * Delete the stack
 */
static inline void delete_rdl_edge_stack(rdl_edge_stack_t *stack) {
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
static void init_rdl_matrix(rdl_matrix_t *matrix) {
  matrix->size = 0;
  matrix->dim = 0;
  matrix->data = NULL;
}


/*
 * Copy cell *src into *dst
 */
static void copy_rdl_cell(rdl_cell_t *dst, rdl_cell_t *src) {
  dst->id = src->id;
  rdl_const_set(&dst->dist, &src->dist);
}

/*
 * Resize to an (n * n) matrix
 * - if n > matrix->dim then new cells are initialized as follows:
 * - for new x, M[x, x].id = 0, M[x, x].dist = 0
 *   for new x and y with x != y, M[x, y].id = null_rdl_edge
 * If n < matrix->dim, then some cells are lost
 */
static void resize_rdl_matrix(rdl_matrix_t *matrix, uint32_t n) {
  uint64_t new_size;
  uint32_t i, j, d, old_size;
  rdl_cell_t *src, *dst;


  // d = current dimension, n = new dimension
  d = matrix->dim;
  if (d == n) return;

  matrix->dim = n;

  // extend the data array if it's too small
  if (n > matrix->size) {
    new_size = n * n;
    if (n >= MAX_RDL_MATRIX_DIMENSION || new_size >= (SIZE_MAX/sizeof(rdl_cell_t))) {
      out_of_memory();
    }

    // initialize the new cells: id = null_rdl_edge, dist = 0;
    src = (rdl_cell_t *) safe_realloc(matrix->data, new_size * sizeof(rdl_cell_t));
    old_size = matrix->size * matrix->size;
    for (i=old_size; i<new_size; i++) {
      src[i].id = null_rdl_edge;
      init_rdl_const(&src[i].dist);
    }

    matrix->data = src;
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
        // copy src[j] into dst[j]
        copy_rdl_cell(dst+j, src+j);
      }
    }


    // initialize cells [d...n-1] in rows 0 to d-1
    dst = matrix->data;
    for (i=0; i<d; i++) {
      for (j=d; j<n; j++) {
        dst[j].id = null_rdl_edge;
      }
      dst += n;
    }

    // initialize cells [0 ... n-1] in rows d to n-1
    while (i<n) {
      for (j=0; j<n; j++) {
        dst[j].id = null_rdl_edge;
      }
      i ++;
      dst += n;
    }

    // initialize diagonal: cell i of row i, for i=d to n-1
    for (i=d; i<n; i++) {
      dst = matrix->data + n * i + i;
      dst->id = 0;
      reset_rdl_const(&dst->dist);
    }

  } else {
    assert(n < d);

    // move existing cells
    for (i=0; i<n; i++) {
      src = matrix->data + d * i;
      dst = matrix->data + n * i;
      for (j=0; j<n; j++) {
        // copy src[j] into dst[j]
        copy_rdl_cell(dst+j, src+j);
      }
    }
  }
}


/*
 * Reset to the empty matrix
 */
static inline void reset_rdl_matrix(rdl_matrix_t *matrix) {
  matrix->dim = 0;
}


/*
 * Delete the matrix
 */
static inline void delete_rdl_matrix(rdl_matrix_t *matrix) {
  uint32_t i, n;

  n = matrix->size * matrix->size;
  for (i=0; i<n; i++) {
    clear_rdl_const(&matrix->data[i].dist);
  }
  safe_free(matrix->data);
  matrix->data = NULL;
}


/*
 * Pointer to cell x, y
 */
static inline rdl_cell_t *rdl_cell(rdl_matrix_t *m, uint32_t x, uint32_t y) {
  assert(0 <= x && x < m->dim && 0 <= y && y < m->dim);
  return m->data + x * m->dim + y;
}

/*
 * Pointer to the start of row x
 */
static inline rdl_cell_t *rdl_row(rdl_matrix_t *m, uint32_t x) {
  assert(0 <= x && x < m->dim);
  return m->data + x * m->dim;
}


/*
 * Distance from x to y
 */
static inline rdl_const_t *rdl_dist(rdl_matrix_t *m, uint32_t x, uint32_t y) {
  assert(rdl_cell(m, x, y)->id >= 0);
  return &rdl_cell(m, x, y)->dist;
}

/*
 * Edge id for path from x to y
 */
static inline int32_t rdl_edge_id(rdl_matrix_t *m, uint32_t x, uint32_t y) {
  return rdl_cell(m, x, y)->id;
}





/*****************
 *  SAVED CELLS  *
 ****************/

/*
 * Initialize the stack
 * - n = initial size
 */
static void init_rdl_cell_stack(rdl_cell_stack_t *stack, uint32_t n) {
  uint32_t i;
  rdl_saved_cell_t *tmp;

  assert(n < MAX_RDL_CELL_STACK_SIZE);

  tmp = (rdl_saved_cell_t *) safe_malloc(n * sizeof(rdl_saved_cell_t));
  for (i=0; i<n; i++) {
    init_rdl_const(&tmp[i].saved.dist);
  }

  stack->data = tmp;
  stack->size = n;
  stack->top = 0;
}


/*
 * Make the stack 50% larger
 */
static void extend_rdl_cell_stack(rdl_cell_stack_t *stack) {
  uint32_t i, n;
  rdl_saved_cell_t *tmp;

  n = stack->size + 1;
  n += n>>1;
  if (n >= MAX_RDL_CELL_STACK_SIZE) {
    out_of_memory();
  }

  tmp = (rdl_saved_cell_t *) safe_realloc(stack->data, n * sizeof(rdl_saved_cell_t));
  for (i=stack->size; i<n; i++) {
    init_rdl_const(&tmp[i].saved.dist);
  }

  stack->data = tmp;
  stack->size = n;
}


/*
 * Save cell c on top of the stack
 * - k = index of c in the matrix
 */
static void save_cell(rdl_cell_stack_t *stack, uint32_t k, rdl_cell_t *c) {
  uint32_t i;
  rdl_saved_cell_t *s;

  i = stack->top;
  if (i == stack->size) {
    extend_rdl_cell_stack(stack);
  }
  assert(i < stack->size);
  s = stack->data + i;
  s->index = k;
  s->saved.id = c->id;
  rdl_const_set(&s->saved.dist, &c->dist);

  stack->top = i+1;
}


/*
 * Empty the stack
 */
static inline void reset_rdl_cell_stack(rdl_cell_stack_t *stack) {
  stack->top = 0;
}


/*
 * Delete the stack
 */
static inline void delete_rdl_cell_stack(rdl_cell_stack_t *stack) {
  uint32_t i, n;
  rdl_saved_cell_t *tmp;

  tmp = stack->data;
  n = stack->size;
  for (i=0; i<n; i++) {
    clear_rdl_const(&tmp[i].saved.dist);
  }
  safe_free(tmp);
  stack->data = NULL;
}





/***********
 *  GRAPH  *
 **********/

/*
 * Initialize graph: use default sizes
 * - store edge 0 (used as a marker for path from x to x)
 */
static void init_rdl_graph(rdl_graph_t *graph) {
  init_rdl_matrix(&graph->matrix);
  init_rdl_edge_stack(&graph->edges, DEFAULT_RDL_EDGE_STACK_SIZE);
  init_rdl_cell_stack(&graph->cstack, DEFAULT_RDL_CELL_STACK_SIZE);
  init_ivector(&graph->buffer, DEFAULT_RDL_BUFFER_SIZE);
  init_rdl_const(&graph->c0);

  push_edge(&graph->edges, null_rdl_vertex, null_rdl_vertex, true_literal);
}

/*
 * Delete all
 */
static void delete_rdl_graph(rdl_graph_t *graph) {
  delete_rdl_cell_stack(&graph->cstack);
  delete_rdl_edge_stack(&graph->edges);
  delete_rdl_matrix(&graph->matrix);
  delete_ivector(&graph->buffer);
  clear_rdl_const(&graph->c0);
}

/*
 * Reset: empty graph
 */
static void reset_rdl_graph(rdl_graph_t *graph) {
  reset_rdl_matrix(&graph->matrix);
  reset_rdl_edge_stack(&graph->edges);
  reset_rdl_cell_stack(&graph->cstack);
  ivector_reset(&graph->buffer);
  reset_rdl_const(&graph->c0);

  push_edge(&graph->edges, null_rdl_vertex, null_rdl_vertex, true_literal);
}


/*
 * Resize: n = number of vertices
 * - extend and initialize the matrix appropriately
 */
static inline void resize_rdl_graph(rdl_graph_t *graph, uint32_t n) {
  resize_rdl_matrix(&graph->matrix, n);
}


/*
 * Get number of edges and saved cells
 */
static inline uint32_t rdl_graph_num_edges(rdl_graph_t *graph) {
  return graph->edges.top;
}

static inline uint32_t rdl_graph_num_cells(rdl_graph_t *graph) {
  return graph->cstack.top;
}


/*
 * Auxiliary function: save cell r onto the saved cell stack
 */
static inline void rdl_graph_save_cell(rdl_graph_t *graph, rdl_cell_t *r) {
  save_cell(&graph->cstack, r - graph->matrix.data, r);
}


/*
 * Auxiliary function: check whether c + r->dist < s->dist
 * - use d as a buffer
 */
static bool dist_reduced(rdl_cell_t *r, rdl_cell_t *s, rdl_const_t *c, rdl_const_t *d) {
  if (s->id < 0) return true;

  rdl_const_set(d, c);
  rdl_const_add(d, &r->dist);
  return rdl_const_lt(d, &s->dist);
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
 * Side effect:
 * - graph->c0 is modified
 */
static void rdl_graph_add_edge(rdl_graph_t *graph, int32_t x, int32_t y, rdl_const_t *c, literal_t l, int32_t k) {
  int32_t id, z, w;
  rdl_const_t *d;
  rdl_cell_t *r, *s;
  ivector_t *v;
  rdl_matrix_t *m;
  int32_t *aux;
  uint32_t i, n;

  m = &graph->matrix;
  d = &graph->c0;
  assert(0 <= x && x < m->dim && 0 <= y && y < m->dim && x != y && c != d);

  id = graph->edges.top; // index of the new edge
  push_edge(&graph->edges, x, y, l);

  /*
   * collect relevant vertices in vector v:
   * vertex z is relevant if there's a path from y to z and
   *    c + dist(y, z) < dist(x, z)
   * if z is not relevant then, for any vertex w, the new edge
   * cannot reduce dist(w, z)
   */
  v = &graph->buffer;
  ivector_reset(v);
  r = rdl_row(m, y);  // start of row y
  s = rdl_row(m, x);  // start of row x
  for (z=0; z<m->dim; z++, r++, s++) {
    // r --> cell[y, z] and s --> cell[x, z]
    if (r->id >= 0 && dist_reduced(r, s, c, d)) {
      // c + r->dist < s->dist: z is relevant
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
  r = rdl_row(m, 0);
  for (w=0; w<m->dim; w++, r += m->dim) {
    // r[x] == cell[w, x] and r[y] == cell[w, y]
    if (r[x].id >= 0 && dist_reduced(r + x, r + y, c, d)) {
      // (c + r[x].dist < r[y].dist)
      // w is relevant: check D[w, z] for all z in vector aux
      for (i=0; i<n; i++) {
        z = aux[i];
        if (w != z) {
          // d := length of path w ---> x -> y ---> z
          rdl_const_set(d, &r[x].dist);
          rdl_const_add(d, c);
          rdl_const_add(d, rdl_dist(m, y, z));
          // we have r[z] == cell[w, z]
          if (r[z].id < 0 || rdl_const_lt(d, &r[z].dist)) {
            // path w ---> x --> y ---> z is shorter than
            // the current path from w to z.
            // save then update cell[w, z]
            if (r[z].id < k) {
              rdl_graph_save_cell(graph, r + z);
            }
            r[z].id = id;
            rdl_const_set(&r[z].dist, d);
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
static void rdl_graph_remove_edges(rdl_graph_t *graph, int32_t e, uint32_t c) {
  rdl_saved_cell_t *saved;
  rdl_cell_t *m;
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
    m[k].id = saved[i].saved.id;
    rdl_const_set(&m[k].dist, &saved[i].saved.dist);
  }
  graph->cstack.top = c;
}




/*
 * Build explanation: get all literals appearing along the shortest path from x to y
 * - the literals are stored in vector v
 */
static void rdl_graph_explain_path(rdl_graph_t *graph, int32_t x, int32_t y, ivector_t *v) {
  int32_t i;
  literal_t l;

  if (x != y) {
    i = rdl_edge_id(&graph->matrix, x, y);
    assert(1 <= i && i < graph->edges.top);
    /*
     * The shortest path from x to y is x ---> s -> t ---> y
     * where s = source of edge i and t = target of edge i.
     */
    rdl_graph_explain_path(graph, x, graph->edges.data[i].source, v);
    l = graph->edges.lit[i];
    if (l != true_literal) {
      ivector_push(v, l);
    }
    rdl_graph_explain_path(graph, graph->edges.data[i].target, y, v);
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
static bool valid_rdl_graph(rdl_graph_t *graph) {
  rdl_matrix_t *m;
  rdl_edge_t *e;
  int32_t x, y, i;
  int32_t u, v;
  rdl_const_t d;

  init_rdl_const(&d);

  m = &graph->matrix;
  for (x=0; x<m->dim; x++) {
    for (y=0; y<m->dim; y++) {
      i = rdl_edge_id(m, x, y);
      if (i == null_rdl_edge) {
        if (x == y) return false;
      } else if (i == 0) {
        if (x != y || ! rdl_const_is_zero(rdl_dist(m, x, y))) return false;
      } else {
        if (x == y || i >= rdl_graph_num_edges(graph)) return false;

        e = graph->edges.data + i;
        u = e->source;
        v = e->target;

        if (rdl_edge_id(m, x, u) == null_rdl_edge || rdl_edge_id(m, x, u) >= i ||
            rdl_edge_id(m, v, y) == null_rdl_edge || rdl_edge_id(m, v, y) >= i ||
            rdl_edge_id(m, u, v) != i) {
          return false;
        }


        rdl_const_set(&d, rdl_dist(m, x, u));
        rdl_const_add(&d, rdl_dist(m, u, v)); // i.e. cost of edge e
        rdl_const_add(&d, rdl_dist(m, v, y));
        if (! rdl_const_eq(&d, rdl_dist(m, x, y))){
          return false;
        }
      }
    }
  }

  clear_rdl_const(&d);

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
static void init_rdl_atbl(rdl_atbl_t *table, uint32_t n) {
  rdl_listelem_t *tmp;
  rdl_atom_t *atm;
  uint32_t i;

  assert(n < MAX_RDL_ATBL_SIZE);

  atm = (rdl_atom_t *) safe_malloc(n * sizeof(rdl_atom_t));
  for (i=0; i<n; i++) {
    q_init(&atm[i].cost);
  }

  table->size = n;
  table->natoms = 0;
  table->atoms = atm;
  table->mark = allocate_bitvector(n);

  // table->free_list[-1] is the list header
  // the list is initially empty
  tmp = (rdl_listelem_t *) safe_malloc((n+1) * sizeof(rdl_listelem_t));
  tmp[0].pre = -1;
  tmp[0].next = -1;
  table->free_list = tmp + 1;
}


/*
 * Make the table 50% larger
 */
static void extend_rdl_atbl(rdl_atbl_t *table) {
  uint32_t i, n;
  rdl_listelem_t *tmp;
  rdl_atom_t *atm;

  n = table->size + 1;
  n += n>>1;
  if (n >= MAX_RDL_ATBL_SIZE) {
    out_of_memory();
  }

  atm = (rdl_atom_t *) safe_realloc(table->atoms, n * sizeof(rdl_atom_t));
  for (i=table->size; i<n; i++) {
    q_init(&atm[i].cost);
  }

  table->size = n;
  table->atoms = atm;
  table->mark = extend_bitvector(table->mark, n);

  tmp = (rdl_listelem_t *) safe_realloc(table->free_list - 1, (n+1) * sizeof(rdl_listelem_t));
  table->free_list = tmp + 1;
}



/*
 * Add element i last into the free list
 */
static inline void rdlatom_add_last(rdl_listelem_t *list, int32_t i) {
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
static inline void rdlatom_remove(rdl_listelem_t *list, int32_t i) {
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
static inline void rdlatom_putback(rdl_listelem_t *list, int32_t i) {
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
static inline void reset_rdlatom_list(rdl_listelem_t *list) {
  list[-1].next = -1;
  list[-1].pre = -1;
}


/*
 * First element of the list (-1 if the list is empty)
 */
static inline int32_t first_in_list(rdl_listelem_t *list) {
  return list[-1].next;
}

/*
 * Successor of i in the list (-1 if i is the last element)
 */
static inline int32_t next_in_list(rdl_listelem_t *list, int32_t i) {
  return list[i].next;
}



/*
 * Create a new atom: (x - y <= c)
 * returned value = the atom id
 * boolvar is initialized to null_bvar
 * the mark is cleared and the atom id is added to the free list
 */
static int32_t new_rdl_atom(rdl_atbl_t *table, int32_t x, int32_t y, rational_t *c) {
  uint32_t i;
  rdl_atom_t *a;

  i = table->natoms;
  if (i == table->size) {
    extend_rdl_atbl(table);
  }
  assert(i < table->size);
  a = table->atoms + i;
  a->source = x;
  a->target = y;
  q_set(&a->cost, c);
  a->boolvar = null_bvar;

  clr_bit(table->mark, i);
  rdlatom_add_last(table->free_list, i);
  table->natoms ++;

  return i;
}


/*
 * Get atom descriptor for atom i
 */
static inline rdl_atom_t *get_rdl_atom(rdl_atbl_t *table, int32_t i) {
  assert(0 <= i && i < table->natoms);
  return table->atoms + i;
}


/*
 * Check whether atom i is assigned (i.e., marked)
 */
static inline bool rdl_atom_is_assigned(rdl_atbl_t *table, int32_t i) {
  assert(0 <= i && i < table->natoms);
  return tst_bit(table->mark, i);
}


/*
 * Record that atom i is assigned: mark it, remove it from the free list
 * - i must not be marked
 */
static void mark_atom_assigned(rdl_atbl_t *table, int32_t i) {
  assert(0 <= i && i < table->natoms && ! tst_bit(table->mark, i));
  set_bit(table->mark, i);
  rdlatom_remove(table->free_list, i);
}


/*
 * Record that atom i is no longer assigned: clear is mark,
 * put it back into the free list
 */
static void mark_atom_unassigned(rdl_atbl_t *table, int32_t i) {
  assert(0 <= i && i < table->natoms && tst_bit(table->mark, i));
  clr_bit(table->mark, i);
  rdlatom_putback(table->free_list, i);
}




/*
 * Get the index of the first unassigned atom (-1 if all atoms are assigned)
 */
static inline int32_t first_unassigned_atom(rdl_atbl_t *table) {
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
static inline int32_t next_unassigned_atom(rdl_atbl_t *table, int32_t i) {
  return next_in_list(table->free_list, i);
}


/*
 * Remove all atoms of index >= n
 */
static void restore_rdl_atbl(rdl_atbl_t *table, uint32_t n) {
  uint32_t i;

  assert(n <= table->natoms);

  // remove atoms from the free list
  for (i=n; i<table->natoms; i++) {
    if (! tst_bit(table->mark, i)) {
      rdlatom_remove(table->free_list, i);
    }
  }
  table->natoms = n;
}


/*
 * Empty the table
 */
static inline void reset_rdl_atbl(rdl_atbl_t *table) {
  table->natoms = 0;
  reset_rdlatom_list(table->free_list);
}


/*
 * Delete the table
 */
static inline void delete_rdl_atbl(rdl_atbl_t *table) {
  rdl_atom_t *atm;
  uint32_t i, n;

  atm = table->atoms;
  n = table->size;
  for (i=0; i<n; i++) {
    q_clear(&atm[i].cost);
  }

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
static void init_rdl_astack(rdl_astack_t *stack, uint32_t n) {
  assert(n < MAX_RDL_ASTACK_SIZE);
  stack->size = n;
  stack->top = 0;
  stack->prop_ptr = 0;
  stack->data = (int32_t *) safe_malloc(n * sizeof(int32_t));
}

/*
 * Make the stack 50% larger
 */
static void extend_rdl_astack(rdl_astack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n>>1;
  if (n >= MAX_RDL_ASTACK_SIZE) {
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
static void push_atom_index(rdl_astack_t *stack, int32_t k) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_rdl_astack(stack);
  }
  assert(i < stack->size);
  stack->data[i] = k;
  stack->top = i+1;
}


/*
 * Empty the stack
 */
static inline void reset_rdl_astack(rdl_astack_t *stack) {
  stack->top = 0;
  stack->prop_ptr = 0;
}


/*
 * Delete the stack
 */
static inline void delete_rdl_astack(rdl_astack_t *stack) {
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
static void init_rdl_undo_stack(rdl_undo_stack_t *stack, uint32_t n) {
  assert(n < MAX_RDL_UNDO_STACK_SIZE);

  stack->size = n;
  stack->top = 0;
  stack->data = (rdl_undo_record_t *) safe_malloc(n * sizeof(rdl_undo_record_t));
}

/*
 * Extend the stack: make it 50% larger
 */
static void extend_rdl_undo_stack(rdl_undo_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n>>1;
  if (n >= MAX_RDL_UNDO_STACK_SIZE) {
    out_of_memory();
  }
  stack->size = n;
  stack->data = (rdl_undo_record_t *) safe_realloc(stack->data, n * sizeof(rdl_undo_record_t));
}


/*
 * Push record (e, c, a) on top of the stack
 * - e = top edge id
 * - c = top of the saved cell stack
 * - a = top of the atom stack
 */
static void push_undo_record(rdl_undo_stack_t *stack, int32_t e, uint32_t c, uint32_t a) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_rdl_undo_stack(stack);
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
static inline rdl_undo_record_t *rdl_undo_stack_top(rdl_undo_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}


/*
 * Empty the stack
 */
static inline void reset_rdl_undo_stack(rdl_undo_stack_t *stack) {
  stack->top = 0;
}

/*
 * Delete the stack
 */
static inline void delete_rdl_undo_stack(rdl_undo_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}



/********************
 *  PUSH/POP STACK  *
 *******************/

/*
 * Initialize: size = 0;
 */
static void init_rdl_trail_stack(rdl_trail_stack_t *stack) {
  stack->size = 0;
  stack->top = 0;
  stack->data = NULL;
}


/*
 * Save data for the current base_level:
 * - nv = number of vertices
 * - na = number of atoms
 */
static void rdl_trail_stack_save(rdl_trail_stack_t *stack, uint32_t nv, uint32_t na) {
  uint32_t i, n;

  i = stack->top;
  n = stack->size;
  if (i == n) {
    if (n == 0) {
      n = DEFAULT_RDL_TRAIL_SIZE;
    } else {
      n += n>>1; // 50% larger
      if (n >= MAX_RDL_TRAIL_SIZE) {
        out_of_memory();
      }
    }
    stack->data = (rdl_trail_t *) safe_realloc(stack->data, n * sizeof(rdl_trail_t));
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
static inline rdl_trail_t *rdl_trail_stack_top(rdl_trail_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}


/*
 * Remove the top record
 */
static inline void rdl_trail_stack_pop(rdl_trail_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}


/*
 * Empty the stack
 */
static inline void reset_rdl_trail_stack(rdl_trail_stack_t *stack) {
  stack->top = 0;
}


/*
 * Delete the stack
 */
static inline void delete_rdl_trail_stack(rdl_trail_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}






/*********************
 *  VERTEX CREATION  *
 ********************/

/*
 * Create a new vertex and return its index
 * - return null_rdl_vertex if there are too many vertices
 */
int32_t rdl_new_vertex(rdl_solver_t *solver) {
  uint32_t n;

  n = solver->nvertices;
  if (n >= MAX_RDL_VERTICES) {
    return null_rdl_vertex;
  }
  solver->nvertices = n + 1;
  return n;
}


/*
 * Get the zero vertex (create a new vertex if needed)
 * - return null_rdl_vertex if the new vertex can't be created
 */
int32_t rdl_zero_vertex(rdl_solver_t *solver) {
  int32_t z;

  z = solver->zero_vertex;
  if (z == null_rdl_vertex) {
    z = rdl_new_vertex(solver);
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
static inline uint32_t hash_rdl_atom(int32_t x, int32_t y, rational_t *d) {
  uint32_t hn, hd;
  q_hash_decompose(d, &hn, &hd);
  return jenkins_hash_quad(x, hn, y, hd, 0x74178ade);
}


/*
 * Hash consing object for interfacing with int_hash_table
 */
typedef struct rdlatom_hobj_s {
  int_hobj_t m;     // methods
  rdl_atbl_t *atbl; // atom table
  int32_t source, target;
  rational_t *cost;
} rdlatom_hobj_t;


/*
 * Functions for int_hash_table
 */
static uint32_t hash_atom(rdlatom_hobj_t *p) {
  return hash_rdl_atom(p->source, p->target, p->cost);
}

static bool equal_atom(rdlatom_hobj_t *p, int32_t id) {
  rdl_atom_t *atm;

  atm = get_rdl_atom(p->atbl, id);
  return atm->source == p->source && atm->target == p->target && q_eq(&atm->cost, p->cost);
}

static int32_t build_atom(rdlatom_hobj_t *p) {
  return new_rdl_atom(p->atbl, p->source, p->target, p->cost);
}

/*
 * Hobject
 */
static rdlatom_hobj_t atom_hobj = {
  { (hobj_hash_t) hash_atom, (hobj_eq_t) equal_atom, (hobj_build_t) build_atom },
  NULL,
  0, 0, 0,
};


/*
 * Atom constructor: use hash consing
 * - if the atom is new, create a fresh boolean variable v
 *   and the atom index to v in the core
 */
static bvar_t bvar_for_atom(rdl_solver_t *solver, int32_t x, int32_t y, rational_t *d) {
  int32_t id;
  rdl_atom_t *atm;
  bvar_t v;

  atom_hobj.atbl = &solver->atoms;
  atom_hobj.source = x;
  atom_hobj.target = y;
  atom_hobj.cost = d;
  id = int_htbl_get_obj(&solver->htbl, (int_hobj_t *) &atom_hobj);
  atm = get_rdl_atom(&solver->atoms, id);
  v = atm->boolvar;
  if (v == null_bvar) {
    v = create_boolean_variable(solver->core);
    atm->boolvar = v;
    attach_atom_to_bvar(solver->core, v, rdl_index2atom(id));
  }
  return v;
}


/*
 * Get literal for atom (x - y <= c): simplify and normalize first
 * Side effect: modify solver->c1
 */
literal_t rdl_make_atom(rdl_solver_t *solver, int32_t x, int32_t y, rational_t *c) {
  assert(0 <= x && x < solver->nvertices && 0 <= y && y < solver->nvertices);

  if (x == y) {
    return q_is_nonneg(c) ? true_literal : false_literal;
  }

  // EXPERIMENTAL
  if (solver->base_level == solver->decision_level &&
      x < solver->graph.matrix.dim && y < solver->graph.matrix.dim) {
    rdl_cell_t *cell;
    rdl_const_t *d;

    d = &solver->c1;
    rdl_const_set_rational(d, c);

    cell = rdl_cell(&solver->graph.matrix, x, y);
    if (cell->id >= 0 && rdl_const_le(&cell->dist, d)){
      // dist[x, y] <= c so new atom is true
      return true_literal;
    }

    cell = rdl_cell(&solver->graph.matrix, y, x);
    if (cell->id >= 0) {
      rdl_const_add(d, &cell->dist);
      // dist[y, x] + c < 0, so new atom is false
      if (rdl_const_is_neg(d)) {
        return false_literal;
      }
    }
  }

  return pos_lit(bvar_for_atom(solver, x, y, c));
}









/****************
 *  ASSERTIONS  *
 ***************/

/*
 * Assert (x - y <= d) as an axiom:
 * - attach true_literal to the edge
 * Side effect: solver->graph.c0 is modified (so d must be different from solver->graph.c0)
 */
static void rdl_axiom_edge(rdl_solver_t *solver, int32_t x, int32_t y, rdl_const_t *d) {
  rdl_cell_t *cell;
  int32_t k;
  rdl_const_t *aux;

  assert(0 <= x && x < solver->nvertices && 0 <= y && y < solver->nvertices);
  assert(solver->decision_level == solver->base_level);
  assert(d != &solver->graph.c0);

  // do nothing if the solver is already in an inconsistent state
  if (solver->unsat_before_search) return;

  resize_rdl_graph(&solver->graph, solver->nvertices);

  // check whether the new axiom is redundant
  cell = rdl_cell(&solver->graph.matrix, x, y);
  if (cell->id >= 0 && rdl_const_le(&cell->dist, d)) {
    // d[x, y] <= c
    return;
  }

  // check whether adding the edge x--->y forms a negative circuit
  cell = rdl_cell(&solver->graph.matrix, y, x);
  if (cell->id >= 0) {
    aux = &solver->graph.c0;
    rdl_const_set(aux, d);
    rdl_const_add(aux, &cell->dist);
    if (rdl_const_is_neg(aux)) {
      solver->unsat_before_search = true;
      return;
    }
  }

  /*
   * save limit for add_edge:
   * k = top edge id stored in the top record of the undo stack
   * if base level == 0, k = -1, so nothing will be saved
   */
  assert(solver->stack.top == solver->decision_level + 1);
  k = rdl_undo_stack_top(&solver->stack)->edge_id;

  // add the edge
  rdl_graph_add_edge(&solver->graph, x, y, d, true_literal, k);
}


/*
 * Assert (x - y <= d) or (x - y < d) as an axiom
 * Side effect: modifies solver->c1
 */
void rdl_add_axiom_edge(rdl_solver_t *solver, int32_t x, int32_t y, rational_t *d, bool strict) {
  rdl_const_t *aux;

  aux = &solver->c1;
  rdl_const_set_rational(aux, d);
  if (strict) {
    aux->delta = -1;
  }
  rdl_axiom_edge(solver, x, y, aux);
}


/*
 * Assert (x - y == d) as an axiom: (x - y <= d && y - x <= -d)
 * Side effect: modifies solver->c1
 */
void rdl_add_axiom_eq(rdl_solver_t *solver, int32_t x, int32_t y, rational_t *d) {
  rdl_const_t *aux;

  aux = &solver->c1;
  rdl_const_set_rational(aux, d);
  rdl_axiom_edge(solver, x, y, aux);
  rdl_const_negate(aux);
  rdl_axiom_edge(solver, y, x, aux);
}


/*
 * Try to assert (x - y <= d) with explanation l
 * - if that causes a conflict, generate the conflict explanation and return false
 * - return true if the edge does not cause a conflict
 * The graph matrix must have dimension == solver->nvertices
 * SIDE EFFECT: modifies solver->graph.c0
 */
static bool rdl_add_edge(rdl_solver_t *solver, int32_t x, int32_t y, rdl_const_t *d, literal_t l) {
  rdl_cell_t *cell;
  int32_t k;
  uint32_t i, n;
  ivector_t *v;
  rdl_const_t *aux;

  assert(0 <= x && x < solver->nvertices && 0 <= y && y < solver->nvertices);
  assert(d != &solver->graph.c0);

  // check whether the new edge causes a negative circuit
  cell = rdl_cell(&solver->graph.matrix, y, x);
  if (cell->id >= 0) {
    aux = &solver->graph.c0;
    rdl_const_set(aux, d);
    rdl_const_add(aux, &cell->dist);
    if (rdl_const_is_neg(aux)) {
      v = &solver->expl_buffer;
      ivector_reset(v);
      rdl_graph_explain_path(&solver->graph, y, x, v);
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
  }

  cell = rdl_cell(&solver->graph.matrix, x, y);
  if (cell->id < 0 || rdl_const_lt(d, &cell->dist)) {
    /*
     * The edge is not redundant: add it to the graph
     * backtrack point = number of edges on entry to the current decision level
     * that's stored in the top element in the undo stack
     */
    assert(solver->stack.top == solver->decision_level + 1);
    k = rdl_undo_stack_top(&solver->stack)->edge_id;
    rdl_graph_add_edge(&solver->graph, x, y, d, l, k);
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
static literal_t *gen_rdl_prop_antecedent(rdl_solver_t *solver, int32_t x, int32_t y) {
  ivector_t *v;
  literal_t *expl;
  uint32_t i, n;

  v = &solver->expl_buffer;
  ivector_reset(v);
  rdl_graph_explain_path(&solver->graph, x, y, v);

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
 * Side effect: modifies solver->c1
 */
static void check_atom_for_propagation(rdl_solver_t *solver, int32_t i) {
  rdl_atom_t *a;
  int32_t x, y;
  rdl_cell_t *cell;
  literal_t *expl;
  rdl_const_t *d;

  assert(! rdl_atom_is_assigned(&solver->atoms, i));

  d = &solver->c1;

  a = get_rdl_atom(&solver->atoms, i);
  x = a->source;
  y = a->target;
  rdl_const_set_rational(d, &a->cost);

  cell = rdl_cell(&solver->graph.matrix, x, y);
  if (cell->id >= 0 && rdl_const_le(&cell->dist, d)) {
    // d[x, y] <= d so x - y <= d is implied
    expl = gen_rdl_prop_antecedent(solver, x, y);
    mark_atom_assigned(&solver->atoms, i);
    push_atom_index(&solver->astack, pos_index(i));
    propagate_literal(solver->core, pos_lit(a->boolvar), expl);
    return;
  }

  cell = rdl_cell(&solver->graph.matrix, y, x);
  rdl_const_negate(d);
  if (cell->id >= 0 && rdl_const_lt(&cell->dist, d)) {
    // we have y - x <= d[y, x] < -d so x - y > d is implied
    expl = gen_rdl_prop_antecedent(solver, y, x);
    mark_atom_assigned(&solver->atoms, i);
    push_atom_index(&solver->astack, neg_index(i));
    propagate_literal(solver->core, neg_lit(a->boolvar), expl);
  }
}



/*
 * Scan all unassigned atoms and check propagation
 * - must be called after all atoms in the queue have been processed
 */
static void rdl_atom_propagation(rdl_solver_t *solver) {
  rdl_atbl_t *tbl;
  int32_t i;

  assert(solver->astack.top == solver->astack.prop_ptr);

  tbl = &solver->atoms;
  for (i=first_unassigned_atom(tbl); i >= 0; i = next_unassigned_atom(tbl, i)) {
    check_atom_for_propagation(solver, i);
  }

  // update prop_ptr to skip all implied atoms in the next
  // call to rdl_propagate.
  solver->astack.prop_ptr = solver->astack.top;
}



/********************
 *  SMT OPERATIONS  *
 *******************/

/*
 * Start internalization: do nothing
 */
void rdl_start_internalization(rdl_solver_t *solver) {
}


/*
 * Start search: if unsat flag is true, force a conflict in the core.
 * Otherwise, do nothing.
 */
void rdl_start_search(rdl_solver_t *solver) {
  if (solver->unsat_before_search) {
    record_empty_theory_conflict(solver->core);
  }
}


/*
 * Start a new decision level:
 * - save the current number of edges and saved cells,
 *   and the size of the atom queue
 */
void rdl_increase_decision_level(rdl_solver_t *solver) {
  uint32_t e, c, a;

  assert(! solver->unsat_before_search);
  assert(solver->astack.top == solver->astack.prop_ptr);

  e = rdl_graph_num_edges(&solver->graph);
  c = rdl_graph_num_cells(&solver->graph);
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
 * - neg_lit means assert its negation (y - x < -c)
 * We just push the corresponding atom index onto the propagation queue
 */
bool rdl_assert_atom(rdl_solver_t *solver, void *a, literal_t l) {
  int32_t k;

  k = rdl_atom2index(a);
  assert(var_of(l) == get_rdl_atom(&solver->atoms, k)->boolvar);

  if (! rdl_atom_is_assigned(&solver->atoms, k)) {
    mark_atom_assigned(&solver->atoms, k);
    push_atom_index(&solver->astack, mk_index(k, sign_of_lit(l)));
  }

  return true;
}


/*
 * Process all asserted atoms then propagate implied atoms to the core
 */
bool rdl_propagate(rdl_solver_t *solver) {
  uint32_t i, n;
  int32_t k, *a;
  int32_t x, y;
  literal_t l;
  rdl_atom_t *atom;
  rdl_const_t *d;

  resize_rdl_graph(&solver->graph, solver->nvertices);
  //  assert(valid_rdl_graph(&solver->graph));

  d = &solver->c1;
  a = solver->astack.data;
  n = solver->astack.top;
  for (i=solver->astack.prop_ptr; i<n; i++) {
    k = a[i];
    atom = get_rdl_atom(&solver->atoms, atom_of_index(k));
    // turn atom or its negation into (x - y <= d)
    if (is_pos_index(k)) {
      x = atom->source;
      y = atom->target;
      rdl_const_set_rational(d, &atom->cost); // d is cost
      l = pos_lit(atom->boolvar);
    } else {
      x = atom->target;
      y = atom->source;
      rdl_const_set_lt_rational(d, &atom->cost); // d is - cost - delta
      l = neg_lit(atom->boolvar);
    }

    if (! rdl_add_edge(solver, x, y, d, l)) return false; // conflict
  }

  solver->astack.prop_ptr = n;

  assert(valid_rdl_graph(&solver->graph));

  // theory propagation
  rdl_atom_propagation(solver);

  return true;
}



/*
 * Final check: do nothing and return SAT
 */
fcheck_code_t rdl_final_check(rdl_solver_t *solver) {
  return FCHECK_SAT;
}


/*
 * Clear: do nothing
 */
void rdl_clear(rdl_solver_t *solver) {
}




/*
 * Expand explanation for literal l
 * - l was implied with expl as antecedent
 * - expl is a null-terminated array of literals stored in the arena.
 * - v = vector where the explanation is to be added
 */
void rdl_expand_explanation(rdl_solver_t *solver, literal_t l, literal_t *expl, ivector_t *v) {
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
void rdl_backtrack(rdl_solver_t *solver, uint32_t back_level) {
  rdl_undo_record_t *undo;
  uint32_t i, n;
  int32_t k, *a;

  assert(solver->base_level <= back_level && back_level < solver->decision_level);

  /*
   * stack->data[back_level+1] = undo record created on entry to back_level + 1
   */
  assert(back_level + 1 < solver->stack.top);
  undo = solver->stack.data + back_level + 1;
  // remove all edges of level >= back_level + 1
  rdl_graph_remove_edges(&solver->graph, undo->edge_id, undo->nsaved);

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

  assert(valid_rdl_graph(&solver->graph));
}





/*
 * Push:
 * - store current number of vertices and atoms on the trail_stack
 * - increment both decision level and base level
 */
void rdl_push(rdl_solver_t *solver) {
  assert(solver->base_level == solver->decision_level);

  dl_vartable_push(&solver->vtbl);
  rdl_trail_stack_save(&solver->trail_stack, solver->nvertices, solver->atoms.natoms);
  solver->base_level ++;
  rdl_increase_decision_level(solver);
  assert(solver->decision_level == solver->base_level);
}


/*
 * Pop: remove vertices and atoms created at the current base-level
 */
void rdl_pop(rdl_solver_t *solver) {
  rdl_trail_t *top;
  uint32_t i, h, n, p;
  rdl_atom_t *a;

  assert(solver->base_level > 0 && solver->base_level == solver->decision_level);
  top = rdl_trail_stack_top(&solver->trail_stack);

  // remove variables
  dl_vartable_pop(&solver->vtbl);

  // remove atoms from the hash table
  p = top->natoms;
  n = solver->atoms.natoms;
  for (i = p; i<n; i++) {
    a = get_rdl_atom(&solver->atoms, i);
    h = hash_rdl_atom(a->source, a->target, &a->cost);
    int_htbl_erase_record(&solver->htbl, h, i);
  }

  // remove atoms from the atom table
  restore_rdl_atbl(&solver->atoms, n);

  // restore vertice count
  solver->nvertices = top->nvertices;
  resize_rdl_matrix(&solver->graph.matrix, top->nvertices);

  // decrement base_level
  solver->base_level --;
  rdl_trail_stack_pop(&solver->trail_stack);

  // backtrack to base_level
  rdl_backtrack(solver, solver->base_level);

  assert(valid_rdl_graph(&solver->graph));
}


/*
 * Reset
 */
void rdl_reset(rdl_solver_t *solver) {
  solver->base_level = 0;
  solver->decision_level = 0;
  solver->unsat_before_search = false;

  reset_dl_vartable(&solver->vtbl);

  solver->nvertices = 0;
  solver->zero_vertex = null_rdl_vertex;
  reset_rdl_graph(&solver->graph);

  reset_rdl_atbl(&solver->atoms);
  reset_rdl_astack(&solver->astack);
  reset_rdl_undo_stack(&solver->stack);
  reset_rdl_trail_stack(&solver->trail_stack);

  reset_int_htbl(&solver->htbl);
  arena_reset(&solver->arena);
  ivector_reset(&solver->expl_buffer);
  ivector_reset(&solver->aux_vector);
  reset_rdl_const(&solver->c1);
  q_clear(&solver->q);

  solver->triple.target = nil_vertex;
  solver->triple.source = nil_vertex;
  q_clear(&solver->triple.constant);
  reset_poly_buffer(&solver->buffer);

  q_clear(&solver->epsilon);
  q_clear(&solver->factor);
  q_clear(&solver->aux);
  q_clear(&solver->aux2);

  if (solver->value != NULL) {
    free_rational_array(solver->value, solver->nvertices);
    solver->value = NULL;
  }

  // undo record for level 0
  push_undo_record(&solver->stack, -1, 0, 0);

}



/*
 * THEORY-BRANCHING
 */

/*
 * We compute a variable assignment using vertex 0 as a reference:
 * - val[x] = d[0, x]
 * then to decide whether to case-split (x - y <= b) = true or false
 * we check whether val[x] - val[y] <= b.
 */
literal_t rdl_select_polarity(rdl_solver_t *solver, void *a, literal_t l) {
  bvar_t v;
  int32_t id;
  rdl_atom_t *atom;
  int32_t x, y;
  rdl_cell_t *cell_x, *cell_y;
  rdl_const_t *d;

  v = var_of(l);
  id = rdl_atom2index(a);
  atom = get_rdl_atom(&solver->atoms, id);
  assert(atom->boolvar == v);

  x = atom->source;
  y = atom->target;
  cell_x = rdl_cell(&solver->graph.matrix, 0, x);
  cell_y = rdl_cell(&solver->graph.matrix, 0, y);
  if (cell_x->id >= 0 && cell_y->id >= 0) {
    // d[0, x] and d[0, y] are defined:
    d = &solver->c1;
    rdl_const_set(d, &cell_x->dist);
    rdl_const_sub(d, &cell_y->dist);
    if (rdl_const_le_q(d, &atom->cost)) {
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
static __attribute__ ((noreturn)) void rdl_exception(rdl_solver_t *solver, int code) {
  if (solver->env != NULL) {
    longjmp(*solver->env, code);
  }
  abort();
}


/*
 * Apply renaming and substitution to polynomial p
 * - map is a variable renaming: if p is a_0 t_0 + ... + a_n t_n then
 *   map[i] = x_i is the theory variable that replaces t_i
 *   (with the exception that map[0] = null_thvar if t_0 is const_idx)
 * The function constructs a_0 x_0 + ... + a_n x_n and stores
 * the result into solver->buffer.
 */
static void rdl_rename_poly(rdl_solver_t *solver, polynomial_t *p, thvar_t *map) {
  poly_buffer_t *b;
  monomial_t *mono;
  uint32_t i, n;

  b = &solver->buffer;
  reset_poly_buffer(b);

  n = p->nterms;
  mono = p->mono;

  // deal with p's constant term if any
  if (map[0] == null_thvar) {
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
static int32_t rdl_get_zero_vertex(rdl_solver_t *solver) {
  int32_t z;

  z = rdl_zero_vertex(solver);
  if (z < 0) {
    rdl_exception(solver, TOO_MANY_ARITH_VARS);
  }
  return z;
}


/*
 * Create the atom (x - y + c) == 0 for d = (x - y + c)
 */
static literal_t rdl_eq_from_triple(rdl_solver_t *solver, dl_triple_t *d) {
  literal_t l1, l2;
  int32_t x, y;

  x = d->target;
  y = d->source;

  /*
   * d is (x - y + c)
   */
  if (x == y) {
    if (q_is_zero(&d->constant)) {
      return true_literal;
    } else {
      return false_literal;
    }
  }

  // a nil_vertex in triples denote 'zero'
  if (x < 0) {
    x = rdl_get_zero_vertex(solver);
  } else if (y < 0) {
    y = rdl_get_zero_vertex(solver);
  }

  // d == 0 is the conjunction of (y - x <= c) and (x - y <= -c)
  l1 = rdl_make_atom(solver, y, x, &d->constant); // atom (y - x <= c)
  q_set_neg(&solver->q, &d->constant);            // q := -c
  l2 = rdl_make_atom(solver, x, y, &solver->q);   // atom (x - y <= -c)

  return mk_and_gate2(solver->gate_manager, l1, l2);
}



/*
 * Create the atom (x - y + c) >= 0 for d = (x - y + c)
 */
static literal_t rdl_ge_from_triple(rdl_solver_t *solver, dl_triple_t *d) {
  int32_t x, y;
  x = d->target;
  y = d->source;

  if (x == y) {
    if (q_is_nonneg(&d->constant)) { // c >= 0
      return true_literal;
    } else {
      return false_literal;
    }
  }

  if (x < 0) {
    x = rdl_get_zero_vertex(solver);
  } else if (y < 0) {
    y = rdl_get_zero_vertex(solver);
  }

  // (x - y + c >= 0) is (y - x <= c)
  return rdl_make_atom(solver, y, x, &d->constant);
}


/*
 * Assert (x - y + c) == 0 or (x - y + c) != 0, given a triple d = x - y + c
 * - tt true: assert the equality
 * - tt false: assert the disequality
 */
static void rdl_assert_triple_eq(rdl_solver_t *solver, dl_triple_t *d, bool tt) {
  int32_t x, y;
  literal_t l1, l2;

  x = d->target;
  y = d->source;

  // d is (x - y + c)
  if (x == y) {
    if (q_is_zero(&d->constant) != tt) {
      solver->unsat_before_search = true;
    }
    return;
  }

  if (x < 0) {
    x = rdl_get_zero_vertex(solver);
  } else if (y < 0) {
    y = rdl_get_zero_vertex(solver);
  }

  if (tt) {
    // (x - y + c) == 0 is equivalent to y - x == c
    rdl_add_axiom_eq(solver, y, x, &d->constant);
  } else {
    // (x - y + c) != 0 is equivalent to
    // (not (y - x <= c)) or (not (x - y <= -c))
    l1 = rdl_make_atom(solver, y, x, &d->constant); // atom (y - x <= c)
    q_set_neg(&solver->q, &d->constant);            // q := -c
    l2 = rdl_make_atom(solver, x, y, &solver->q);   // atom (x - y <= -c)

    add_binary_clause(solver->core, not(l1), not(l2));
  }
}


/*
 * Assert either (x - y + c >= 0) or (x - y + c < 0) (depending on tt)
 * - if tt is true:  assert x - y + c >= 0
 * - if tt is false: assert x - y + x < 0
 */
static void rdl_assert_triple_ge(rdl_solver_t *solver, dl_triple_t *d, bool tt) {
  int32_t x, y;

  x = d->target;
  y = d->source;

  // d is (x - y + c)
  if (x == y) {
    if (q_is_nonneg(&d->constant) != tt) {
      // either c >= 0 and tt is false or c < 0 and tt is true
      solver->unsat_before_search = true;
    }
    return;
  }

  if (x < 0) {
    x = rdl_get_zero_vertex(solver);
  } else if (y < 0) {
    y = rdl_get_zero_vertex(solver);
  }

  if (tt) {
    // (x - y + c) >= 0 is equivalent to (y - x <= c)
    rdl_add_axiom_edge(solver, y, x, &d->constant, false);
  } else {
    // (x - y + c) < 0 is equivalent to (x - y < -c)
    q_set_neg(&solver->q, &d->constant);
    rdl_add_axiom_edge(solver, x, y, &solver->q, true);
  }
}



/*
 * TERM CONSTRUCTORS
 */

/*
 * Create a new theory variable
 * - is_int indicates whether the variable should be an integer,
 *   so it should always be true for this solver.
 * - raise exception NOT_RDL if is_int is true
 * - raise exception TOO_MANY_VARS if we can't create a new vertex
 *   for that variable
 */
thvar_t rdl_create_var(rdl_solver_t *solver, bool is_int) {
  dl_triple_t *triple;
  int32_t v;

  if (is_int) {
    rdl_exception(solver, FORMULA_NOT_RDL);
  }

  v = rdl_new_vertex(solver);
  if (v < 0) {
    rdl_exception(solver, TOO_MANY_ARITH_VARS);
  }

  // new variable descriptor = [v, nil, 0]
  triple = &solver->triple;
  triple->target = v;
  triple->source = nil_vertex;
  q_clear(&triple->constant);

  return get_dl_var(&solver->vtbl, triple);
}


/*
 * Create a variable that represents the constant q
 */
thvar_t rdl_create_const(rdl_solver_t *solver, rational_t *q) {
  dl_triple_t *triple;

  triple = &solver->triple;
  triple->target = nil_vertex;
  triple->source = nil_vertex;
  q_set(&triple->constant, q);

  return get_dl_var(&solver->vtbl, triple);
}


/*
 * Create a variable for a polynomial p, with variables defined by map:
 * - p is of the form a_0 t_0 + ... + a_n t_n where t_0, ..., t_n
 *   are arithmetic terms.
 * - map[i] is the theory variable x_i for t_i
 *   (with map[0] = null_thvar if t_0 is const_idx)
 * - the function constructs a variable equal to a_0 x_0 + ... + a_n x_n
 *
 * - fails if a_0 x_0 + ... + a_n x_n is not an RDL polynomial
 *   (i.e., not of the form x - y + c)
 */
thvar_t rdl_create_poly(rdl_solver_t *solver, polynomial_t *p, thvar_t *map) {
  poly_buffer_t *b;
  dl_triple_t *triple;

  // apply renaming
  rdl_rename_poly(solver, p, map);
  b = &solver->buffer;

  // b contains a_0 x_0 + ... + a_n x_n
  triple = &solver->triple;
  if (! convert_poly_buffer_to_dl_triple(b, triple)) {
    /*
     * Exception here: b is not of the right form
     */
    rdl_exception(solver, FORMULA_NOT_RDL);
  }

  return get_dl_var(&solver->vtbl, triple);
}


/*
 * Internalization for a product: always fails with NOT_RDL exception
 */
thvar_t rdl_create_pprod(rdl_solver_t *solver, pprod_t *p, thvar_t *map) {
  rdl_exception(solver, FORMULA_NOT_RDL);
}



/*
 * ATOM CONSTRUCTORS
 */

/*
 * Create the atom v = 0
 */
literal_t rdl_create_eq_atom(rdl_solver_t *solver, thvar_t v) {
  return rdl_eq_from_triple(solver, dl_var_triple(&solver->vtbl, v));
}


/*
 * Create the atom v >= 0
 */
literal_t rdl_create_ge_atom(rdl_solver_t *solver, thvar_t v) {
  return rdl_ge_from_triple(solver, dl_var_triple(&solver->vtbl, v));
}


/*
 * Atom p == 0
 */
literal_t rdl_create_poly_eq_atom(rdl_solver_t *solver, polynomial_t *p, thvar_t *map) {
  poly_buffer_t *b;
  dl_triple_t *triple;

  // apply renaming
  rdl_rename_poly(solver, p, map);

  b = &solver->buffer;
  triple = &solver->triple;
  if (! rescale_poly_buffer_to_dl_triple(b, triple)) {
    // not convertible to (x - y + c) == 0
    rdl_exception(solver, FORMULA_NOT_RDL);
  }

  return rdl_eq_from_triple(solver, triple);
}


/*
 * Atom p >= 0
 */
literal_t rdl_create_poly_ge_atom(rdl_solver_t *solver, polynomial_t *p, thvar_t *map) {
  poly_buffer_t *b;
  dl_triple_t *triple;

  // apply renaming
  rdl_rename_poly(solver, p, map);

  b = &solver->buffer;
  triple = &solver->triple;
  if (! rescale_poly_buffer_to_dl_triple(b, triple)) {
    // not convertible to (x - y + c) == 0
    rdl_exception(solver, FORMULA_NOT_RDL);
  }

  return rdl_ge_from_triple(solver, triple);
}



/*
 * Create the atom (v = w)
 */
literal_t rdl_create_vareq_atom(rdl_solver_t *solver, thvar_t v, thvar_t w) {
  dl_triple_t *triple;

  triple = &solver->triple;
  if (! diff_dl_vars(&solver->vtbl, v, w, triple)) {
    // v - w is not expressible as (target - source + c)
    rdl_exception(solver, FORMULA_NOT_RDL);
  }

  return rdl_eq_from_triple(solver, triple);
}



/*
 * TOP-LEVEL ASSERTIONS
 */

/*
 * Assert the top-level constraint (v == 0) or (v != 0)
 * - if tt is true: assert v == 0
 * - if tt is false: assert v != 0
 */
void rdl_assert_eq_axiom(rdl_solver_t *solver, thvar_t v, bool tt) {
  rdl_assert_triple_eq(solver, dl_var_triple(&solver->vtbl, v), tt);
}


/*
 * Assert the top-level constraint (v >= 0) or (v < 0)
 * - if tt is true: assert (v >= 0)
 * - if tt is false: assert (v < 0)
 */
void rdl_assert_ge_axiom(rdl_solver_t *solver, thvar_t v, bool tt) {
  rdl_assert_triple_ge(solver, dl_var_triple(&solver->vtbl, v), tt);
}


/*
 * Assert p == 0 if tt is true or p != 0 if tt is false
 * - map = variable renaming (as in create_poly)
 */
void rdl_assert_poly_eq_axiom(rdl_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt) {
  poly_buffer_t *b;
  dl_triple_t *triple;

  // apply renaming
  rdl_rename_poly(solver, p, map);

  b = &solver->buffer;
  triple = &solver->triple;
  if (! rescale_poly_buffer_to_dl_triple(b, triple)) {
    // not convertible to (x - y + c) == 0
    rdl_exception(solver, FORMULA_NOT_RDL);
  }

  rdl_assert_triple_eq(solver, triple, tt);
}


/*
 * Assert p >= 0 if tt is true or p < 0 if tt is false
 * - map = variable renaming (as in create_poly)
 */
void rdl_assert_poly_ge_axiom(rdl_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt) {
  poly_buffer_t *b;
  dl_triple_t *triple;

  // apply renaming
  rdl_rename_poly(solver, p, map);

  b = &solver->buffer;
  triple = &solver->triple;
  if (! rescale_poly_buffer_to_dl_triple(b, triple)) {
    // not convertible to (x - y + c) >= 0
    rdl_exception(solver, FORMULA_NOT_RDL);
  }

  rdl_assert_triple_ge(solver, triple, tt);
}



/*
 * Assert (v == w) or (v != w)
 * - if tt is true: assert (v == w)
 * - if tt is false: assert (v != w)
 */
void rdl_assert_vareq_axiom(rdl_solver_t *solver, thvar_t v, thvar_t w, bool tt) {
  dl_triple_t *triple;

  triple = &solver->triple;
  if (! diff_dl_vars(&solver->vtbl, v, w, triple)) {
    rdl_exception(solver, FORMULA_NOT_RDL);
  }

  rdl_assert_triple_eq(solver, triple, tt);
}


/*
 * Assert (c ==> v == w)
 */
void rdl_assert_cond_vareq_axiom(rdl_solver_t *solver, literal_t c, thvar_t v, thvar_t w) {
  dl_triple_t *triple;
  int32_t x, y;
  literal_t l1, l2;

  triple = &solver->triple;
  if (! diff_dl_vars(&solver->vtbl, v, w, triple)) {
    rdl_exception(solver, FORMULA_NOT_RDL);
  }

  x = triple->target;
  y = triple->source;
  // v == w is equivalent to (x - y + d) == 0
  if (x == y) {
    if (q_is_nonzero(&triple->constant)) {
      // (x - y + d) == 0 is false
      add_unit_clause(solver->core, not(c));
    }
    return;
  }


  if (x < 0) {
    x = rdl_get_zero_vertex(solver);
  } else if (y < 0) {
    y = rdl_get_zero_vertex(solver);
  }

  /*
   * Assert (c ==> (x - y + d) == 0) as two clauses:
   *  c ==> (y - x <= d)
   *  c ==> (x - y <= -d)
   */
  l1 = rdl_make_atom(solver, y, x, &triple->constant);  // (y - x <= d)
  q_set_neg(&solver->q, &triple->constant);             /// q := -d
  l2 = rdl_make_atom(solver, x, y, &solver->q);         // (x - y <= -d)
  add_binary_clause(solver->core, not(c), l1);
  add_binary_clause(solver->core, not(c), l2);
}



/*
 * Assert (c[0] \/ ... \/ c[n-1]  \/  v == w)
 */
void rdl_assert_clause_vareq_axiom(rdl_solver_t *solver, uint32_t n, literal_t *c, thvar_t v, thvar_t w) {
  dl_triple_t *triple;
  ivector_t *aux;
  int32_t x, y;
  literal_t l1, l2;

  triple = &solver->triple;
  if (! diff_dl_vars(&solver->vtbl, v, w, triple)) {
    rdl_exception(solver, FORMULA_NOT_RDL);
  }

  x = triple->target;
  y = triple->source;
  // v == w is equivalent to (x - y + d) == 0
  if (x == y) {
    if (q_is_nonzero(&triple->constant)) {
      // (x - y + d) == 0 is false
      add_clause(solver->core, n, c);
    }
    return;
  }


  if (x < 0) {
    x = rdl_get_zero_vertex(solver);
  } else if (y < 0) {
    y = rdl_get_zero_vertex(solver);
  }

  /*
   * Assert two clauses:
   *  c[0] \/ ... \/ c[n-1] \/ (y - x <= d)
   *  c[0] \/ ... \/ c[n-1] \/ (x - y <= -d)
   */
  l1 = rdl_make_atom(solver, y, x, &triple->constant);  // (y - x <= d)
  q_set_neg(&solver->q, &triple->constant);             /// q := -d
  l2 = rdl_make_atom(solver, x, y, &solver->q);         // (x - y <= -d)


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
 * Compute a safe rational value for delta.
 *
 * This assumes the system is feasible, i.e., there is no negative
 * circuit in the graph.
 *
 * For any circuit x --> y ---> x
 *    d[x, y] = a + b delta
 *    d[y, x] = a' + b' delta
 * So d[x, y] + d[y, x] >= 0 over the extended rationals, means
 * either (a + a') > 0 or (a + a') = 0 and (b + b') > 0.
 *
 * We want to find a positive rational epsilon for which the inequality
 * d[x, y] + d[y, x] >= 0 holds in the rationals. If (b + b') < 0, we must
 * take  epsilon <= - (a + a')/(b + b'). If (b + b') >= 0, any epsilon > 0 works.
 */

/*
 * Assign epsilon := min(epsilon, - (a+a')/(b + b')) for the two vertices x, y
 * - x and y must be distinct and there must be a path from x to y
 */
static void rdl_adjust_epsilon(rdl_solver_t *solver, int32_t x, int32_t y) {
  rdl_cell_t *cell_xy, *cell_yx;
  rational_t *aux, *factor;
  int32_t b;

  assert(x != y);
  cell_xy = rdl_cell(&solver->graph.matrix, x, y);
  cell_yx = rdl_cell(&solver->graph.matrix, y, x);
  assert(cell_xy->id > 0);
  if (cell_yx->id > 0) {
    // a circuit x --> y --> x exists
    b = cell_xy->dist.delta + cell_yx->dist.delta; // (b + b')
    if (b < 0) {
      aux = &solver->aux;
      q_set(aux, &cell_xy->dist.q);
      q_add(aux, &cell_yx->dist.q); // (a + a')
      assert(q_is_pos(aux));
      factor = &solver->factor;
      q_set32(factor, -b);
      q_div(aux, factor);  // aux := - (a+a')/(b+b');
      if (q_lt(aux, &solver->epsilon)) {
        q_set(&solver->epsilon, aux);
      }
    }
  }
}

static void rdl_compute_model_epsilon(rdl_solver_t *solver) {
  rdl_edge_t *edges;
  uint32_t i, n;

  q_set_one(&solver->epsilon); // any positive value as default

  // scan all the edges in the graph
  edges = solver->graph.edges.data;
  n = solver->graph.edges.top; // number of edges
  for (i=1; i<n; i++) {  // skip edge 0 = marker
    rdl_adjust_epsilon(solver, edges[i].source, edges[i].target);
  }
}


/*
 * Add a rational distance (computed using solver->epsilon) to rational v
 * - c = distance in symbolic form (a + k delta)
 */
static void rdl_add_rational_distance(rdl_solver_t *solver, rational_t *v, rdl_const_t *c) {
  rational_t *factor;

  factor = &solver->factor;
  assert(v != factor);
  q_add(v, &c->q);
  if (c->delta != 0) {
    q_set32(factor, c->delta);
    q_addmul(v, factor, &solver->epsilon);
  }
}

/*
 * Subtract a rational distance (computed using solver->epsilon) from rational v
 * - c = distance in symbolic form (a + k delta)
 */
static void rdl_sub_rational_distance(rdl_solver_t *solver, rational_t *v, rdl_const_t *c) {
  rational_t *factor;

  factor = &solver->factor;
  assert(v != factor);
  q_sub(v, &c->q);
  if (c->delta != 0) {
    q_set32(factor, c->delta);
    q_submul(v, factor, &solver->epsilon);
  }
}


/*
 * Assign value v to vertex x, then extend the model to predecessors of x
 * that are not marked. If y is not marked and there's a path from y to x,
 *  val[y] is set to v + d[x, y] (as computed using solver->epsilon).
 */
static void rdl_set_reference_point(rdl_solver_t *solver, int32_t x, rational_t *v, byte_t *mark) {
  rdl_matrix_t *m;
  rdl_cell_t *cell;
  rational_t *val, *aux;
  int32_t y, n;

  assert(solver->value != NULL && 0 <= x && x < solver->nvertices && ! tst_bit(mark, x));

  val = solver->value;
  aux = &solver->aux2;
  m = &solver->graph.matrix;

  assert(aux != v);

  q_set(val + x, v);
  set_bit(mark, x);

  n = solver->nvertices;
  for (y=0; y<n; y++) {
    cell = rdl_cell(m, y, x);
    if (cell->id > 0 && ! tst_bit(mark, y)) {
      q_set(aux, v);
      rdl_add_rational_distance(solver, aux, &cell->dist);
      // store that as value of y
      q_set(val + y, aux);
      set_bit(mark, y);
    }
  }
}


/*
 * Compute a value for vertex x in a new strongly connected component.
 * - there's no path from x to any of the already marked vertices
 * - we can set val[x] to anything larger than val[y] - d[y, x] where y is marked
 *   and is a predecessor of x
 */
static void rdl_get_value_for_new_vertex(rdl_solver_t *solver, int32_t x, rational_t *v, byte_t *mark) {
  rdl_matrix_t *m;
  rdl_cell_t *cell;
  rational_t *val, *aux;
  int32_t y, n;

  val = solver->value;
  aux = &solver->aux2;
  m = &solver->graph.matrix;
  n = solver->nvertices;

  assert(aux != v);

  q_clear(v); // set default to 0

  // scan predecessors and increase v if needed
  for (y=0; y<n; y++) {
    cell = rdl_cell(m, y, x);
    if (cell->id > 0 && tst_bit(mark, y)) {
      q_set(aux, val + y);
      rdl_sub_rational_distance(solver, aux, &cell->dist);
      // aux is val[y] - dist[y, x]
      if (q_gt(aux, v)) {
        q_set(v, aux);
      }
    }
  }
}



#ifndef NDEBUG

/*
 * For debugging: check whether the model is good
 * - for every vertex pair (x, y) we want val[x] - val[y] <= dist[x, y]
 */
static bool good_rdl_model(rdl_solver_t *solver) {
  rdl_matrix_t *m;
  rdl_cell_t *cell;
  rational_t *val, *aux;
  uint32_t n;
  int32_t x, y;

  m = &solver->graph.matrix;
  val = solver->value;
  aux = &solver->aux;
  n = solver->nvertices;
  for (x=0; x<n; x++) {
    for (y=0; y<n; y++) {
      cell = rdl_cell(m, x, y);
      if (cell->id >= 0) {
        // aux := val[x] - val[y]
        q_set(aux, val + x);
        q_sub(aux, val + y);
        // check whether aux <= dist[x, y]
        if (rdl_const_lt_q(&cell->dist, aux)) {
          printf("---> BUG: invalid RDL model\n");
          printf("   val[");
          print_rdl_vertex(stdout, x);
          printf("] = ");
          q_print(stdout, val + x);
          printf("\n");
          printf("   val[");
          print_rdl_vertex(stdout, y);
          printf("] = ");
          q_print(stdout, val + y);
          printf("\n");
          printf("   dist[");
          print_rdl_vertex(stdout, x);
          printf(", ");
          print_rdl_vertex(stdout, y);
          printf("] = ");
          print_rdl_const(stdout, &cell->dist);
          printf("\n");
          fflush(stdout);

          return false;
        }
      }
    }
  }

  return true;
}

#endif


/*
 * Build a mapping from variables to rationals
 */
void rdl_build_model(rdl_solver_t *solver) {
  byte_t *mark;
  uint32_t nvars;
  rational_t *aux;
  int32_t x;

  assert(solver->value == NULL);

  rdl_compute_model_epsilon(solver);
  assert(q_is_pos(&solver->epsilon));

  nvars = solver->nvertices;
  solver->value = new_rational_array(nvars);
  mark = allocate_bitvector0(nvars);
  aux = &solver->aux;

  // make sure the zero vertex has value 0
  x = solver->zero_vertex;
  if (x >= 0) {
    q_clear(aux);
    rdl_set_reference_point(solver, x, aux, mark);
  }

  // extend the model
  for (x=0; x<nvars; x++) {
    if (! tst_bit(mark, x)) {
      rdl_get_value_for_new_vertex(solver, x, aux, mark);
      rdl_set_reference_point(solver, x, aux, mark);
    }
  }


  delete_bitvector(mark);

  assert(good_rdl_model(solver));
}


/*
 * Free the model
 */
void rdl_free_model(rdl_solver_t *solver) {
  assert(solver->value != NULL);
  free_rational_array(solver->value, solver->nvertices);
  solver->value = NULL;
  q_clear(&solver->epsilon);
  q_clear(&solver->aux);
}



/*
 * Value of variable x in the model
 * - copy the value in v and return true
 */
bool rdl_value_in_model(rdl_solver_t *solver, thvar_t x, rational_t *v) {
  dl_triple_t *d;

  assert(solver->value != NULL && 0 <= x && x < solver->vtbl.nvars);
  d = dl_var_triple(&solver->vtbl, x);

  q_clear(v);
  if (d->target >= 0) {
    q_set(v, rdl_vertex_value(solver, d->target));
  }

  if (d->source >= 0) {
    q_sub(v, rdl_vertex_value(solver, d->source));
  }

  q_add(v, &d->constant);

  return true;
}


/*
 * Interface function: check whether x is an integer variable.
 */
bool rdl_var_is_integer(rdl_solver_t *solver, thvar_t x) {
  assert(0 <= x && x < solver->vtbl.nvars);
  return false;
}





/****************************
 *  INTERFACE DESCRIPTORS   *
 ***************************/

/*
 * Control interface
 */
static th_ctrl_interface_t rdl_control = {
  (start_intern_fun_t) rdl_start_internalization,
  (start_fun_t) rdl_start_search,
  (propagate_fun_t) rdl_propagate,
  (final_check_fun_t) rdl_final_check,
  (increase_level_fun_t) rdl_increase_decision_level,
  (backtrack_fun_t) rdl_backtrack,
  (push_fun_t) rdl_push,
  (pop_fun_t) rdl_pop,
  (reset_fun_t) rdl_reset,
  (clear_fun_t) rdl_clear,
};


/*
 * SMT interface: delete_atom and end_atom_deletion are not supported.
 */
static th_smt_interface_t rdl_smt = {
  (assert_fun_t) rdl_assert_atom,
  (expand_expl_fun_t) rdl_expand_explanation,
  (select_pol_fun_t) rdl_select_polarity,
  NULL,
  NULL,
};


/*
 * Internalization interface
 */
static arith_interface_t rdl_intern = {
  (create_arith_var_fun_t) rdl_create_var,
  (create_arith_const_fun_t) rdl_create_const,
  (create_arith_poly_fun_t) rdl_create_poly,
  (create_arith_pprod_fun_t) rdl_create_pprod,

  (create_arith_atom_fun_t) rdl_create_eq_atom,
  (create_arith_atom_fun_t) rdl_create_ge_atom,
  (create_arith_patom_fun_t) rdl_create_poly_eq_atom,
  (create_arith_patom_fun_t) rdl_create_poly_ge_atom,
  (create_arith_vareq_atom_fun_t) rdl_create_vareq_atom,

  (assert_arith_axiom_fun_t) rdl_assert_eq_axiom,
  (assert_arith_axiom_fun_t) rdl_assert_ge_axiom,
  (assert_arith_paxiom_fun_t) rdl_assert_poly_eq_axiom,
  (assert_arith_paxiom_fun_t) rdl_assert_poly_ge_axiom,
  (assert_arith_vareq_axiom_fun_t) rdl_assert_vareq_axiom,
  (assert_arith_cond_vareq_axiom_fun_t) rdl_assert_cond_vareq_axiom,
  (assert_arith_clause_vareq_axiom_fun_t) rdl_assert_clause_vareq_axiom,

  NULL, // attach_eterm is not supported
  NULL, // eterm of var is not supported

  (build_model_fun_t) rdl_build_model,
  (free_model_fun_t) rdl_free_model,
  (arith_val_in_model_fun_t) rdl_value_in_model,

  (arith_var_is_int_fun_t) rdl_var_is_integer,
};






/*****************
 *  FULL SOLVER  *
 ****************/

/*
 * Initialize solver:
 * - core = attached smt_core solver
 * - gates = the attached gate manager
 */
void init_rdl_solver(rdl_solver_t *solver, smt_core_t *core, gate_manager_t *gates) {
  solver->core = core;
  solver->gate_manager = gates;
  solver->base_level = 0;
  solver->decision_level = 0;
  solver->unsat_before_search = false;

  init_dl_vartable(&solver->vtbl);

  solver->nvertices = 0;
  solver->zero_vertex = null_rdl_vertex;
  init_rdl_graph(&solver->graph);

  init_rdl_atbl(&solver->atoms, DEFAULT_RDL_ATBL_SIZE);
  init_rdl_astack(&solver->astack, DEFAULT_RDL_ASTACK_SIZE);
  init_rdl_undo_stack(&solver->stack, DEFAULT_RDL_UNDO_STACK_SIZE);
  init_rdl_trail_stack(&solver->trail_stack);

  init_int_htbl(&solver->htbl, 0);
  init_arena(&solver->arena);
  init_ivector(&solver->expl_buffer, DEFAULT_RDL_BUFFER_SIZE);
  init_ivector(&solver->aux_vector, DEFAULT_RDL_BUFFER_SIZE);
  init_rdl_const(&solver->c1);
  q_init(&solver->q);

  // triple + poly buffer
  solver->triple.target = nil_vertex;
  solver->triple.source = nil_vertex;
  q_init(&solver->triple.constant);
  init_poly_buffer(&solver->buffer);

  // Model construction objects
  q_init(&solver->epsilon);
  q_init(&solver->factor);
  q_init(&solver->aux);
  q_init(&solver->aux2);
  solver->value = NULL;

  // No jump buffer yet
  solver->env = NULL;

  // undo record for level 0
  push_undo_record(&solver->stack, -1, 0, 0);

  assert(valid_rdl_graph(&solver->graph));
}


/*
 * Delete solver
 */
void delete_rdl_solver(rdl_solver_t *solver) {
  delete_dl_vartable(&solver->vtbl);
  delete_rdl_graph(&solver->graph);
  delete_rdl_atbl(&solver->atoms);
  delete_rdl_astack(&solver->astack);
  delete_rdl_undo_stack(&solver->stack);
  delete_rdl_trail_stack(&solver->trail_stack);

  delete_int_htbl(&solver->htbl);
  delete_arena(&solver->arena);
  delete_ivector(&solver->expl_buffer);
  delete_ivector(&solver->aux_vector);
  clear_rdl_const(&solver->c1);
  q_clear(&solver->q);

  q_clear(&solver->triple.constant);
  delete_poly_buffer(&solver->buffer);

  q_clear(&solver->epsilon);
  q_clear(&solver->factor);
  q_clear(&solver->aux);
  q_clear(&solver->aux2);

  if (solver->value != NULL) {
    free_rational_array(solver->value, solver->nvertices);
    solver->value = NULL;
  }


}



/*
 * Attach a jump buffer
 */
void rdl_solver_init_jmpbuf(rdl_solver_t *solver, jmp_buf *buffer) {
  solver->env = buffer;
}



/*
 * Get the control and smt interfaces
 */
th_ctrl_interface_t *rdl_ctrl_interface(rdl_solver_t *solver) {
  return &rdl_control;
}

th_smt_interface_t *rdl_smt_interface(rdl_solver_t *solver) {
  return &rdl_smt;
}


/*
 * Get the internalization interface
 */
arith_interface_t *rdl_arith_interface(rdl_solver_t *solver) {
  return &rdl_intern;
}
