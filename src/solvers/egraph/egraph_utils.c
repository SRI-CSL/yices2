/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * UTILITIES: ACCESS TO INTERNAL EGRAPH STRUCTURES
 */

#include "solvers/egraph/egraph_utils.h"
#include "utils/int_hash_map.h"

/*
 * Allocate and initialize the internal imap
 */
void egraph_alloc_imap(egraph_t *egraph) {
  assert(egraph->imap == NULL);
  egraph->imap = (int_hmap_t *) safe_malloc(sizeof(int_hmap_t));
  init_int_hmap(egraph->imap, 0);
}




/*
 * SUPPORT FOR GARBAGE COLLECTOR
 */

/*
 * Mark all types present in eterm table
 * - types = the relevant type table
 */
static void eterm_table_gc_mark(eterm_table_t *tbl, type_table_t *types) {
  uint32_t i, n;
  type_t tau;

  n = tbl->nterms;
  for (i=0; i<n; i++) {
    tau = tbl->real_type[i];
    if (tau != NULL_TYPE) { // not sure this test is necessary
      type_table_set_gc_mark(types, tau);
    }
  }
}

/*
 * Mark all types present in lambda tag table
 * - types = relevant type table
 */
static void ltag_table_gc_mark(ltag_table_t *tbl, type_table_t *types) {
  ltag_desc_t *d;
  uint32_t i, ntags;
  uint32_t j ,n;

  ntags = tbl->ntags;
  for (i=0; i<ntags; i++) {
    d = tbl->data[i];
    n = d->arity;
    for (j=0; j<n; j++) {
      type_table_set_gc_mark(types, d->dom[j]);
    }
  }
}

/*
 * Mark all types used by egraph to preserve them from deletion on
 * the next call to type_table_gc.
 *
 * Marked types include:
 * - any type tau that occurs in egraph->terms.real_type[i]
 * - all types that occur in egraph->tag_table.
 */
void egraph_gc_mark(egraph_t *egraph) {
  eterm_table_gc_mark(&egraph->terms, egraph->types);
  ltag_table_gc_mark(&egraph->tag_table, egraph->types);
}

