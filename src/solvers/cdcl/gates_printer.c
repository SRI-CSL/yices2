/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRINT BOOLEAN GATE STRUCTURES
 */

#include <inttypes.h>

#include "solvers/cdcl/gates_printer.h"
#include "solvers/cdcl/smt_core_printer.h"


static const char * const boolop2string[] = {
  "XOR", "OR", "ITE", "CMP", "HALFADD", "FULLLADD", "<invalid gate>",
};

static void print_gate_op(FILE *f, uint32_t tag) {
  gate_op_t op;
  op = tag_combinator(tag);
  if (op > GTAG_NUM_OPS) op = GTAG_NUM_OPS;
  fputs(boolop2string[op], f);
}

void print_boolgate_old(FILE *f, boolgate_t *g) {
  uint32_t i, d, n, tag;

  tag = g->tag;
  d = tag_indegree(tag);
  n = d + tag_outdegree(tag);

  print_gate_op(f, tag);
  fputc('(', f);
  for (i=0; i<n; i++) {
    if (i == d) {
      fputs(")(", f);
    } else if (i > 0) {
      fputc(' ', f);
    }
    print_literal(f, g->lit[i]);
  }
  fputc(')', f);
}


void print_boolgate(FILE *f, boolgate_t *g) {
  uint32_t i, d, tag;
  gate_op_t op;

  tag = g->tag;
  d = tag_indegree(tag);
  op = tag_combinator(tag);

  switch (op) {
  case XOR_GATE:
  case OR_GATE:
  case ITE_GATE:
  case CMP_GATE:
    assert(tag_outdegree(tag) == 1);
    print_literal(f, g->lit[d]);
    fputs(" := ", f);
    print_gate_op(f, tag);
    fputc('(', f);
    for (i=0; i<d; i++) {
      if (i > 0) fputc(' ', f);
      print_literal(f, g->lit[i]);
    }
    fputs(")\n",f);
    break;

  case HALFADD_GATE:
    assert(tag_outdegree(tag) == 2);
    print_literal(f, g->lit[d]);
    fputs(" := XOR(", f);
    for (i=0; i<d; i++) {
      if (i > 0) fputc(' ', f);
      print_literal(f, g->lit[i]);
    }
    fputs(")\n",f);
    fputs("    ", f);
    print_literal(f, g->lit[d+1]);
    fputs(" := AND(", f);
    for (i=0; i<d; i++) {
      if (i > 0) fputc(' ', f);
      print_literal(f, g->lit[i]);
    }
    fputs(")\n",f);
    break;

  case FULLADD_GATE:
    assert(tag_outdegree(tag) == 2);
    print_literal(f, g->lit[d]);
    fputs(" := SUM(", f);
    for (i=0; i<d; i++) {
      if (i > 0) fputc(' ', f);
      print_literal(f, g->lit[i]);
    }
    fputs(")\n",f);
    fputs("    ", f);
    print_literal(f, g->lit[d+1]);
    fputs(" := MAJ(", f);
    for (i=0; i<d; i++) {
      if (i > 0) fputc(' ', f);
      print_literal(f, g->lit[i]);
    }
    fputs(")\n",f);
    break;
  }

}


/*
 * Print all gates in the list
 */
void print_boolgate_list(FILE *f, lnkgate_t *list) {
  while (list != NULL) {
    fputs("    ", f);
    print_boolgate(f, &list->gate);
    fputc('\n', f);
    list = list->next;
  }
}


/*
 * List of gates + creation level
 */
void print_boolgate_levlist(FILE *f, levlist_t *lv) {
  fprintf(f, "  gates at level %"PRIu32"\n", lv->level);
  print_boolgate_list(f, lv->list);
}


/*
 * Push/pop stack in gate_table
 */
void print_gate_table_stack(FILE *f, gate_table_t *tbl) {
  levlist_stack_t *stack;
  uint32_t i;

  stack = &tbl->stack;
  fprintf(f, "Trail stack for gate table %p\n", tbl);
  fprintf(f, "  current level = %"PRIu32"\n", stack->current_level);
  fprintf(f, "  top level = %"PRIu32"\n", stack->top_level);
  for (i=0; i<stack->nlists; i++) {
    print_boolgate_levlist(f, stack->data + i);
  }
}


/*
 * Print all gates in table data: n = its size
 */
static void print_gates_in_table(FILE *f, boolgate_t **data, uint32_t n) {
  uint32_t i;
  boolgate_t *g;

  for (i=0; i<n; i++) {
    g = data[i];
    if (g != NULL && g != DELETED_GATE) {
      fputs("    ", f);
      print_boolgate(f, g);
      fputc('\n', f);
    }
  }
}


/*
 * Details of the hash-table
 */
void print_gate_table_htbl(FILE *f, gate_table_t *tbl) {
  gate_htbl_t *htbl;

  htbl = &tbl->htbl;
  fprintf(f, "Hash table for gate table %p\n", tbl);
  fprintf(f, "  size = %"PRIu32"\n", htbl->size);
  fprintf(f, "  nelems = %"PRIu32"\n", htbl->nelems);
  fprintf(f, "  ndeleted = %"PRIu32"\n", htbl->ndeleted);
  fprintf(f, "  resize threshold = %"PRIu32"\n", htbl->resize_threshold);
  fprintf(f, "  cleanup threshold = %"PRIu32"\n", htbl->cleanup_threshold);
  fputs("  Content\n", f);
  print_gates_in_table(f, htbl->data, htbl->size);
  fputc('\n', f);
}


/*
 * Less-detailed view
 */
void print_gate_table(FILE *f, gate_table_t *tbl) {
  if (tbl->htbl.nelems == 0) {
    fprintf(f, "Gate table %p is empty\n", tbl);
  } else {
    fprintf(f, "Content of gate table %p\n", tbl);
    print_gates_in_table(f, tbl->htbl.data, tbl->htbl.size);
  }
}


