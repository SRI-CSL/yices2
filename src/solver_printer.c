/*
 * Print solver data
 */

#include <inttypes.h>

#include "refcount_strings.h"
#include "int_hash_sets.h"
#include "int_array_sort.h"
#include "prng.h"
#include "pointer_vectors.h"
#include "ptr_vectors.h"

#include "term_printer.h"
#include "solver_printer.h"

// #include "theory_explanations.h"
// #include "egraph_utils.h"
// #include "translation.h"



#if 0

/****************
 *  NAME TABLE  *
 ***************/

/*
 * The name table can be setup for a single context, after internalization.
 * The table keeps track of the mappings from solver objects to the name 
 * of the corresponding term in the global term table.
 */
static uint32_t name_size = 0;
static char **name = NULL;

/*
 * Initialization based on a context
 */
void printer_init(context_t *ctx) {
  translator_t *trans;
  term_table_t *terms;
  uint32_t i, n, m;
  eterm_t t;
  icode_t code;
  char *aux;

  assert(name == NULL && name_size ==0);

  trans = &ctx->trans;
  terms = ctx->terms;
  n = trans->term_map.size;
  m = 0;

  for (i=0; i<n; i++) {
    code = code_of_term(trans, i);
    if (code_is_valid(code) && code_is_eterm(code)) {
      t = code2eterm(code);
      aux = term_name(terms, i);
      if (aux != NULL && m < t) {
	m = t;
      }
    }
  }

  m ++;
  name = (char **) safe_malloc(m * sizeof(char *));
  name_size = m;

  for (i=0; i<m; i++) name[i] = NULL;

  for (i=0; i<n; i++) {
    code = code_of_term(trans, i);
    if (code_is_valid(code) && code_is_eterm(code)) {
      t = code2eterm(code);
      aux = term_name(terms, i);
      assert(aux == NULL || t < m);
      if (aux != NULL && name[t] == NULL) {
	string_incref(aux);
	name[t] = aux;
      }
    }
  }
}

/*
 * Free memory
 */
void printer_cleanup(void) {
  uint32_t i, n;
  char *aux;

  n = name_size;
  for (i=0; i<n; i++) {
    aux = name[i];
    if (aux != NULL) string_decref(aux);
  }

  safe_free(name);
  name = NULL;
  name_size = 0;
}


#endif



/********************************
 *  BASIC CORE/EGRAPH OBJECTS   *
 *******************************/

/*
 * Print basic objects from smt_core and egraph
 */
static const char * const bval2string[] = {
  "false", "undef", "true", "<invalid bval>",
};

static const char * const status2string[] = {
  "idle", "searching", "unknown", "sat", "unsat", "interrupted", 
  "<invalid status>",
};

static const char * const etype2string[] = {
  "int ", "real", "bv  ", "fun ", "bool", "tupl", "none", "<invalid etype>",
};

static const char * const etype2theory[] = {
  "arith", "ariht", "bv", "fun", "bool", "tuple", "none", "<invalid etype>",  
};

static const char * const cmpkind2string[] = {
  "apply", "update", "tuple", "eq", "ite", "distinct", "or", "<invalid composite kind>",
};

static const char * const boolop2string[] = {
  "XOR", "OR", "ITE", "CMP", "HALFADD", "FULLLADD", "<invalid gate>",
};

/*
 * Boolean value
 */
void print_bval(FILE *f, bval_t b) {
  if (b < 0 || b > VAL_TRUE) {
    b = VAL_TRUE + 1;
  }
  fputs(bval2string[b], f);
}

/*
 * Status
 */
void print_status(FILE *f, smt_status_t s) {
  if (s > STATUS_INTERRUPTED) {
    s = STATUS_INTERRUPTED + 1;
  }
  fputs(status2string[s], f);
}

/*
 * Boolean variable
 */
void print_bvar(FILE *f, bvar_t x) {
  if (x < 0) {
    if (x == null_bvar) {
      fputs("null_bvar", f);
    } else {
      fprintf(f, "BVAR%"PRId32, x);
    }
  } else if (x == bool_const) {
    fputs("true", f);
  } else {
    fprintf(f, "p!%"PRId32, x);
  }
}

/*
 * Literal
 */
void print_literal(FILE *f, literal_t l) {
  if (l < 0) {
    if (l == null_literal) {
      //      fputs("null_literal", f);
      fputs("nil", f);
    } else {
      fprintf(f, "LIT%"PRId32, l);
    }
  } else if (l == true_literal) {
    fputs("tt", f);      
  } else if (l == false_literal) {
    fputs("ff", f);
  } else {
    if (is_neg(l)) fputc('~', f);
    fprintf(f, "p!%"PRId32, var_of(l));
  }
}


#if 0

/*
 * Basic egraph objects
 */
void print_etype(FILE *f, etype_t tau) {
  if (tau < 0 || tau > NUM_ETYPES) {
    tau = NUM_ETYPES;
  }
  fputs(etype2string[tau], f);
}


/*
 * Theory name for type tau
 */
void print_theory_id(FILE *f, etype_t tau) {
  if (tau < 0 || tau > NUM_ETYPES) {
    tau = NUM_ETYPES;
  }
  fputs(etype2theory[tau], f);  
}


/*
 * Term id
 */
static void print_eterm_name(FILE *f, eterm_t t) {
  assert(t >= 0);
  if (t < name_size && name[t] != NULL) {
    fputs(name[t], f);
  } else {
    fprintf(f, "g!%"PRId32, t);
  }
}

void print_eterm_id(FILE *f, eterm_t t) {
  if (t <= 0) {
    if (t == null_eterm) {
      fputs("null_eterm", f);
    } else if (t == true_eterm) {
      fputs("tt", f);
    } else {
      fprintf(f, "ETERM%"PRId32, t);
    }
  } else {
    print_eterm_name(f, t);
  }
}

/*
 * Theory variable
 */
void print_thvar(FILE *f, thvar_t v) {
  if (v < 0) {
    if (v == null_thvar) {
      fputs("null_thvar", f);
    } else {
      fprintf(f, "THVAR%"PRId32, v);
    }
  } else {
    fprintf(f, "v!%"PRId32, v);
  }
}


/*
 * Term id + polarity
 */
void print_occurrence(FILE *f, occ_t t) {
  if (t < 0) {
    if (t == null_occurrence) {
      fputs("null", f);
    } else {
      fprintf(f, "OCC%"PRId32, t);
    }
  } else if (t == true_occ) {
    fputs("tt", f);
  } else if (t == false_occ) {
    fputs("ff", f);
  } else {
    if (is_neg_occ(t)) fputc('~', f);
    print_eterm_name(f, term_of(t));
  }
}

/*
 * Class id
 */
void print_class_id(FILE *f, class_t c) {
  if (c < 0) {
    if (c == null_class) {
      fputs("null_class", f);
    } else {
      fprintf(f, "CLASS%"PRId32, c);
    }
  } else {
    fprintf(f, "C!%"PRId32, c);
  }
}

/*
 * Label: class id + polarity
 */
void print_label(FILE *f, elabel_t l) {
  char sgn;

  if (l < 0) {
    if (l == null_label) {
      fputs("null_label", f);
    } else {
      fprintf(f, "LABEL%"PRId32, l);
    }
  } else {
    fprintf(f, "C!%"PRId32, class_of(l));
    sgn = is_pos_label(l) ? '+' : '-';
    fputc(sgn, f);
  }
}


/*
 * Dmask: bit vector
 */
void print_dmask(FILE *f, uint32_t d) {
  uint32_t k, m;
  char bit;

  m = ((uint32_t) 1) << 31;
  for (k=0; k<32; k++) {
    bit = '0';
    if ((d & m) != 0) bit = '1';
    fputc(bit, f);
    m >>= 1;
  }
}

#endif


/*
 * CORE: INTERNAL OBJECTS
 */

/*
 * Clause
 */
void print_clause(FILE *f, clause_t *cl) {
  uint32_t i;
  literal_t l;

  fputc('{', f);
  print_literal(f, cl->cl[0]);
  i = 1;
  l = cl->cl[i];
  while (l >= 0) {
    fputc(' ', f);
    print_literal(f, l);
    i ++;
    l = cl->cl[i];
  }
  fputc('}', f);
}


/*
 * Print unit clauses = all the literals in core->stack[0 .. core->nb_units-1]
 */
void print_unit_clause(FILE *f, literal_t l) {
  fputc('{', f);
  print_literal(f, l);
  fputc('}', f);
}

void print_unit_clauses(FILE *f, smt_core_t *core) {
  prop_stack_t *stack;
  uint32_t i, n;

  n = core->nb_unit_clauses;
  stack = &core->stack;
  for (i=0; i<n; i++) {
    print_unit_clause(f, stack->lit[i]);
    fputc('\n', f);
  }
}


/*
 * Print array a, formatted as a clause
 */
void print_litarray(FILE *f, uint32_t n, literal_t *a) {
  uint32_t i;

  fputc('{', f);
  if (n > 0) {
    print_literal(f, a[0]);
    for (i=1; i<n; i++) {
      fputc(' ', f);
      print_literal(f, a[i]);
    }
  }
  fputc('}', f);
}


/*
 * Print binary and problem clauses
 */
void print_binary_clause(FILE *f, literal_t l1, literal_t l2) {
  fputc('{', f);
  print_literal(f, l1);
  fputc(' ', f);
  print_literal(f, l2);
  fputc('}', f);
}

void print_binary_clauses(FILE *f, smt_core_t *core) {
  int32_t n;
  literal_t l1, l2;
  literal_t *bin;

  n = core->nlits;  
  for (l1=0; l1<n; l1++) {
    bin = core->bin[l1];
    if (bin != NULL) {
      for (;;) {
	l2 = *bin++;
	if (l2 < 0) break;
	if (l1 <= l2) {
	  print_binary_clause(f, l1, l2);
	  fputc('\n', f);
	}
      }
    }
  }
}

static void print_clause_vector(FILE *f, clause_t **vector) {
  uint32_t i, n;

  n = get_cv_size(vector);
  for (i=0; i<n; i++) {
    print_clause(f, vector[i]);
    fputc('\n', f);
  }
}

void print_problem_clauses(FILE *f, smt_core_t *core) {
  print_clause_vector(f, core->problem_clauses);
}

void print_learned_clauses(FILE *f, smt_core_t *core) {
  print_clause_vector(f, core->learned_clauses);
}

void print_clauses(FILE *f, smt_core_t *core) {
  print_unit_clauses(f, core);
  print_binary_clauses(f, core);
  print_problem_clauses(f, core);
  fputc('\n', f);
}

void print_all_clauses(FILE *f, smt_core_t *core) {
  print_binary_clauses(f, core);
  fputc('\n', f);
  print_problem_clauses(f, core);  
  fputc('\n', f);
  print_learned_clauses(f, core);
  fputc('\n', f);
}

/* 
 * Find the length of a lemma a: 
 * - a must be terminated by null_literal (or any negative end marker)
 */
static uint32_t lemma_length(literal_t *a) {
  uint32_t n;

  n = 0;
  while (*a >= 0) {
    a ++;
    n ++;
  }
  return n;
}

 
/*
 * Print all lemmas
 */
void print_lemmas(FILE *f, smt_core_t *core) {
  lemma_block_t *tmp;
  literal_t *lemma;
  uint32_t i, j, n;

  for (i=0; i<core->lemmas.free_block; i++) {
    tmp = core->lemmas.block[i];
    lemma = tmp->data;
    j = 0;
    while (j < tmp->ptr) {
      n = lemma_length(lemma);
      print_litarray(f, n, lemma);
      fputc('\n', f);
      n ++;
      j += n;
      lemma += n;
    }
  }
}


/*
 * Print assignment
 */
void print_boolean_assignment(FILE *f, smt_core_t *core) {
  prop_stack_t *stack;
  uint32_t i, n;
  literal_t l;

  stack = &core->stack;
  n = stack->top;
  for (i=0; i<n; i++) {
    l = stack->lit[i];
    fputc(' ', f);
    if (is_pos(l)) fputc(' ', f);
    print_literal(f, l);
    fprintf(f, " level = %"PRIu32"\n", core->level[var_of(l)]);
  }
}

/*
 * Print conflict data
 */
void print_conflict(FILE *f, smt_core_t *core) {
  literal_t l;
  uint32_t i;

  if (core->inconsistent) {
    i = 0;
    l = core->conflict[i];
    if (l < 0) {
      fputs("Conflict: empty clause\n", f);
    } else {
      fputs("Conflict:", f);    
      while (l >= 0) {
	fputc(' ', f);
	print_literal(f, l);
	i ++;
	l = core->conflict[i];
      }
      fputc('\n', f);
    }

  } else {
    fputs("No conflict\n", f);
  }
}

/*
 * Print current state of core
 * (This needs to be exported for now, because it's used in the tests)
 */
void print_smt_core(FILE *f, smt_core_t *core) {
  fprintf(f, "SMT Core %p\n", core);
  fprintf(f, "  %"PRIu32" variables\n", core->nvars);
  fprintf(f, "  %"PRIu32" unit clauses\n", core->nb_unit_clauses);
  fprintf(f, "  %"PRIu32" binary clauses\n", core->nb_bin_clauses);
  fprintf(f, "  %"PRIu32" problem clauses\n", get_cv_size(core->problem_clauses));
  fprintf(f, "  %"PRIu32" learned clauses\n", get_cv_size(core->learned_clauses));
  fprintf(f, "status = %s\n", status2string[core->status]);
  fprintf(f, "base_level = %"PRIu32"\n", core->base_level);
  fprintf(f, "decision_level = %"PRIu32"\n", core->decision_level);
  print_conflict(f, core);
  fprintf(f, "Assignment:\n");
  print_boolean_assignment(f, core);
  fprintf(f, "Clauses:\n");
  print_unit_clauses(f, core);
  print_binary_clauses(f, core);
  print_problem_clauses(f, core);
  print_learned_clauses(f, core);
  fputc('\n', f);
  fflush(f);
}




/*
 * BOOLEAN GATES
 */
static void print_gate_op(FILE *f, uint32_t tag) {
  gate_op_t op;
  op = tag_combinator(tag);
  if (op > GTAG_NUM_OPS) op = GTAG_NUM_OPS;
  fputs(boolop2string[op], f);
}

void print_boolgate(FILE *f, boolgate_t *g) {
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


#if 0


/*
 * EGRAPH: INTERNAL STATE
 */
static void print_kind(FILE *f, composite_kind_t k) {
  if (k < 0 || k > COMPOSITE_OR) {
    k = COMPOSITE_OR + 1;
  }
  fputs(cmpkind2string[k], f);
}

void print_composite(FILE *f, composite_t *c) {
  uint32_t i, n;
  composite_kind_t k;

  k = composite_kind(c);
  n = composite_arity(c);

  fputc('(', f);
  if (k != COMPOSITE_APPLY) { 
    print_kind(f, composite_kind(c));
    for (i=0; i<n; i++) {
      fputc(' ', f);
      print_occurrence(f, c->child[i]);
    }
  } else {
    print_occurrence(f, c->child[0]);
    for (i=1; i<n; i++) {
      fputc(' ', f);
      print_occurrence(f, c->child[i]);
    }
  }
  fputc(')', f);
}

void print_signature(FILE *f, signature_t *s) {
  uint32_t i, n;

  n = tag_arity(s->tag);
  fputc('[', f);
  print_kind(f, tag_kind(s->tag));
  for (i=0; i<n; i++) {
    fputc(' ', f);
    print_label(f, s->sigma[i]);
  }
  fputc(']', f);
}





/*
 * Parent vectors: skip all non-valid entries
 */
void print_parents(FILE *f, use_vector_t *v) {
  uint32_t i, n;
  composite_t *p;

  n = v->last;
  for (i=0; i<n; i++) {
    p = v->data[i];
    if (valid_entry(p)) {
      fputs("  ", f);
      print_composite(f, p);
      fputc('\n', f);
    }
  }
}


void print_parents_details(FILE *f, use_vector_t *v) {
  uint32_t i, n;
  composite_t *p;

  n = v->last;
  for (i=0; i<n; i++) {
    p = v->data[i];
    if (valid_entry(p)) {
      fputs("  ", f);
      print_composite(f, p);
      fputc('\n', f);
    } else if (marked_entry(p)) {
      fputs("  ", f);
      print_composite(f, unmark_entry(p));      
      fputs(" [hidden]\n", f);
    }
  }
}


/*
 * Print a theory explanation
 */
void print_th_eq(FILE *f, th_eq_t *eq) {
  fputc('(', f);
  print_eterm_id(f, eq->lhs);
  fputs(" = ", f);
  print_eterm_id(f, eq->rhs);
  fputc(')', f);
}

void print_th_diseq(FILE *f, diseq_pre_expl_t *diseq) {
  fputc('(', f);
  print_eterm_id(f, diseq->t1);
  fputs(" != ", f);
  print_eterm_id(f, diseq->t2);
  fputc(')', f);
}

static void print_literal_array(FILE *f, literal_t *a, uint32_t n) {
  uint32_t i;

  assert(n > 0);
  i = 0;
  for (;;) {
    print_literal(f, a[i]);
    i ++;
    if (i >= n) break;
    fputc(' ', f);
  }
}



static void print_th_eq_array(FILE *f, th_eq_t *a, uint32_t n) {
  uint32_t i;

  assert(n > 0);
  i = 0;
  for (;;) {
    print_th_eq(f, a + i);
    i ++;
    if (i >= n) break;
    fputc(' ', f);
  }
}

static void print_th_diseq_array(FILE *f, diseq_pre_expl_t *a, uint32_t n) {
  uint32_t i;

  assert(n > 0);
  i = 0;
  for (;;) {
    print_th_diseq(f, a + i);
    i ++;
    if (i >= n) break;
    fputc(' ', f);
  }  
}

void print_theory_explanation(FILE *f, th_explanation_t *e) {
  literal_t *atoms;
  th_eq_t *eqs;
  diseq_pre_expl_t *diseqs;
  bool empty;

  empty = true;

  atoms = e->atoms;
  if (atoms != NULL && get_av_size(atoms) > 0) {
    print_literal_array(f, atoms, get_av_size(atoms));
    empty = false;
  }

  eqs = e->eqs;
  if (eqs != NULL && get_eqv_size(eqs) > 0) {
    if (! empty) fputc(' ', f);
    print_th_eq_array(f, eqs, get_eqv_size(eqs));
    empty = false;
  }

  diseqs = e->diseqs;
  if (diseqs != NULL && get_diseqv_size(diseqs) > 0) {
    if (! empty) fputc(' ', f);
    print_th_diseq_array(f, diseqs, get_diseqv_size(diseqs));
    empty = false;
  }

  if (empty) {
    fputs("<empty explanation>", f);
  }
  fflush(f);
}



/*
 * Term in egraph
 */
void print_eterm(FILE *f, egraph_t *egraph, eterm_t t) {
  composite_t *c;

  c = egraph_term_body(egraph, t);
  if (atomic_body(c)) {
    print_eterm_id(f, t);
  } else {
    print_composite(f, c);
  }
}

void print_eterm_def(FILE *f, egraph_t *egraph, eterm_t t) {
  composite_t *c;
#if 0
  thvar_t x;
  etype_t tau;
#endif

  print_eterm_id(f, t);
  c = egraph_term_body(egraph, t);
  if (constant_body(c)) {
    fputs(" (constant)\n", f);
  } else if (c == VARIABLE_BODY) {
    fputs(" (variable)\n", f);
  } else if (c == NULL) {
    fputs(" (deleted)\n", f);
  } else {
    fputs(" := ", f);
    print_composite(f, c);
    fputc('\n', f);
  }

#if 0
  x = egraph_term_base_thvar(egraph, t);
  if (x != null_thvar) {
    fputs("   thvar: ", f);    
    print_thvar(f, x);
    tau = egraph_term_type(egraph, t);
    fputs(", ", f);
    print_theory_id(f, tau);
    fputc('\n', f);
  }
#endif

}


void print_eterm_details(FILE *f, egraph_t *egraph, eterm_t t) {
  composite_t *c;

  fputs("--- Term ", f);
  print_eterm_id(f, t);
  fputs(" ---\n", f);

  c = egraph_term_body(egraph, t);
  if (constant_body(c)) {
    fputs("constant\n", f);
  } else if (c == VARIABLE_BODY) {
    fputs("variable\n", f);
  } else if (c == NULL) {
    fputs("deleted\n", f);
  } else {
    fputs("body: ", f);
    print_composite(f, c);
    fputc('\n', f);
  }

  if (c != NULL) {
    fputs("label: ", f);
    print_label(f, egraph_term_label(egraph, t));
    fputc('\n', f);
  }
}


static void print_list(FILE *f, egraph_t *egraph, occ_t t1) {
  occ_t t;

  t = t1;
  do {
    fputc(' ', f);
    print_occurrence(f, t);
    t = egraph_next(egraph, t);
  } while (t != t1);
}

void print_class(FILE *f, egraph_t *egraph, class_t c) {
  print_class_id(f, c);
  fputs(" := {", f);
  print_list(f, egraph, egraph_class_root(egraph, c));
  fputs(" }\n", f);
}


void print_class_details(FILE *f, egraph_t *egraph, class_t c) {
  occ_t root;
  eterm_t t;

  fputs("--- Class ", f);
  print_class_id(f, c);
  fputs("---\n", f);

  root = egraph_class_root(egraph, c);
  fputs("root: ", f);
  print_occurrence(f, root);
  fputc('\n', f);

  fputs("dmask: ", f);
  print_dmask(f, egraph_class_dmask(egraph, c));
  fputc('\n', f);
  
  fputs("type: ", f);
  print_etype(f, egraph_class_type(egraph, c));
  fputc('\n', f);

  fputs("thvar: ", f);
  print_thvar(f, egraph_class_thvar(egraph, c));
  fputc('\n', f);

  fputs("members: ", f);
  print_list(f, egraph, root);
  fputc('\n', f);

  fputs("member defs:\n", f);
  t = term_of(root);
  do {
    fputs("  ", f);
    print_eterm_def(f, egraph, t);
    t = egraph_term_next(egraph, t);
  } while (t != term_of(root));

  fputs("parents:\n", f);
  print_parents_details(f, egraph_class_parents(egraph, c));
  fputc('\n', f);
}


void print_class_of_occ(FILE *f, egraph_t *egraph, occ_t t) {
  fputs("class of ", f);
  print_occurrence(f, t);
  fputs(": ", f);
  print_label(f, egraph_label(egraph, t));
  fputs(" = {", f);
  print_list(f, egraph, t);
  fputs(" }\n", f);
}

void print_class_of_term(FILE *f, egraph_t *egraph, eterm_t t) {
  print_class_of_occ(f, egraph, pos_occ(t));
}



/*
 * Parents of all terms in t's class
 */
void print_parents_of_term(FILE *f, egraph_t *egraph, eterm_t t) {
  class_t c;

  fputs("parents of ", f);
  print_eterm_name(f, t);
  fputs(":\n", f);
  c = egraph_term_class(egraph, t);
  print_parents(f, egraph_class_parents(egraph, c));
}



/*
 * Egraph atom 
 */
void print_egraph_atom(FILE *f, egraph_t *egraph, atom_t *atom) {
  fputc('[', f);
  print_bvar(f, atom->boolvar);
  fputs(" := ", f);
  print_eterm(f, egraph, atom->eterm);
  fputc(']', f);
}


void print_egraph_atom_of_literal(FILE *f, egraph_t *egraph, literal_t l) {
  void *atom;
  bvar_t v;

  v = var_of(l);
  assert(bvar_has_atom(egraph->core, v));
  atom = bvar_atom(egraph->core, v);
  assert(atom_tag(atom) == EGRAPH_ATM_TAG);
  if (is_neg(l)) {
    fputs("(not ", f);
  }
  print_eterm(f, egraph, ((atom_t *) untag_atom(atom))->eterm);
  if (is_neg(l)) {
    fputc(')', f);
  }
}



/*
 * Print definitions of all terms
 */
EXPORTED
void print_egraph_terms(FILE *f, egraph_t *egraph) {
  composite_t *c;
  uint32_t i, n;
  thvar_t x;

  n = egraph->terms.nterms;
  for (i=0; i<n; i++) {
    print_eterm_id(f, i);
    c = egraph_term_body(egraph, i);
    if (constant_body(c)) {
      fputs(" (constant)       ", f);
    } else if (c == VARIABLE_BODY) {
      fputs(" (variable)       ", f);
    } else if (c == NULL) {
      fputs(" (deleted)        ", f);
    } else {
      fputs(" := ", f);
      print_composite(f, c);
    }
    fputs("\t\t", f);
    print_type(f, egraph_term_real_type(egraph, i));
    //    fputs("\t\tetype = ", f);
    //    print_etype(f, egraph_class_type(egraph, i));
    x = egraph_term_base_thvar(egraph, i);
    if (x != null_thvar) {
      fputs("\t\t", f);
      switch(egraph_term_type(egraph, i)) {
      case ETYPE_INT:
	fprintf(f, "arith(i!%"PRId32")\t\t", x);
	// HACK
	print_simplex_var_value(f, egraph->th[ETYPE_INT], x);
	break;
      case ETYPE_REAL:
	fprintf(f, "arith(z!%"PRId32")\t\t", x);
	// HACK
	print_simplex_var_value(f, egraph->th[ETYPE_INT], x);
	break;
      case ETYPE_BV:
	fprintf(f, "bv(u!%"PRId32")\t\t", x);
	// HACK
	print_bvsolver_var_value(f, egraph->th[ETYPE_BV], x);
	break;
      case ETYPE_FUNCTION:
	fprintf(f, "fun(f!%"PRId32")", x);
	break;
      case ETYPE_BOOL:
	fprintf(f, "lit(p!%"PRId32")\t\t", x);
	print_bval(f, bvar_value(egraph->core, x));
	break;
      case ETYPE_TUPLE:
	fprintf(f, "tup(g!%"PRId32")", x);
	break;
      default:
	fprintf(f, "BADTHVAR(%"PRId32")", x);
	break;
      }
    } else {
      if (egraph_term_is_true(egraph, i)) {
	fputs("\t\t(true term)", f);
      } else if (egraph_term_is_false(egraph, i)) {
	fputs("\t\t(false term)", f);
      }
    }

    fputc('\n', f);
  }
}

EXPORTED
void print_egraph_terms_details(FILE *f, egraph_t *egraph) {
  uint32_t i, n;

  n = egraph->terms.nterms;
  for (i=0; i<n; i++) {
    print_eterm_details(f, egraph, i);
  }
}

/*
 * Collect the root classes (and sort them)
 */
static void collect_root_classes(egraph_t *egraph, int_hset_t *roots) {
  uint32_t i, n;
  n = egraph->terms.nterms;
  for (i=0; i<n; i++) {
    if (egraph->terms.body[i] != NULL) {
      int_hset_add(roots, egraph_term_class(egraph, i));
    }
  }
  int_hset_close(roots);

  // coercion to (int32_t *) is safe since class_ids are less than INT32_MAX
  int_array_sort((int32_t *)roots->data, roots->nelems);
}


EXPORTED
void print_egraph_root_classes(FILE *f, egraph_t *egraph) {
  uint32_t i, n;
  int_hset_t roots;

  init_int_hset(&roots, 0);
  collect_root_classes(egraph, &roots);

  n = roots.nelems;
  for (i=0; i<n; i++) {
    print_class(f, egraph, roots.data[i]);
  }

  delete_int_hset(&roots);
}


EXPORTED
void print_egraph_root_classes_details(FILE *f, egraph_t *egraph) {
  uint32_t i, n;
  int_hset_t roots;

  init_int_hset(&roots, 0);
  collect_root_classes(egraph, &roots);

  n = roots.nelems;
  for (i=0; i<n; i++) {
    print_class_details(f, egraph, roots.data[i]);
  }

  delete_int_hset(&roots);
}


/*
 * All atoms
 */
EXPORTED
void print_egraph_atoms(FILE *f, egraph_t *egraph) {
  smt_core_t *core;
  uint32_t v, n;
  void *atm;

  core = egraph->core;
  if (core != NULL) {
    n = num_vars(core);
    for (v=0; v<n; v++) {
      atm = bvar_atom(core, v);
      if (atm != NULL && atom_tag(atm) == EGRAPH_ATM_TAG) {
	print_egraph_atom(f, egraph, untag_atom(atm));
	fputc('\n', f);
      }
    }
  }
}






/*
 * Sort all composites in array a in increasing order of id.
 * - n = size of the array
 */
static void qsort_composite_array(composite_t **a, uint32_t n);

static void isort_composite_array(composite_t **a, uint32_t n) {
  uint32_t i, j;
  composite_t *x, *y;

  for (i=1; i<n; i++) {
    x = a[i];
    j = 0;
    while (a[j]->id < x->id) j++;
    while (j < i) {
      y = a[j]; a[j] = x; x = y;
      j ++;
    }
    a[j] = x;
  }
}

static void sort_composite_array(composite_t **a, uint32_t n) {
  if (n <= 10) {
    isort_composite_array(a, n);
  } else {
    qsort_composite_array(a, n);
  }
}

static void qsort_composite_array(composite_t **a, uint32_t n) {
  uint32_t i, j;
  composite_t *x, *y;

  // x = random pivot
  i = random_uint(n);
  x = a[i];

  // swap x and a[0]
  a[i] = a[0];
  a[0] = x;

  i = 0;
  j = n;

  do { j--; } while (a[j]->id > x->id);
  do { i++; } while (i <= j && a[i]->id < x->id);

  while (i < j) {
    y = a[i]; a[i] = a[j]; a[j] = y;

    do { j--; } while (a[j]->id > x->id);
    do { i++; } while (a[i]->id < x->id);
  }

  // pivot goes into a[j]
  a[0] = a[j];
  a[j] = x;

  // sort a[0...j-1] and a[j+1 .. n-1]
  sort_composite_array(a, j);
  j++;
  sort_composite_array(a + j, n - j);
}



/*
 * Collect all composites in the congruence table into vector v
 */
static void collect_congruence_roots(congruence_table_t *tbl, pvector_t *v) {
  uint32_t i, n;
  composite_t *tmp;

  n = tbl->size;
  for (i=0; i<n; i++) {
    tmp = tbl->data[i];
    if (tmp != NULL_COMPOSITE && tmp != DELETED_COMPOSITE) {
      pvector_push(v, tmp);
    }
  }
  sort_composite_array((composite_t **) v->data, v->size);
}



/*
 * Print a congruence root c = composite in the congruence table
 */
static void print_congruence_root(FILE *f, composite_t *c) {
  print_eterm_id(f, c->id);
  fputs(" := ", f);
  print_composite(f, c);
  fputc('\n', f);
}


void print_egraph_congruence_roots(FILE *f, egraph_t *egraph) {
  uint32_t i, n;
  pvector_t v;

  init_pvector(&v, 10);
  collect_congruence_roots(&egraph->ctable, &v);
  n = v.size;
  if (n > 0) {
    fputs("--- Congruence roots ---\n", f);    
    for (i=0; i<n; i++) {
      print_congruence_root(f, v.data[i]);
    }
  } else {
    fputs("--- Empty congruence table ---\n", f);
  }
  
  delete_pvector(&v);
}




/****************
 *  IDL SOLVER  *
 ***************/

/*
 * Print idl variable x
 */
void print_idl_var(FILE *f, thvar_t x) {
  if (x >= 0) {
    fprintf(f, "y!%"PRId32, x);
  } else if (x == null_idl_vertex) {
    fputs("null", f);
  } else {
    fprintf(f, "IDLV%"PRId32, x);
  }
}

/*
 * Print atom
 */
void print_idl_atom(FILE *f, idl_atom_t *atom) {
  fputc('[', f);
  print_bvar(f, atom->boolvar);
  fputs(" := (", f);
  print_idl_var(f, atom->source);
  fputs(" - ", f);
  print_idl_var(f, atom->target);
  fprintf(f, " <= %3"PRId32")]", atom->cost);
}


/*
 * Print all atoms in idl solver
 */
void print_idl_atoms(FILE *f, idl_solver_t *idl) {
  uint32_t i, n;

  n = idl->atoms.natoms;
  for (i=0; i<n; i++) {
    print_idl_atom(f, idl->atoms.atoms + i);
    fputc('\n', f);
  }
}


/*
 * Value of var v in the idl solver
 *
 * HACK:
 * - we use distance[0, v] as the value
 * - if the distance is not defined we print ???
 */
void print_idl_var_value(FILE *f, idl_solver_t *idl, thvar_t v) {
  idl_matrix_t *m;
  idl_cell_t *cell;
  int32_t z;

  m = &idl->graph.matrix;
  z = idl->zero_vertex;
  if (z == null_idl_vertex) {
    z = 0;
  }
  
  if (m != NULL && z < m->dim && v < m->dim) {
    cell = m->data + z * m->dim + v;
    if (cell->id >= 0) {
      // ditance [z, x] is defined
      fprintf(f, "%"PRId32, cell->dist);
      return;
    }
  }

  fprintf(f, "???");
}




/****************
 *  RDL SOLVER  *
 ***************/

/*
 * Print rdl variable x
 */
void print_rdl_var(FILE *f, thvar_t x) {
  if (x >= 0) {
    fprintf(f, "x!%"PRId32, x);
  } else if (x == null_idl_vertex) {
    fputs("null", f);
  } else {
    fprintf(f, "RDLV%"PRId32, x);
  }
}

/*
 * Constant used by rdl solver = rational + k * delta
 */
void print_rdl_const(FILE *f, rdl_const_t *c) {
  int32_t d;

  d = c->delta;

  if (q_is_zero(&c->q)) {
    if (d == 0) {
      fputc('0', f);
    } else {
      if (d < 0) {
	fputs("- ", f);
	d = - d;
      }
      if (d == 1) {
	fputs("delta", f);
      } else {
	fprintf(f, "%"PRId32" * delta", d);
      }
    }
  } else {
    q_print(f, &c->q);
    if (d != 0) {
      if (d < 0) {
	fputs(" - ", f);
	d = - d;
      } else {
	fputs(" + ", f);
      }
      if (d == 1) {
	fputs("delta", f);
      } else {
	fprintf(f, "%"PRId32" * delta", d);
      }
    }
  }
}


/*
 * Print atom
 */
void print_rdl_atom(FILE *f, rdl_atom_t *atom) {
  fputc('[', f);
  print_bvar(f, atom->boolvar);
  fputs(" := (", f);
  print_rdl_var(f, atom->source);
  fputs(" - ", f);
  print_rdl_var(f, atom->target);
  fprintf(f, " <= ");
  q_print(f, &atom->cost);
  fprintf(f, ")]");
}


/*
 * Print all atoms in rdl solver
 */
void print_rdl_atoms(FILE *f, rdl_solver_t *rdl) {
  uint32_t i, n;

  n = rdl->atoms.natoms;
  for (i=0; i<n; i++) {
    print_rdl_atom(f, rdl->atoms.atoms + i);
    fputc('\n', f);
  }
}


/*
 * Value of var v in the rdl solver
 *
 * HACK:
 * - we use distance[0, v] as the value
 * - if the distance is not defined we print ???
 */
void print_rdl_var_value(FILE *f, rdl_solver_t *rdl, thvar_t v) {
  rdl_matrix_t *m;
  rdl_cell_t *cell;
  int32_t z;

  m = &rdl->graph.matrix;
  z = rdl->zero_vertex;
  if (z == null_rdl_vertex) z = 0;
  
  if (m != NULL && z < m->dim && v < m->dim) {
    cell = m->data + z * m->dim + v;
    if (cell->id >= 0) {
      // distance [z, x] is defined
      print_rdl_const(f, &cell->dist);
      return;
    }
  }

  fprintf(f, "???");
}




/******************
 *  SUMMARY INFO  *
 *****************/

/*
 * For a core solver
 */
EXPORTED
void print_core_summary(FILE *f, smt_core_t *core) {
  uint32_t eg_atoms, arith_atoms, bv_atoms;
  uint32_t i, n;
  void *atom;
  
  eg_atoms = 0;
  arith_atoms = 0;
  bv_atoms = 0;
  n = core->nvars;
  for (i=0; i<n; i++) {
    atom = bvar_atom(core, i);
    if (atom != NULL) {
      switch (atom_tag(atom)) {
      case EGRAPH_ATM_TAG:
	eg_atoms ++;
	break;
      case ARITH_ATM_TAG:
	arith_atoms ++;
	break;
      case BV_ATM_TAG:
	bv_atoms ++;
	break;
      default:
	break;
      }
    }
  }

  fprintf(f, "SMT Core %p\n", core);
  fprintf(f, "  %"PRIu32" variables\n", core->nvars);
  fprintf(f, "  %"PRIu32" unit clauses\n", core->nb_unit_clauses);
  fprintf(f, "  %"PRIu32" binary clauses\n", core->nb_bin_clauses);
  fprintf(f, "  %"PRIu32" problem clauses\n", get_cv_size(core->problem_clauses));
  fprintf(f, "  %"PRIu32" learned clauses\n", get_cv_size(core->learned_clauses));
  fprintf(f, "  %"PRIu32" atoms:\n", eg_atoms + arith_atoms + bv_atoms);
  fprintf(f, "     %"PRIu32" egraph atoms\n", eg_atoms);
  fprintf(f, "     %"PRIu32" arithmetic atoms\n", arith_atoms);
  fprintf(f, "     %"PRIu32" bitvector atoms\n", bv_atoms);
  fprintf(f, "status = %s\n", status2string[core->status]);
  fprintf(f, "base_level = %"PRIu32"\n", core->base_level);
  fprintf(f, "decision_level = %"PRIu32"\n", core->decision_level);
  print_conflict(f, core);
  fprintf(f, "propagation queue: prop_ptr = %"PRIu32", th_ptr = %"PRIu32", top = %"PRIu32"\n", 
	  core->stack.prop_ptr, core->stack.theory_ptr, core->stack.top);
}


/*
 * For the egraph
 */
EXPORTED
void print_egraph_summary(FILE *f, egraph_t *egraph) {
  fprintf(f, "Egraph %p\n", egraph);
  fprintf(f, "  %"PRIu32" terms\n", egraph->terms.nterms);
  fprintf(f, "  %"PRIu32" classes\n", egraph->classes.nclasses);
  fprintf(f, "  %"PRIu32" congruence roots\n", egraph->ctable.nelems);
  fprintf(f, "base_level = %"PRIu32"\n", egraph->base_level);
  fprintf(f, "decision_level = %"PRIu32"\n", egraph->decision_level);
  fprintf(f, "equality propagation queue: prop_ptr = %"PRIu32", top = %"PRIu32"\n",
	  egraph->stack.prop_ptr, egraph->stack.top);
}






/*
 * For the context
 */
EXPORTED
void print_context_summary(FILE *f, context_t *ctx) {
  printf("Context %p\n", ctx);
  printf("  %"PRIu32" eliminated eqs\n", num_eliminated_eqs(ctx));
  printf("  %"PRIu32" subst candidates\n", num_subst_candidates(ctx));
  printf("  %"PRIu32" substitutions\n", num_substitutions(ctx));
  printf("  %"PRIu32" top equalities\n", num_top_eqs(ctx));
  printf("  %"PRIu32" top atoms\n", num_top_atoms(ctx));
  printf("  %"PRIu32" top formulas\n", num_top_formulas(ctx));
}



/*******************
 * INTERNALIZATION *
 ******************/

// kind of type of term t (using globals)
static inline type_kind_t typekind(context_t *ctx, term_t t) {
  return term_type_kind(ctx->terms, t);
}


// print a code x, tau = corresponding kind of type
static void print_internal_code(FILE *f, icode_t x, type_kind_t tau) {
  if (code_is_valid(x)) {
    if (code_is_eterm(x)) {
      fputs("occ(", f);
      print_occurrence(f, code2occ(x));
      fputc(')', f);
    } else {
      switch (tau) {
      case BOOL_TYPE:
	fputs("lit(", f);
	print_literal(f, code2literal(x));
	fputc(')', f);
	break;
      case INT_TYPE:
	fprintf(f, "arith(y!%"PRId32")", code2arithvar(x));
	break;
      case REAL_TYPE:
	fprintf(f, "arith(x!%"PRId32")", code2arithvar(x));
	break;
      case BITVECTOR_TYPE:
	fprintf(f, "bv(u!%"PRId32")", code2bvvar(x));
	break;
      default:
	fprintf(f, "VAR(%"PRId32")", x);
	break;
      }
    }
  } else if (x == nil) {
    fputs("nil", f);
  } else if (x == mark) {
    fputs("mark", f);
  } else {
    fprintf(f, "CODE%"PRId32, x);
  }
}


void print_internal_code_of_term(FILE *f, context_t *ctx, term_t t) {
  icode_t x;

  x = get_internal_code(ctx, t);
  if (x != nil) {
    fputs("term ", f);
    print_term_name(f, t);
    fputs("\tmapped to ", f);
    print_internal_code(f, x, typekind(ctx, t));
    fputc('\n', f);
  }
}

// more details
void print_internalization(FILE *f, context_t *ctx, term_t t) {
  icode_t x;

  x = get_internal_code(ctx, t);
  fputs("term ", f);
  print_term(f, t);
  fputs(" mapped to ", f);
  print_internal_code(f, x, typekind(ctx, t));
  fputc('\n', f);
  fputs("--> ", f);
  print_term(f, t);
  fputs(" is ", f);
  print_term_id(f, t);
  fputc('\n', f);
  if (code_is_valid(x) && code_is_eterm(x)) {
    fputs("--> ", f);
    print_eterm_def(f, ctx->egraph, code2eterm(x));
  }
  
}

EXPORTED
void print_internalization_table(FILE *f, context_t *ctx) {
  translator_t *trans;
  uint32_t i, n;

  trans = &ctx->trans;
  n = trans->term_map.size;
  for (i=0; i<n; i++) {
    print_internal_code_of_term(f, ctx, i);
  }
  fputc('\n', f);
}


void print_term_vector(FILE *f, context_t *ctx, ivector_t *v) {
  uint32_t i, n;
  term_t t;
  icode_t x;

  n = v->size;
  for (i=0; i<n; i++) {
    t = v->data[i];
    x = get_internal_code(ctx, t);
    fprintf(f, "term[%"PRId32"]: ", t);
    print_term_name(f, t);
    fprintf(f, " --> ");
    print_internal_code(f, x, typekind(ctx, t));
    fprintf(f, "\n  ");
    print_termdef(f, t);
    fprintf(f, "\n");    
  }
  fprintf(f, "\n\n");
  fflush(f);
}




/*
 * Find root of t in partition p
 */
static term_t find_root(partition_t *p, term_t t) {
  term_t *parent;
  term_t y;

  if (t >= p->nelems) return NULL_TERM;
  parent = p->parent;
  y = parent[t];
  if (y == NULL_TERM) return y;
  while (y != t) {
    t = y;
    y = parent[t];
    assert(y != NULL_TERM);
  }
  return y;
}


/*
 * Print the partition mapping
 */
void print_partition(FILE *f, context_t *ctx) {
  partition_t *p;
  uint32_t i, n;
  term_t r;

  p = &ctx->partition;
  n = p->nelems;
  for (i=0; i<n; i++) {
    r = find_root(p, i);
    if (r != NULL_TERM && r != i) {
      fputs("term ", f);
      print_term_id(f, i);
      fputs(", ", f);
      print_term(f, i);
      fputs(" --> ", f);
      print_termdef(f, r);
      fputc('\n', f);
    }
  }
}

/*
 * Get the substitution candidate mapped to t:
 * - t should be an unassigned variable
 * - return NULL_TERM if t is not mapped to anything
 */
static term_t subst_candidate(context_t *ctx, term_t t) {
  int_hmap_pair_t *p;

  p = int_hmap_find(&ctx->pseudo_subst, t);
  if (p == NULL) {
    return NULL_TERM;
  } else {
    return p->val;
  }
}



/*
 * Print the substitutions
 */
void print_substitutions(FILE *f, context_t *ctx) {
  partition_t *p;
  uint32_t i, n;
  term_t r, s;

  p = &ctx->partition;
  n = p->nelems;
  for (i=0; i<n; i++) {
    r = find_root(p, i);
    if (r == i) {
      s = subst_candidate(ctx, r);
      if (s != NULL_TERM) {
	fputs("term ", f);
	print_term_id(f, r);
	fputs(", ", f);
	print_term(f, r);
	fputs(" --> ", f);
	print_termdef(f, s);
	fputc('\n', f);	
      }
    }
  }
}



/******************************************
 *  ARITHMETIC VARIABLES AND DEFINITIONS  *
 *****************************************/

/*
 * We can't use print_polynomial, print_varprod, etc. from term_printer
 * because the solver variables are not maintained in the global arith_manager
 */
static void print_avar(FILE *f, arith_vartable_t *table, thvar_t v) {
  if (arith_var_is_int(table, v)) {
    fprintf(f, "i!%"PRId32, v);
  } else {
    fprintf(f, "z!%"PRId32, v);
  }
}

static void print_avar_power(FILE *f, arith_vartable_t *table, varexp_t *p) {
  print_avar(f, table, p->var);
  if (p->exp > 1) {
    fprintf(f, "^%"PRId32, p->exp);
  }
}

static void print_avar_product(FILE *f, arith_vartable_t *table, varprod_t *p) {
  int32_t i, n;

  n = p->len;
  if (n == 0) {
    fprintf(f, "1");
  } else {
    i = 0;
    for (;;) {
      print_avar_power(f, table, p->prod + i);
      i ++;
      if (i == n) break;
      fputs(" * ", f);
    }
  }
}

static void print_avar_monomial(FILE *f, arith_vartable_t *table, thvar_t v, rational_t *coeff, bool first) {
  bool negative;
  bool abs_one;

  negative = q_is_neg(coeff);

  if (negative) {
    if (first) {
      fputs("- ", f);
    } else {
      fputs(" - ", f);
    }
    abs_one = q_is_minus_one(coeff);
  } else {
    if (! first) {
      fputs(" + ", f);
    }
    abs_one = q_is_one(coeff);
  }

  if (v == const_idx) {
    q_print_abs(f, coeff);
  } else {
    if (! abs_one) {
      q_print_abs(f, coeff);
      fputs(" * ", f);
    }
    print_avar(f, table, v);
  }
}

static void print_avar_poly(FILE *f, arith_vartable_t *table, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    for (i=0; i<n; i++) {
      print_avar_monomial(f, table, p->mono[i].var, &p->mono[i].coeff, i == 0);
    }
  }
}


void print_arith_vartable(FILE *f, arith_vartable_t *table) {
  uint32_t i, n;

  n = table->nvars;
  for (i=0; i<n; i++) {
    print_avar(f, table, i);
    if (arith_var_def_is_poly(table, i)) {
      fputs(" := ", f);
      print_avar_poly(f, table, arith_var_poly_def(table, i));
    } else if (arith_var_def_is_product(table, i)) {
      fputs(" := ", f);
      print_avar_product(f, table, arith_var_product_def(table, i));
    }
    if (arith_var_has_eterm(table, i)) {
      fputs(" --> ", f);
      print_eterm_id(f, arith_var_eterm(table, i));
    }
    fputc('\n', f);
  }  
}


/*
 * ARITHMETIC ATOMS
 */
static void print_arith_atom_op(FILE *f, arithatm_tag_t tag) {
  switch (tag) {
  case GE_ATM:
    fputs(" >= ", f);
    break;
  case LE_ATM:
    fputs(" <= ", f);
    break;
  case EQ_ATM:
    fputs(" == ", f);
    break;
  default:
    fputs(" <badop> ", f);
    break;
  }
}

static void print_arith_atom(FILE *f, arith_vartable_t *table, arith_atom_t *atom) {
  print_avar(f, table, var_of_atom(atom));
  print_arith_atom_op(f, tag_of_atom(atom));
  q_print(f, &atom->bound);
}

void print_arith_atomtable(FILE *f, arith_vartable_t *vtbl, arith_atomtable_t *atbl) {
  uint32_t i, n;
  arith_atom_t *a;

  n = atbl->natoms;
  a = atbl->atoms;
  for (i=0; i<n; i++) {
    print_bvar(f, a[i].boolvar);
    fputs(" := ", f);
    print_arith_atom(f, vtbl, a + i);
    fputs("\t\t", f);
    print_bval(f, bvar_value(atbl->core, a[i].boolvar));
    fputc('\n', f);    
  }
}


/*
 * MATRIX
 */

// row is printed as a_1 x_1 + .... + a_n x_n == 0
static void print_row(FILE *f, arith_vartable_t *vtbl, row_t *row) {
  uint32_t i, n;
  thvar_t x;
  bool first;

  first = true;
  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      print_avar_monomial(f, vtbl, x, &row->data[i].coeff, first);
      first = false;
    }
  }
  if (first) {
    // nothing printed so the row is empty
    fputc('0', f); 
  }
  fputs(" == 0", f);
}


void print_matrix(FILE *f, arith_vartable_t *vtbl, matrix_t *matrix) {
  uint32_t i, n;

  n = matrix->nrows;
  for (i=0; i<n; i++) {
    fprintf(f, "  row[%"PRIu32"]:", i);
    print_space(f, i);
    print_row(f, vtbl, matrix->row[i]);
    fputc('\n', f);
  }
  fputc('\n', f);
}


void print_elim_matrix(FILE *f, arith_vartable_t *vtbl, elim_matrix_t *elim) {
  uint32_t i, n;

  n = elim->nrows;
  for (i=0; i<n; i++) {
    fprintf(f, "  elim[%"PRIu32"]:", i);
    print_space(f, i);
    print_avar_poly(f, vtbl, elim->row[i]);
    fputs("  (", f);
    print_avar(f, vtbl, elim->base_var[i]);
    fputs(")\n", f);
  }
  fputc('\n', f);
}


void print_fixed_var_vector(FILE *f, arith_vartable_t *vtbl, fvar_vector_t *fvars) {
  uint32_t i, n;

  n = fvars->nvars;
  for (i=0; i<n; i++) {
    fprintf(f, "  fixed[%"PRIu32"]:", i);
    print_space(f, i);
    print_avar(f, vtbl, fvars->fvar[i].var);
    fputs(" == ", f);
    q_print(f, &fvars->fvar[i].value);
    fputc('\n', f);
  }
  fputc('\n', f);
}



/*
 * Bounds on variable x
 */
static void print_avar_bounds(FILE *f, simplex_solver_t *solver, thvar_t x) {
  int32_t lb, ub;

  lb = arith_var_lower_index(&solver->vtbl, x);
  ub = arith_var_upper_index(&solver->vtbl, x);
  if (lb >= 0 || ub >= 0) {
    fputs("  ", f);
    if (lb >= 0) {
      xq_print(f, solver->bstack.bound + lb);
      fputs(" <= ", f);
    }
    print_avar(f, &solver->vtbl, x);
    if (ub >= 0) {
      fputs(" <= ", f);
      xq_print(f, solver->bstack.bound + ub);
    }
    fputc('\n', f);
  }
}


/*
 * Value of variable x
 */
static void print_avar_value(FILE *f, arith_vartable_t *vtbl, thvar_t x) {
  fputs("  val[", f);  
  print_avar(f, vtbl, x);
  fputs("] = ", f);
  xq_print(f, arith_var_value(vtbl, x));
}


/*
 * Bounds + value of x + row where x is basic
 */
static void print_avar_full(FILE *f, simplex_solver_t *solver, thvar_t x) {
  int32_t lb, ub, r;

  lb = arith_var_lower_index(&solver->vtbl, x);
  ub = arith_var_upper_index(&solver->vtbl, x);
  r = matrix_basic_row(&solver->matrix, x);

  fputs("  ", f);
  print_avar(f, &solver->vtbl, x);
  fputs(" = ", f);
  xq_print(f, arith_var_value(&solver->vtbl, x));
  fputc('\t', f);

  if (lb >= 0 || ub >= 0) {
    if (lb >= 0) {
      xq_print(f, solver->bstack.bound + lb);
      fputs(" <= ", f);
    }
    print_avar(f, &solver->vtbl, x);
    if (ub >= 0) {
      fputs(" <= ", f);
      xq_print(f, solver->bstack.bound + ub);
    }
  } else {
    fputs("no bounds", f); 
  }

  if (r >= 0) {
    fprintf(f, "\t\tbasic in row[%"PRIu32"]\n", r);
  } else {
    fprintf(f, "\t\tnon basic\n");
  }
}


/*
 * Simplex components
 */
void print_simplex_vars(FILE *f, simplex_solver_t *solver) {
  print_arith_vartable(f, &solver->vtbl);
}

void print_simplex_atoms(FILE *f, simplex_solver_t *solver) {
  print_arith_atomtable(f, &solver->vtbl, &solver->atbl);
}

void print_simplex_atom(FILE *f, simplex_solver_t *solver, int32_t id) {
  print_arith_atom(f, &solver->vtbl, arith_atom(&solver->atbl, id));
}

void print_simplex_row(FILE *f, simplex_solver_t *solver, row_t *row) {
  print_row(f, &solver->vtbl, row);
}

void print_simplex_matrix(FILE *f, simplex_solver_t *solver) {
  print_matrix(f, &solver->vtbl, &solver->matrix);
}

void print_simplex_basic_vars(FILE *f, simplex_solver_t *solver) {
  matrix_t *matrix;
  uint32_t i, n;
  int32_t x;

  matrix = &solver->matrix;
  n = matrix->nrows;
  for (i=0; i<n; i++) {
    fprintf(f, "  row[%"PRIu32"]: ", i);
    x = matrix->base_var[i];
    if (x >=0 ) {
      fputs("basic var = ", f);
      print_avar(f, &solver->vtbl, x);
      fputc('\n', f);
    } else {
      fputs("no basic var\n", f);
    }
  }
  fputc('\n', f);
}


void print_simplex_bounds(FILE *f, simplex_solver_t *solver) {
  uint32_t i, n;

  n = num_arith_vars(&solver->vtbl);
  for (i=0; i<n; i++) {
    print_avar_bounds(f, solver, i);
  }
}

void print_simplex_assignment(FILE *f, simplex_solver_t *solver) {
  uint32_t i, n;

  n = num_arith_vars(&solver->vtbl);
  for (i=0; i<n; i++) {
    print_avar_value(f, &solver->vtbl, i);
    fputc('\n', f);
  }
}


void print_simplex_allvars(FILE *f, simplex_solver_t *solver) {
  uint32_t i, n;

  n = num_arith_vars(&solver->vtbl);
  for (i=0; i<n; i++) {
    print_avar_full(f, solver, i);
  }
  fputc('\n', f);
}


void print_simplex_vardef(FILE *f, simplex_solver_t *solver, thvar_t v) {
  arith_vartable_t *table;

  table = &solver->vtbl;
  print_avar(f, table, v);
  if (arith_var_def_is_poly(table, v)) {
    fputs(" := ", f);
    print_avar_poly(f, table, arith_var_poly_def(table, v));
  } else if (arith_var_def_is_product(table, v)) {
    fputs(" := ", f);
    print_avar_product(f, table, arith_var_product_def(table, v));
  } 
  fputc('\n', f);
}

void print_simplex_var(FILE *f, simplex_solver_t *solver, thvar_t v) {
  print_avar(f, &solver->vtbl, v);
}

void print_simplex_var_value(FILE *f, simplex_solver_t *solver, thvar_t v) {
  xq_print(f, arith_var_value(&solver->vtbl, v));
}

void print_simplex_atomdef(FILE *f, simplex_solver_t *solver, bvar_t v) {
  void *atm;
  arith_atom_t *a;
  int32_t i;

  atm = get_bvar_atom(solver->core, v);
  i = arithatom_tagged_ptr2idx(atm);
  a = arith_atom(&solver->atbl, i);
  assert(a->boolvar == v);
  print_bvar(f, v);
  fputs(" := ", f);
  print_arith_atom(f, &solver->vtbl, a);
  fputc('\n', f);
}


void print_simplex_atom_of_literal(FILE *f, simplex_solver_t *solver, literal_t l) {
  void *atm;
  arith_atom_t *a;
  bvar_t v;
  int32_t i;

  v = var_of(l);
  assert(bvar_has_atom(solver->core, v));
  atm = bvar_atom(solver->core, v);
  assert(atom_tag(atm) == ARITH_ATM_TAG);
  i = arithatom_tagged_ptr2idx(atm);
  a = arith_atom(&solver->atbl, i);
  assert(a->boolvar == v);

  if (is_neg(l)) {
    fputs("(not ", f);
  }
  print_arith_atom(f, &solver->vtbl, a);
  if (is_neg(l)) {
    fputc(')', f);
  }
}


void print_simplex_buffer(FILE *f, simplex_solver_t *solver) {
  poly_buffer_t *b;  
  uint32_t i, n;

  b = &solver->buffer;
  n = b->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    for (i=0; i<n; i++) {
      print_avar_monomial(f, &solver->vtbl, b->mono[i].var, &b->mono[i].coeff, i == 0);
    }
  }
}


void print_simplex_bound(FILE *f, simplex_solver_t *solver, uint32_t i) {
  fprintf(f, "bound[%"PRIu32"]: ", i);
  if (i < solver->bstack.top) {
    print_avar(f, &solver->vtbl, solver->bstack.var[i]);
    if (arith_tag_get_type(solver->bstack.tag[i]) == ATYPE_UB) {
      fputs(" <= ", f);
    } else {
      fputs(" >= ", f);
    }
    xq_print(f, solver->bstack.bound + i);    
  } else {
    fprintf(f, "<INVALID BOUND INDEX>");
  }
}



/*
 * Print row in a simplified form: replace fixed variables by their value
 */
void print_simplex_reduced_row(FILE *f, simplex_solver_t *solver, row_t *row) {
  arith_vartable_t *vtbl;
  arith_bstack_t *bstack;
  rational_t q;
  uint32_t i, n;
  thvar_t x;
  bool first;
  int32_t l, u;

  vtbl = &solver->vtbl;
  bstack = &solver->bstack;

  // compute the constant
  q_init(&q);
  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      l = arith_var_lower_index(&solver->vtbl, x);
      u = arith_var_upper_index(&solver->vtbl, x);
      if (l >= 0 && u >= 0 && xq_eq(bstack->bound + l, bstack->bound + u)) {
	// x is a a fixed variable
	assert(xq_eq(bstack->bound + l, arith_var_value(vtbl, x)));
	assert(xq_is_rational(arith_var_value(vtbl, x)));
	q_addmul(&q, &row->data[i].coeff, &arith_var_value(vtbl, x)->main);
      }
    }
  }

  // print the non-constant monomials and q 
  first = true;
  if (q_is_nonzero(&q)) {
    print_avar_monomial(f, vtbl, const_idx, &q, first);
    first = false;
  }

  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      l = arith_var_lower_index(&solver->vtbl, x);
      u = arith_var_upper_index(&solver->vtbl, x);
      if (l < 0 || u < 0 || xq_neq(bstack->bound + l, bstack->bound + u)) {
	// x is not a fixed variable
	print_avar_monomial(f, vtbl, x, &row->data[i].coeff, first);
	first = false;
      }
    }
  }

  if (first) {
    // nothing printed so the row is empty
    fputc('0', f); 
  }
  fputs(" == 0", f);

  q_clear(&q);
}



/*
 * Variant of print_simplex_bounds
 */
void print_simplex_bounds2(FILE *f, simplex_solver_t *solver) {
  uint32_t i, n;
  int32_t lb, ub;

  n = num_arith_vars(&solver->vtbl);
  for (i=0; i<n; i++) {
    lb = arith_var_lower_index(&solver->vtbl, i);
    ub = arith_var_upper_index(&solver->vtbl, i);
    if (lb >= 0 && ub >= 0) {
      if (xq_neq(solver->bstack.bound + lb, solver->bstack.bound + ub)) {
	fputs("  ", f);
	xq_print(f, solver->bstack.bound + lb);
	fprintf(f, " <= x_%"PRIu32" <= ", i);
	xq_print(f, solver->bstack.bound + ub);
	fputc('\n', f);
      }
    } else if (lb >= 0) {
      fputs("  ", f);
      xq_print(f, solver->bstack.bound + lb);
      fprintf(f, " <= x_%"PRIu32"\n", i);
    } else if (ub >= 0) {
      fprintf(f, "  x_%"PRIu32" <= ", i);
      xq_print(f, solver->bstack.bound + ub);
      fputc('\n', f);
    }
  }
}




/*
 * ARRAY/FUNCTION SOLVER
 */

/*
 * Print edge i
 */
void print_fsolver_edge(FILE *f, fun_solver_t *solver, uint32_t edge_id) {
  fun_edgetable_t *etbl;
  fun_edge_t *e;
  uint32_t i, n;

  etbl = &solver->etbl;
  assert(0 <= edge_id && edge_id < etbl->nedges);
  e = etbl->data[edge_id];

  fprintf(f, "edge[%"PRIu32"] : f!%"PRIu32" ---> f!%"PRIu32" [", edge_id, e->source, e->target);
  n = solver->vtbl.arity[e->source];
  assert(solver->vtbl.arity[e->target] == n);
  for (i=0; i<n; i++) {
    if (i>0) {
      fputc(' ', f);
    }
    print_occurrence(f, e->index[i]);
  }
  fprintf(f, "]");
}


/*
 * Print the egdes
 */
void print_fsolver_edges(FILE *f, fun_solver_t *solver) {
  uint32_t i, n;

  n = solver->etbl.nedges;
  for (i=0; i<n; i++) {
    print_fsolver_edge(f, solver, i);
    fputc('\n', f);
  }
  fflush(f);
}


/*
 * Print the variables
 */
void print_fsolver_vars(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    fprintf(f, "var f!%"PRId32": eterm = ", i);
    print_eterm_id(f, vtbl->eterm[i]);
    if (tst_bit(vtbl->fdom, i)) {
      fprintf(f, ", finite domain");
    }
    fprintf(f, ", type: ");
    print_typedef(f, vtbl->type[i]);
    fprintf(f, "\n");
  }
  fflush(f);
}


/*
 * Print the root variables
 */
void print_fsolver_roots(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    fprintf(f, "root[f!%"PRIu32"] = f!%"PRIu32", eterm[f!%"PRIu32"] = ", i, vtbl->root[i], i);
    print_eterm_id(f, vtbl->eterm[i]);
    fputc('\n', f);
  }
  fflush(f);
}


/*
 * Print the equivalence classes
 */
void print_fsolver_classes(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  uint32_t i, n;
  thvar_t x;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      // i is a root:
      fprintf(f, "class of f!%"PRIu32" = {", i);
      x = i;
      do {
	fprintf(f, " f!%"PRId32, x);
	x = vtbl->next[x];
      } while (x != null_thvar);
      fprintf(f, " }\n");
    }
  }
}


/*
 * Print the application vectors
 */
void print_fsolver_apps(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  composite_t **p;
  uint32_t i, n, j, m;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      p = (composite_t **) vtbl->app[i];
      if (p != NULL) {
	fprintf(f, "--- Apps for f!%"PRIu32" ---\n", i);
	m = pv_size((void **) p);
	for (j=0; j<m; j++) {
	  print_composite(f, p[j]);
	  fputs("  == ", f);
	  print_label(f, egraph_term_label(solver->egraph, p[j]->id));
	  fputc('\n', f);
	}
      } else {
	fprintf(f, "--- No apps for f!%"PRIu32" ---\n", i);
      }
    }
  }
  fflush(f);
}



/*
 * Print (f i_1 ... i_n) as a map element
 */
static void print_map(FILE *f, egraph_t *egraph, composite_t *c) {
  uint32_t i, n;

  assert(composite_kind(c) == COMPOSITE_APPLY);

  n = composite_arity(c);
  fputc('[', f);
  for (i=1; i<n; i++) {
    print_label(f, egraph_label(egraph, composite_child(c, i)));
    fputc(' ', f);
  }
  fputs("|-> ", f);
  print_label(f, egraph_term_label(egraph, c->id));
  fputs("]\n", f);
}


/*
 * Print the application vectors + base labels
 * - formatted as a mapping form egraph labels to egraph labels
 */
void print_fsolver_maps(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  egraph_t *egraph;
  composite_t **p;
  uint32_t i, n, j, m;

  egraph = solver->egraph;
  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      fprintf(f, "--- Map for f!%"PRIu32" ---\n", i);
      fprintf(f, "base = %"PRId32"\n", vtbl->base[i]);
      p = (composite_t **) vtbl->app[i];
      if (p != NULL) {
	m = pv_size((void **) p);
	for (j=0; j<m; j++) {
	  print_map(f, egraph, p[j]);	  
	}
      }
    }
  }
  
}


/*
 * Print the base values for every root variable
 */
void print_fsolver_base_values(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  uint32_t i, n;
  int32_t c, k;

  if (solver->base_value == NULL) {
    fputs("no base values\n", f);
    return;
  }

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      c = vtbl->base[i];
      k = solver->base_value[c];
      fprintf(f, "base value for f!%"PRIu32": ", i);
      if (k < 0) {
	fprintf(f, "fresh(%"PRId32")\n", - (k + 1));
      } else if (k == INT32_MAX) {
	fputs("unknown\n", f);
      } else {
	print_label(f, k);
	fputc('\n', f);
      }
    }
  }
}



/*
 * Print particle x as an index
 */
static void print_particle_index(FILE *f, egraph_t *egraph, particle_t x) {
  pstore_t *store;
  particle_tuple_t *tup;
  uint32_t i, n;

  store = egraph->mdl.pstore;
  switch (particle_kind(store, x)) {
  case LABEL_PARTICLE:
    print_label(f, particle_label(store, x));
    break;
  case FRESH_PARTICLE:
    fprintf(f, "fresh!%"PRId32, x);
    break;
  case TUPLE_PARTICLE:
    tup = tuple_particle_desc(store, x);
    n = tup->nelems;
    for (i=0; i<n; i++) {
      if (i>0) fputc(' ', f);
      print_particle_index(f, egraph, tup->elem[i]);
    }
    break;
  }
}

/*
 * Print particle x as a value
 */
static void print_particle_value(FILE *f, egraph_t *egraph, particle_t x) {
  pstore_t *store;
  particle_tuple_t *tup;
  uint32_t i, n;

  store = egraph->mdl.pstore;
  switch (particle_kind(store, x)) {
  case LABEL_PARTICLE:
    print_label(f, particle_label(store, x));
    break;
  case FRESH_PARTICLE:
    fprintf(f, "fresh!%"PRId32, x);
    break;
  case TUPLE_PARTICLE:
    tup = tuple_particle_desc(store, x);
    n = tup->nelems;
    fputs("(tuple", f);
    for (i=0; i<n; i++) {
      fputc(' ', f);
      print_particle_value(f, egraph, tup->elem[i]);
    }
    fputc(')', f);
    break;
  }
}

/*
 * Print the mapping [idx -> value]
 */
static void print_map_elem(FILE *f, egraph_t *egraph, particle_t idx, particle_t val) {
  fputc('[', f);
  print_particle_index(f, egraph, idx);
  fputs(" -> ", f);
  print_particle_value(f, egraph, val);
  fputs("]\n", f);
}


/*
 * Print the values
 */
void print_fsolver_values(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  egraph_t *egraph;
  map_t *map;
  uint32_t i, n, j;

  egraph = solver->egraph;
  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      fprintf(f, "--- Value for f!%"PRIu32" ---\n", i);
      map = solver->value[i];
      if (map != NULL) {
	for (j=0; j<map->nelems; j++) {
	  print_map_elem(f, egraph, map->data[j].index, map->data[j].value);	  
	}
	if (map->def != null_particle) {
	  fputs("[else -> ", f);
	  print_particle_value(f, egraph, map->def);
	  fputs("]\n", f);
	}
      }
    }
  }
  
}


/*
 * Print the asserted disequalities
 */
void print_fsolver_diseqs(FILE *f, fun_solver_t *solver) {
  diseq_stack_t *dstack;
  uint32_t i, n;

  dstack = &solver->dstack;
  n = dstack->top;
  for (i=0; i<n; i++) {
    fprintf(f, "diseq[%"PRIu32"]: f!%"PRIu32" != f%"PRIu32"\n", i, dstack->data[i].left, dstack->data[i].right);    
  }
  
}



/*
 * BIT SOLVER
 */
void print_bit_solver_unit_clauses(FILE *f, bit_solver_t *solver) {
  prop_stack_t *stack;
  uint32_t i, n;

  n = solver->nb_unit_clauses;
  stack = &solver->stack;
  for (i=0; i<n; i++) {
    print_unit_clause(f, stack->lit[i]);
    fputc('\n', f);
  }
}

void print_bit_solver_binary_clauses(FILE *f, bit_solver_t *solver) {
  int32_t n;
  literal_t l1, l2;
  literal_t *bin;

  n = solver->nlits;  
  for (l1=0; l1<n; l1++) {
    bin = solver->bin[l1];
    if (bin != NULL) {
      for (;;) {
	l2 = *bin++;
	if (l2 < 0) break;
	if (l1 <= l2) {
	  print_binary_clause(f, l1, l2);
	  fputc('\n', f);
	}
      }
    }
  }
}

void print_bit_solver_problem_clauses(FILE *f, bit_solver_t *solver) {
  print_clause_vector(f, solver->problem_clauses);
}

void print_bit_solver_learned_clauses(FILE *f, bit_solver_t *solver) {
  print_clause_vector(f, solver->learned_clauses);
}

void print_bit_solver_clauses(FILE *f, bit_solver_t *solver) {
  print_bit_solver_unit_clauses(f, solver);
  print_bit_solver_binary_clauses(f, solver);
  print_bit_solver_problem_clauses(f, solver);
  fputc('\n', f);
}

void print_bit_solver_all_clauses(FILE *f, bit_solver_t *solver) {
  print_bit_solver_binary_clauses(f, solver);
  fputc('\n', f);
  print_bit_solver_problem_clauses(f, solver);  
  fputc('\n', f);
  print_bit_solver_learned_clauses(f, solver);
  fputc('\n', f);
}


void print_bit_solver_assignment(FILE *f, bit_solver_t *solver) {
  prop_stack_t *stack;
  uint32_t i, n;
  literal_t l;

  stack = &solver->stack;
  n = stack->top;
  for (i=0; i<n; i++) {
    l = stack->lit[i];
    fputc(' ', f);
    if (is_pos(l)) fputc(' ', f);
    print_literal(f, l);
    fprintf(f, " level = %"PRIu32"\n", solver->level[var_of(l)]);
  }
}


void print_bit_solver_assumptions(FILE *f, bit_solver_t *solver) {
  ivector_t *v;
  uint32_t i, n;
  literal_t l;

  v = &solver->assumptions;
  n = v->size;
  for (i=0; i<n; i++) {
    l = v->data[i];
    fputc(' ', f);
    if (is_pos(l)) fputc(' ', f);
    print_literal(f, l);
    fputc('\n', f);
  }
}



/*
 * BIT-VECTOR SOLVER
 */

/*
 * Print variable x
 */
void print_bvsolver_var(FILE *f, thvar_t x) {
  fprintf(f, "u!%"PRId32, x);
}

void print_bvsolver_bit(FILE *f, bit_t x) {
  if (bit_is_neg(x)) {
    fprintf(f, "~u!%"PRId32, var_of_bit(x));
  } else {
    fprintf(f, "u!%"PRId32, var_of_bit(x));
  }
}

void print_bvsolver_vardef(FILE *f, bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  uint32_t aux[2];
  uint32_t i, nbits;

  vtbl = &solver->vtbl;
  assert(0 <= x && x < vtbl->nvars);
  nbits = vtbl->bit_size[x];
  print_bvsolver_var(f, x);
  fprintf(f, ":bv[%"PRIu32"] = ", nbits);
  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_VAR:
    fputs("var", f);
    break;
  case BVTAG_SMALL_CONST:
    bvconst_set64(aux, 2, vtbl->def[x].ival);
    bvconst_print(f, aux, nbits);
    break;
  case BVTAG_BIG_CONST:
    bvconst_print(f, vtbl->def[x].pval, nbits);
    break;
  case BVTAG_TRUE:
    fputs("tt", f);
    break;
  case BVTAG_SELECT:
    fprintf(f, "u!%"PRId32"[%"PRId32"]", vtbl->def[x].sel.var, vtbl->def[x].sel.idx);
    break;
  case BVTAG_XOR:
    fputs("(xor ", f);
    print_bvsolver_bit(f, vtbl->def[x].bop[0]);
    fputc(' ', f);
    print_bvsolver_bit(f, vtbl->def[x].bop[1]);
    fputc(')', f);
    break;
  case BVTAG_OR:
    fputs("(or ", f);
    print_bvsolver_bit(f, vtbl->def[x].bop[0]);
    fputc(' ', f);
    print_bvsolver_bit(f, vtbl->def[x].bop[1]);
    fputc(')', f);
    break;
  case BVTAG_BIT:
    fputs("(bit ", f);
    print_bvsolver_bit(f, vtbl->def[x].bval);
    fputc(')', f);
    break;
  case BVTAG_BIT_ARRAY:
    fputs("(bits", f);
    for (i=0; i<nbits; i++) {
      fputc(' ', f);
      print_bvsolver_bit(f, vtbl->def[x].bit[i]);
    }
    fputc(')', f);
    break;
  case BVTAG_ADD:
    fprintf(f, "(add u!%"PRId32" u!%"PRId32")", vtbl->def[x].op[0], vtbl->def[x].op[1]);
    break;
  case BVTAG_SUB:
    fprintf(f, "(sub u!%"PRId32" u!%"PRId32")", vtbl->def[x].op[0], vtbl->def[x].op[1]);
    break;
  case BVTAG_NEG:
    fprintf(f, "(neg u!%"PRId32")", vtbl->def[x].op[0]);
    break;
  case BVTAG_MUL:
    fprintf(f, "(mul u!%"PRId32" u!%"PRId32")", vtbl->def[x].op[0], vtbl->def[x].op[1]);
    break;
  case BVTAG_UDIV:
    fprintf(f, "(udiv u!%"PRId32" u!%"PRId32")", vtbl->def[x].op[0], vtbl->def[x].op[1]);
    break;
  case BVTAG_UREM:
    fprintf(f, "(urem u!%"PRId32" u!%"PRId32")", vtbl->def[x].op[0], vtbl->def[x].op[1]);
    break;
  case BVTAG_SDIV:
    fprintf(f, "(sdiv u!%"PRId32" u!%"PRId32")", vtbl->def[x].op[0], vtbl->def[x].op[1]);
    break;
  case BVTAG_SREM:
    fprintf(f, "(srem u!%"PRId32" u!%"PRId32")", vtbl->def[x].op[0], vtbl->def[x].op[1]);
    break;
  case BVTAG_SMOD:
    fprintf(f, "(smod u!%"PRId32" u!%"PRId32")", vtbl->def[x].op[0], vtbl->def[x].op[1]);
    break;
  case BVTAG_SHL:
    fprintf(f, "(shl u!%"PRId32" u!%"PRId32")", vtbl->def[x].op[0], vtbl->def[x].op[1]);
    break;
  case BVTAG_LSHR:
    fprintf(f, "(lshr u!%"PRId32" u!%"PRId32")", vtbl->def[x].op[0], vtbl->def[x].op[1]);
    break;
  case BVTAG_ASHR:
    fprintf(f, "(ashr u!%"PRId32" u!%"PRId32")", vtbl->def[x].op[0], vtbl->def[x].op[1]);
    break;
  case BVTAG_ITE:
    fputs("(ite ", f);
    print_literal(f, vtbl->def[x].ite->cond);
    fprintf(f, " u!%"PRId32" u!%"PRId32")", vtbl->def[x].ite->left, vtbl->def[x].ite->right);
    break;
  default:
    fputs("ERROR", f);
    break;
  }
  fputc('\n', f);
}


static void print_pseudo_literal(FILE *f, literal_t l) {
  if (l == null_literal) {
    fputs("nil", f);
  } else if (l == true_literal) {
    fputs("tt", f);
  } else if (l == false_literal) {
    fputs("ff", f);
  } else {
    if (is_neg(l)) fputc('~', f);
    fprintf(f, "s!%"PRId32, var_of(l));
  }
}

static void print_pseudo_litarray(FILE *f, literal_t *a, uint32_t n) {
  uint32_t i;

  if (a == NULL) {
    fputs("nil", f);
  } else {
    fputc('[', f);
    if (n > 0) {
      print_pseudo_literal(f, a[0]);
      for (i=1; i<n; i++) {
	fputc(' ', f);
	print_pseudo_literal(f, a[i]);
      }
    }
    fputc(']', f);
  }
}


static void print_pseudo_literal_root(FILE *f, remap_table_t *table, literal_t l) {
  if (l != null_literal) {
    l = remap_table_find_root(table, l);
  }
  print_pseudo_literal(f, l);
}


static void print_pseudo_litarray_root(FILE *f, remap_table_t *table, literal_t *a, uint32_t n) {
  uint32_t i;

  if (a == NULL) {
    fputs("nil", f);
  } else {
    fputc('[', f);
    if (n > 0) {
      print_pseudo_literal_root(f, table, a[0]);
      for (i=1; i<n; i++) {
	fputc(' ', f);
	print_pseudo_literal_root(f, table, a[i]);
      }
    }
    fputc(']', f);
  }
}

static void print_pseudo_literal_bit(FILE *f, remap_table_t *table, literal_t l) {
  if (l != null_literal) {
    l = remap_table_find(table, l);
  }
  print_literal(f, l);
}

static void print_pseudo_litarray_bits(FILE *f, remap_table_t *table, literal_t *a, uint32_t n) {
  uint32_t i;

  if (a == NULL) {
    fputs("nil", f);
  } else {
    fputc('[', f);
    if (n > 0) {
      print_pseudo_literal_bit(f, table, a[0]);
      for (i=1; i<n; i++) {
	fputc(' ', f);
	print_pseudo_literal_bit(f, table, a[i]);
      }
    }
    fputc(']', f);
  }
}


// print the value of pseudo literal s in the current boolean assignment
static void print_pseudo_literal_value(FILE *f, bv_solver_t *solver, literal_t s) {
  remap_table_t *rmap;
  smt_core_t *core;
  literal_t l;
  char val;

  l = null_literal;
  val = 'x';
  if (s != null_literal) {
    rmap = solver->remap;
    if (rmap != NULL) {
      l = remap_table_find(rmap, s);
    }
  }
  if (l != null_literal) {
    core = solver->core;
    switch (literal_value(core, l)) {
    case VAL_FALSE:
      val = '0';
      break;

    case VAL_TRUE:
      val = '1';
      break;

    case VAL_UNDEF:
      break;
    }
  }
  fputc(val, f);
}


// value of x in the current boolean assignment
void print_bvsolver_var_value(FILE *f, bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  literal_t *a;
  uint32_t i, nbits;

  vtbl = &solver->vtbl;

  assert(0 <= x && x < vtbl->nvars);

  nbits = vtbl->bit_size[x];
  if (nbits == 0) {
    print_pseudo_literal_value(f, solver, vtbl->map[x].lit);
  } else {
    fputs("0b", f);
    if (nbits == 1) { 
      print_pseudo_literal_value(f, solver, vtbl->map[x].lit);
    } else {
      a = vtbl->map[x].array;
      if (a == NULL) {
	for (i=0; i<nbits; i++) {
	  fputc('x', f);
	}
      } else {
	i = nbits;
	do {
	  i --;
	  print_pseudo_literal_value(f, solver, a[i]);
	} while (i > 0);
      }
    }
  }
}


void print_bvsolver_varmap(FILE *f, bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  literal_t *a;
  uint32_t nbits;

  vtbl = &solver->vtbl;
  assert(0 <= x && x < vtbl->nvars);

  nbits = vtbl->bit_size[x];
  print_bvsolver_var(f, x);
  fputs(" --> ", f);
  if (nbits == 0) {
    print_pseudo_literal(f, vtbl->map[x].lit);
  } else {
    if (nbits == 1) {
      a = NULL;
      if (vtbl->map[x].lit != null_literal) {
	a = &vtbl->map[x].lit;
      }
    } else {
      a = vtbl->map[x].array;
    }      
    print_pseudo_litarray(f, a, nbits);
  }
  fputc('\n', f);
}


void print_bvsolver_varbitmap(FILE *f, bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  literal_t *a;
  uint32_t nbits;

  rmap = solver->remap;
  vtbl = &solver->vtbl;
  assert(0 <= x && x < vtbl->nvars && rmap != NULL);

  nbits = vtbl->bit_size[x];
  print_bvsolver_var(f, x);
  if (! bvvar_is_marked(vtbl, x)) {
    fputs(" .... ", f);
  } else {
    fputs(" --> ", f);
  }
  if (nbits == 0) {
    print_pseudo_literal_bit(f, rmap, vtbl->map[x].lit);
  } else {
    if (nbits == 1) {
      a = NULL;
      if (vtbl->map[x].lit != null_literal) {
	a = &vtbl->map[x].lit;
      }
    } else {
      a = vtbl->map[x].array;
    }      
    print_pseudo_litarray_bits(f, rmap, a, nbits);
  }
  fputc('\n', f);
}


void print_bvsolver_root_varmap(FILE *f, bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  literal_t *a;
  uint32_t nbits;

  rmap = solver->remap;
  vtbl = &solver->vtbl;
  assert(0 <= x && x < vtbl->nvars && rmap != NULL);

  nbits = vtbl->bit_size[x];
  print_bvsolver_var(f, x);
  fputs(" --> ", f);
  if (nbits == 0) {
    print_pseudo_literal_root(f, rmap, vtbl->map[x].lit);
  } else {
    if (nbits == 1) {
      a = NULL;
      if (vtbl->map[x].lit != null_literal) {
	a = &vtbl->map[x].lit;
      }
    } else {
      a = vtbl->map[x].array;
    }      
    print_pseudo_litarray_root(f, rmap, a, nbits);
  }
  fputc('\n', f);
}




void print_bvsolver_atom(FILE *f, bv_solver_t *solver, int32_t id) {
  bv_atomtable_t *atbl;
  bvatm_t *atm;

  atbl = &solver->atbl;
  assert(0 <= id && id < atbl->natoms);
  atm = atbl->data + id;
  fputc('[', f);
  print_bvar(f, bvatm_bvar(atm));
  fputs(" := ", f);
  switch (bvatm_tag(atm)) {
  case BVEQ_ATM:
    fprintf(f, "(bveq u!%"PRId32" u!%"PRId32")", atm->left, atm->right);
    break;
  case BVUGE_ATM:
    fprintf(f, "(bvge u!%"PRId32" u!%"PRId32")", atm->left, atm->right);
    break;
  case BVSGE_ATM:
    fprintf(f, "(bvsge u!%"PRId32" u!%"PRId32")", atm->left, atm->right);
    break;
  }
  fputc(']', f);
}

void print_bvsolver_axiom(FILE *f, bv_solver_t *solver, int32_t id) {
  bv_atomtable_t *atbl;
  bvatm_t *atm;

  atbl = &solver->atbl;
  assert(0 <= id && id < atbl->natoms);
  atm = atbl->data + id;
  fputs("[axiom: ", f);
  switch (bvatm_tag(atm)) {
  case BVEQ_ATM:
    fprintf(f, "(bveq u!%"PRId32" u!%"PRId32")", atm->left, atm->right);
    break;
  case BVUGE_ATM:
    fprintf(f, "(bvge u!%"PRId32" u!%"PRId32")", atm->left, atm->right);
    break;
  case BVSGE_ATM:
    fprintf(f, "(bvsge u!%"PRId32" u!%"PRId32")", atm->left, atm->right);
    break;
  }
  if (atm->lit == true_literal) {
    fputs(" (true)", f);
  } else if (atm->lit == false_literal) {
    fputs(" (false)", f);
  } else {
    fputs(" (BUG)", f);
  }
  fputc(']', f);
}

void print_bvsolver_vars(FILE *f, bv_solver_t *solver) {
  uint32_t i, n;

  n = solver->vtbl.nvars;
  for (i=0; i<n; i++) {
    print_bvsolver_vardef(f, solver, i);
  }
}


void print_bvsolver_maps(FILE *f, bv_solver_t *solver) {
  uint32_t i, n;

  n = solver->vtbl.nvars;
  for (i=0; i<n; i++) {
    print_bvsolver_vardef(f, solver, i);
    print_bvsolver_varmap(f, solver, i);
    if (solver->remap != NULL) {
      print_bvsolver_root_varmap(f, solver, i);
    }
  }
}

void print_bvsolver_bitmaps(FILE *f, bv_solver_t *solver) {
  uint32_t i, n;

  n = solver->vtbl.nvars;
  for (i=0; i<n; i++) {
    print_bvsolver_vardef(f, solver, i);
    print_bvsolver_varmap(f, solver, i);
    if (solver->remap != NULL) {
      print_bvsolver_root_varmap(f, solver, i);
      print_bvsolver_varbitmap(f, solver, i);
    }
    fputc('\n', f);
  }
}

void print_bvsolver_atoms(FILE *f, bv_solver_t *solver) {
  bv_atomtable_t *atbl;
  uint32_t i, n;

  atbl = &solver->atbl;
  n = atbl->natoms;
  for (i=0; i<n; i++) {
    if (bvatm_bvar(atbl->data + i) != bool_const) {
      print_bvsolver_atom(f, solver, i);
      fputc('\n', f);
    }
  }

  for (i=0; i<n; i++) {
    if (bvatm_bvar(atbl->data + i) == bool_const) {
      print_bvsolver_axiom(f, solver, i);
      fputc('\n', f);
    }
  }
}


void print_bvsolver_partition(FILE *f, bv_solver_t *solver) {
  bv_partition_t *p;
  thvar_t *parent;
  thvar_t x, y;
  uint32_t i, n;

  p = &solver->partition;
  parent = p->parent;
  n = p->nelems;
  for (i=0; i<n; i++) {
    y = parent[i];
    if (y >= 0) {
      x = i;
      while (y != x) {
	x = y;
	y = parent[x];
      }
      if (i != y) {
	fprintf(f, "  u!%"PRIu32" --> u!%"PRId32"\n", i, y);
      }
    }
  }
}

#endif
