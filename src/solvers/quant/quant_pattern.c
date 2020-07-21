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
 * QUANTIFIER PATTERNS
 */


#include "solvers/quant/quant_pattern.h"
#include "utils/index_vectors.h"
#include "terms/term_explorer.h"
#include "yices.h"

#define TRACE 0

#if TRACE

#include <stdio.h>

#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/egraph/egraph_printer.h"

#endif



/*******************
 *  PATTERN TABLE  *
 ******************/

/*
 * Make the table 50% larger
 */
static void extend_pattern_table(pattern_table_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  if (n >= MAX_PATTERN_TABLE_SIZE) {
    out_of_memory();
  }
  table->data = (pattern_t *) safe_realloc(table->data, n * sizeof(pattern_t));
  table->size = n;
}


/*
 * Remove all patterns of index >= n
 */
static void shrink_pattern_table(pattern_table_t *table, uint32_t n) {
  uint32_t i;
  pattern_t *pat;

  assert(n <= table->npatterns);

  for(i=n; i<table->npatterns; i++) {
    pat = table->data + i;
    delete_index_vector(pat->pvars);
    delete_index_vector(pat->fun);
    delete_index_vector(pat->fapps);
    delete_index_vector(pat->consts);

    delete_ivector(&pat->matches);
  }

  table->npatterns = n;
}


/*
 * Initialize: default size
 */
void init_pattern_table(pattern_table_t *table) {
  assert(DEF_PATTERN_TABLE_SIZE < MAX_PATTERN_TABLE_SIZE);

  table->size = DEF_PATTERN_TABLE_SIZE;
  table->npatterns = 0;
  table->data = (pattern_t *) safe_malloc(DEF_PATTERN_TABLE_SIZE * sizeof(pattern_t));
}


/*
 * Empty the table: delete all pattern objects
 */
void reset_pattern_table(pattern_table_t *table) {
  shrink_pattern_table(table, 0);
}


/*
 * Delete the table
 */
void delete_pattern_table(pattern_table_t *table) {
  shrink_pattern_table(table, 0);

  safe_free(table->data);
  table->data = NULL;
}


/*
 * Allocate a new pattern index i
 * - data[i] is not initialized
 */
int32_t pattern_table_alloc(pattern_table_t *table) {
  uint32_t i;

  i = table->npatterns;
  if (i == table->size) {
    extend_pattern_table(table);
  }
  assert(i < table->size);
  table->npatterns = i+1;

  return i;
}


/*
 * Create a new pattern
 */
int32_t pattern_table_add_pattern(pattern_table_t *ptbl, term_t p, term_t *pv, uint32_t npv,
    term_t *f, uint32_t nf, term_t *fa, uint32_t nfa, term_t *c, uint32_t nc) {
  pattern_t *pat;
  int32_t i;

  i = pattern_table_alloc(ptbl);
  pat = ptbl->data + i;

  pat->p = p;
  pat->pvars = make_index_vector(pv, npv);
  pat->fun = make_index_vector(f, nf);
  pat->fapps = make_index_vector(fa, nfa);
  pat->consts = make_index_vector(c, nc);
  pat->code = -1;
  init_ivector(&pat->matches, 4);

  return i;
}


/*
 * Recursively push all variables, functions, function applications and constants that occur in term t
 */
void quant_process_pattern_term(term_table_t *terms, term_t t, ivector_t *pv, ivector_t *f,
    ivector_t *fa, ivector_t *c) {
  term_t x, u;
  term_kind_t kind;
  uint32_t i, n;

  x = unsigned_term(t);
  kind = term_kind(terms, x);

  // process all children (if any)
  n = term_num_children(terms, x);
  for(i=0; i<n; i++) {
    u = term_child(terms, x, i);
    quant_process_pattern_term(terms, u, pv, f, fa, c);
  }

  switch (kind) {
  case CONSTANT_TERM:
  case ARITH_CONSTANT:
  case BV64_CONSTANT:
  case BV_CONSTANT:
    // nothing to do
    break;

  case UNINTERPRETED_TERM:
    // add to vector c
    if (is_function_term(terms, x)) {
      ivector_push(f, x);
#if 0
      printf("    adding function: ");
      yices_pp_term(stdout, x, 120, 1, 0);
#endif
    } else {
      ivector_push(c, x);
#if 0
      printf("    adding constant: ");
      yices_pp_term(stdout, x, 120, 1, 0);
#endif
    }
    break;

  case VARIABLE:
    // add to vector pv
    ivector_push(pv, x);
#if 0
    printf("    adding var: ");
    yices_pp_term(stdout, x, 120, 1, 0);
#endif
    break;

  case APP_TERM:
    // add to vector fa
    ivector_push(fa, x);
#if 0
    printf("    adding fapp: ");
    yices_pp_term(stdout, x, 120, 1, 0);
#endif
    break;

  case ARITH_EQ_ATOM:
  case EQ_TERM:            // equality
  case ARITH_BINEQ_ATOM:
  case BV_EQ_ATOM:
  case ITE_TERM:
  case ITE_SPECIAL:
  case DISTINCT_TERM:
  case OR_TERM:            // n-ary OR
  case XOR_TERM:           // n-ary XOR
    // nothing to do
    break;

  default:
//    printf("Unsupported term (kind %d): ", kind);
//    yices_pp_term(stdout, x, 120, 1, 0);
    assert(false);
  }
}


/*
 * Recursively check if an fapp contains all uvars, and if yes, push in out vector
 */
static void quant_infer_single_fapps(term_table_t *terms, term_t t, int_hmap_t *uvarMap, uint32_t nuvars, ivector_t *out) {
  term_t x, u;
  term_kind_t kind;
  uint32_t i, n;
  int_hmap_pair_t *p, *p2;
  int_hmap_t tmpMap;
  int_hmap_t *childMap;

  childMap = &tmpMap;
  x = unsigned_term(t);
  kind = term_kind(terms, x);

#if TRACE
  printf("    processing term ");
  yices_pp_term(stdout, t, 120, 1, 0);
#endif

  // process all children (if any)
  n = term_num_children(terms, x);
  if (n != 0) {
    init_int_hmap(childMap, 0);
    for(i=0; i<n; i++) {
      u = term_child(terms, x, i);
      int_hmap_reset(childMap);
      quant_infer_single_fapps(terms, u, childMap, nuvars, out);

      // add child map to parent based on the kind of child
      switch (term_kind(terms, u)) {
      case CONSTANT_TERM:
      case ARITH_CONSTANT:
      case BV64_CONSTANT:
      case BV_CONSTANT:
      case UNINTERPRETED_TERM:
      case VARIABLE:
      case APP_TERM:
        for (p2 = int_hmap_first_record(childMap);
             p2 != NULL;
             p2 = int_hmap_next_record(childMap, p2)) {
          p = int_hmap_get(uvarMap, p2->key);
          p->val = p2->val;
        }
        break;

      case ARITH_EQ_ATOM:
      case EQ_TERM:            // equality
      case ARITH_BINEQ_ATOM:
      case BV_EQ_ATOM:
      case ITE_TERM:
      case ITE_SPECIAL:
      case DISTINCT_TERM:
      case OR_TERM:            // n-ary OR
      case XOR_TERM:           // n-ary XOR
        // reset the map
        break;

      default:
//        printf("Unsupported term (kind %d): ", kind);
//        yices_pp_term(stdout, x, 120, 1, 0);
        assert(false);
      }

    }
    delete_int_hmap(childMap);
  }

  // find fapps
  switch (kind) {
  case CONSTANT_TERM:
  case ARITH_CONSTANT:
  case BV64_CONSTANT:
  case BV_CONSTANT:
  case UNINTERPRETED_TERM:
    // nothing to do
    break;

  case VARIABLE:
    p = int_hmap_get(uvarMap, x);
    p->val = 1;
#if TRACE
    printf("    found var: ");
    yices_pp_term(stdout, x, 120, 1, 0);
#endif
    break;

  case APP_TERM:
    if (uvarMap->nelems == nuvars) {
      ivector_push(out, x);
#if TRACE
      printf("    found fapp: ");
      yices_pp_term(stdout, x, 120, 1, 0);
#endif
    }
    break;

  case ARITH_EQ_ATOM:
  case EQ_TERM:            // equality
  case ARITH_BINEQ_ATOM:
  case BV_EQ_ATOM:
  case ITE_TERM:
  case ITE_SPECIAL:
  case DISTINCT_TERM:
  case OR_TERM:            // n-ary OR
  case XOR_TERM:           // n-ary XOR
    // reset the map
    break;

  default:
//    printf("Unsupported term (kind %d): ", kind);
//    yices_pp_term(stdout, x, 120, 1, 0);
    assert(false);
  }
}

/*
 * Infer single patterns for term t, by recursively finding fapps which contain all uvars
 */
void quant_infer_single_pattern(term_table_t *terms, term_t t, ivector_t *uvars, ivector_t *out) {
  int_hmap_t uvarMap;

  init_int_hmap(&uvarMap, 0);
  quant_infer_single_fapps(terms, t, &uvarMap, uvars->size, out);
  delete_int_hmap(&uvarMap);
}





