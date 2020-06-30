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
 * E-MATCHING FOR QUANTIFIERS
 */


#include "solvers/quant/quant_ematching.h"


#define TRACE 0

#if TRACE

#include <stdio.h>

#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/egraph/egraph_printer.h"

#include "yices.h"
#include "io/yices_pp.h"
#include "terms/term_explorer.h"

#endif


/*********************
 *   EMATCH STACK  *
 ********************/

/*
 * Initialize the stack
 */
static void init_ematch_stack(ematch_stack_t *stack) {
  assert(DEF_EMATCH_STACK_SIZE < MAX_EMATCH_STACK_SIZE);

  stack->size = DEF_EMATCH_STACK_SIZE;
  stack->top = 0;
  stack->data = (ematch_instr_t **) safe_malloc(DEF_EMATCH_STACK_SIZE * sizeof(ematch_instr_t *));
}


/*
 * Make the stack 50% larger
 */
static void extend_ematch_stack(ematch_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n >> 1;
  if (n >= MAX_EMATCH_STACK_SIZE) {
    out_of_memory();
  }

  stack->data = (ematch_instr_t **) safe_realloc(stack->data, n * sizeof(ematch_instr_t *));
  stack->size = n;
}


/*
 * Empty the stack
 */
static inline void reset_ematch_stack(ematch_stack_t *stack) {
  stack->top = 0;
}


/*
 * Delete the stack
 */
static void delete_ematch_stack(ematch_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Save data for the current top element:
 */
static void ematch_stack_save(ematch_stack_t *stack, ematch_instr_t *instr) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_ematch_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i] = instr;
  stack->top = i + 1;
}


/*
 * Get the top record
 */
static inline ematch_instr_t *ematch_stack_top(ematch_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data[stack->top - 1];
}


/*
 * Remove the top record
 */
static inline void ematch_stack_pop(ematch_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}





/************************
 *  EMATCH INSTR TABLE  *
 ***********************/

/*
 * Initialize: default size
 */
static void init_ematch_instr_table(ematch_instr_table_t *table) {
  assert(DEF_EMATCH_INSTR_TABLE_SIZE < MAX_EMATCH_INSTR_TABLE_SIZE);

  table->size = DEF_EMATCH_INSTR_TABLE_SIZE;
  table->ninstr = 0;
  table->data = (ematch_instr_t *) safe_malloc(DEF_EMATCH_INSTR_TABLE_SIZE * sizeof(ematch_instr_t));
}


/*
 * Make the table 50% larger
 */
static void extend_ematch_instr_table(ematch_instr_table_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  if (n >= MAX_EMATCH_INSTR_TABLE_SIZE) {
    out_of_memory();
  }
  table->data = (ematch_instr_t *) safe_realloc(table->data, n * sizeof(ematch_instr_t));
  table->size = n;
}


/*
 * Remove all ematch_instr of index >= n
 */
static void shrink_ematch_instr_table(ematch_instr_table_t *table, uint32_t n) {
  assert(n <= table->ninstr);

  table->ninstr = n;
}


/*
 * Empty the table: delete all ematch_instr objects
 */
static void reset_ematch_instr_table(ematch_instr_table_t *table) {
  shrink_ematch_instr_table(table, 0);
}


/*
 * Delete the table
 */
static void delete_ematch_instr_table(ematch_instr_table_t *table) {
  shrink_ematch_instr_table(table, 0);

  safe_free(table->data);
  table->data = NULL;
}


/*
 * Allocate a new ematch_instr index i
 * - data[i] is not initialized
 */
static int32_t ematch_instr_table_alloc(ematch_instr_table_t *table) {
  uint32_t i;
  ematch_instr_t *instr;

  i = table->ninstr;
  if (i == table->size) {
    extend_ematch_instr_table(table);
  }
  assert(i < table->size);
  table->ninstr = i+1;

  instr = &table->data[i];

  instr->op = EMATCH_NOOP;
  instr->f = NULL_TERM;
  instr->t = NULL_TERM;
  instr->i = 0;
  instr->j = 0;
  instr->o = 0;
  instr->subs = NULL;
  instr->nsubs = 0;
  instr->alt = -1;
  instr->next = -1;

  return i;
}


/***********************
 *   PATTERN COMPILER  *
 **********************/

#if TRACE
static void ematch_print_W(ematch_compile_t *comp, const char *comment) {
  int_hmap_t *W;
  int_hmap_pair_t *ip;

  W = &comp->W;
  printf("COMP.W #%d %s\n", W->nelems, comment);
  for (ip = int_hmap_first_record(W);
       ip != NULL;
       ip = int_hmap_next_record(W, ip)) {
    if (ip->key >= 0) {
      printf("  %d -> ", ip->key);
      yices_pp_term(stdout, ip->val, 120, 1, 0);
    }
  }
}
#endif

/*
 * Compile constant
 */
static int32_t ematch_compile_const(ematch_compile_t *comp, int32_t i, term_t t) {
  ematch_instr_table_t *itbl;
  int32_t idx;
  ematch_instr_t *instr;

  itbl = comp->itbl;
  idx = ematch_instr_table_alloc(itbl);
  instr = &itbl->data[idx];

  assert(term_kind(comp->terms, t) != VARIABLE);
  assert(term_kind(comp->terms, t) != APP_TERM);

  instr->op = EMATCH_CHECK;

  int_hmap_t *W;
  int_hmap_pair_t *ip;
//  term_t rhs;

  W = &comp->W;
  ip = int_hmap_find(W, i);
  assert(ip != NULL);
//  rhs = ip->val;
  int_hmap_erase(W, ip);

  instr->i = i;
  instr->t = t;

#if TRACE
  printf("    (pre) instr%d: check(%d, %s, instr%d)\n", idx, instr->i, yices_term_to_string(instr->t, 120, 1, 0), instr->next);
#endif

  instr->next = ematch_compile(comp);

#if TRACE
  printf("    instr%d: check(%d, %s, instr%d)\n", idx, instr->i, yices_term_to_string(instr->t, 120, 1, 0), instr->next);
#endif

  // Undo changes to comp
//  int_hmap_add(W, i, rhs);

  return idx;
}

/*
 * Compile variable
 */
static int32_t ematch_compile_var(ematch_compile_t *comp, int32_t i, term_t x) {
  int32_t idx;

  int_hmap_t *W;
  int_hmap_t *V;
  int_hmap_pair_t *ip;
//  term_t rhs;

  W = &comp->W;

  ip = int_hmap_find(W, i);
  assert(ip != NULL);
//  rhs = ip->val;
  int_hmap_erase(W, ip);

  V = &comp->V;
  ip = int_hmap_find(V, x);
  if (ip == NULL) {
    int_hmap_add(V, x, i);

    idx = ematch_compile(comp);

    // Undo changes to comp
    ip = int_hmap_find(V, x);
    int_hmap_erase(V, ip);

  } else {
    ematch_instr_table_t *itbl;
    ematch_instr_t *instr;

    itbl = comp->itbl;
    idx = ematch_instr_table_alloc(itbl);
    instr = &itbl->data[idx];

    instr->op = EMATCH_COMPARE;
    instr->i = i;
    instr->j = ip->val;

#if TRACE
    printf("    (pre) instr%d: compare(%d, %d, instr%d)\n", idx, instr->i, instr->j, instr->next);
#endif

    instr->next = ematch_compile(comp);

#if TRACE
    printf("    instr%d: compare(%d, %d, instr%d)\n", idx, instr->i, instr->j, instr->next);
#endif
  }

  // Undo changes to comp
//  int_hmap_add(W, i, rhs);

  return idx;
}

/*
 * Compile filter
 */
static int32_t* ematch_compile_filter(ematch_compile_t *comp, int32_t i, term_t f, int32_t *next) {
  ematch_instr_table_t *itbl;
  int32_t idx;
  ematch_instr_t *instr;

  itbl = comp->itbl;
  idx = ematch_instr_table_alloc(itbl);
  instr = &itbl->data[idx];

  *next = idx;
  instr->op = EMATCH_FILTER;
  instr->i = i;
  instr->subs = (int_pair_t *) safe_malloc(1 * sizeof(int_pair_t));
  instr->nsubs = 1;
  instr->subs[0].left = i;
  instr->subs[0].right = f;

#if TRACE
  printf("    instr%d: filter(%d, %s, instr++)\n", idx, instr->i, yices_term_to_string(instr->subs[0].right, 120, 1, 0), idx);
#endif

  return &instr->next;
}

/*
 * Compile function application
 */
static int32_t ematch_compile_fapp(ematch_compile_t *comp, int32_t i, term_t f) {
  ematch_instr_table_t *itbl;
  int32_t idx, j;
  ematch_instr_t *instr;

  itbl = comp->itbl;
  idx = ematch_instr_table_alloc(itbl);
  instr = &itbl->data[idx];

  assert(term_kind(comp->terms, f) == APP_TERM);
  instr->op = EMATCH_BIND;

  composite_term_t *app;
  uint32_t n, offset;
  int_hmap_t *W;
  int_hmap_pair_t *ip;
  term_table_t *terms;
//  term_t rhs;

  terms = comp->terms;
  app = app_term_desc(terms, f);
  n = app->arity - 1;
  offset = comp->o;

  W = &comp->W;

  ip = int_hmap_find(W, i);
  assert(ip != NULL);
//  rhs = ip->val;

  int_hmap_erase(W, ip);

  int32_t *next;
  term_t fx;

  next = &instr->next;
  for(j=0; j<n; j++) {
    fx = app->arg[j+1];
    if (term_kind(terms, fx) == APP_TERM) {
      next = ematch_compile_filter(comp, offset+j, composite_term_arg(terms, fx, 0), next);
    }
    int_hmap_add(W, offset+j, fx);
  }
  comp->o = offset + n;

  instr->i = i;
  instr->f = app->arg[0];
  instr->o = offset;

#if TRACE
  printf("    (pre) instr%d: bind(%d, %s, %d, instr%d)\n", idx, instr->i, yices_term_to_string(instr->f, 120, 1, 0), instr->o, instr->next);
#endif

  *next = ematch_compile(comp);

#if TRACE
  printf("    instr%d: bind(%d, %s, %d, instr%d)\n", idx, instr->i, yices_term_to_string(instr->f, 120, 1, 0), instr->o, instr->next);
#endif

  // Undo changes to comp
//  for(i=1; i<n; i++) {
//    ip = int_hmap_find(W, offset+i);
//    assert(ip != NULL);
//    int_hmap_erase(W, ip);
//  }
//  int_hmap_add(W, i, rhs);
  comp->o = offset;

  return idx;
}

/*
 * Compile empty set
 */
static int32_t ematch_compile_empty(ematch_compile_t *comp) {
  ematch_instr_table_t *itbl;
  int32_t idx;
  ematch_instr_t *instr;

  itbl = comp->itbl;
  idx = ematch_instr_table_alloc(itbl);
  instr = &itbl->data[idx];

  assert(comp->W.nelems == 0);

  instr->op = EMATCH_YIELD;

  int_hmap_t *V;
  uint32_t i, n;
  int_hmap_pair_t *ip;

  V = &comp->V;
  n = V->nelems;
  instr->subs = (int_pair_t *) safe_malloc(n * sizeof(int_pair_t));
  instr->nsubs = n;
  i = 0;
  for (ip = int_hmap_first_record(V);
       ip != NULL;
       ip = int_hmap_next_record(V, ip)) {
    if (ip->key >= 0) {
      instr->subs[i].left = ip->key;
      instr->subs[i].right = ip->val;
      i++;
    }
  }

#if TRACE
  printf("    instr%d: yield(#%d entries: ", idx, instr->nsubs);
  for (i=0; i<n; i++) {
    printf("%d <- %s, ", instr->subs[i].right, yices_term_to_string(instr->subs[i].left, 120, 1, 0));
  }
  printf(")\n");
#endif

  return idx;
}

/*
 * Compile based on working set
 */
int32_t ematch_compile(ematch_compile_t *comp) {
  int32_t idx;
  int_hmap_t *W;

  W = &comp->W;
  idx = -1;

  if (W->nelems == 0) {
    idx = ematch_compile_empty(comp);
  } else {
    term_table_t *terms;
    int_hmap_pair_t *ip;
    int32_t i;
    term_t x;

    terms = comp->terms;
    i = -1;
    x = NULL_TERM;

    for (ip = int_hmap_first_record(W);
         ip != NULL;
         ip = int_hmap_next_record(W, ip)) {
      if (ip->key > 0) {
//      if (ip->key > 0 && (i < 0 || ip->key < i)) {
        i = ip->key;
        x = ip->val;
        break;
      }
    }
    assert(i >= 0);

#if 0
    printf("Processing entry: %d -> ", i);
    yices_pp_term(stdout, x, 120, 1, 0);
#endif

    switch(term_kind(terms, x)) {
    case CONSTANT_TERM:
    case ARITH_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
      idx = ematch_compile_const(comp, i, x);
      break;

    case UNINTERPRETED_TERM:
      if (is_function_term(terms, x)) {
        printf("Unexpected term (kind %d): ", term_kind(terms, x));
        yices_pp_term(stdout, x, 120, 1, 0);
        assert(false);
      } else {
        idx = ematch_compile_const(comp, i, x);
      }
      break;

    case VARIABLE:
      idx = ematch_compile_var(comp, i, x);
      break;

    case APP_TERM:
      idx = ematch_compile_fapp(comp, i, x);
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
      printf("Unexpected term (kind %d): ", term_kind(terms, x));
      yices_pp_term(stdout, x, 120, 1, 0);
      assert(false);
      break;

    default:
      printf("Unsupported term (kind %d): ", term_kind(terms, x));
      yices_pp_term(stdout, x, 120, 1, 0);
      assert(false);
    }

  }

  return idx;
}

/*
 * Compile function
 */
static int32_t ematch_compile_func(ematch_compile_t *comp, composite_term_t *app) {
  ematch_instr_table_t *itbl;
  int32_t idx;
  ematch_instr_t *instr;

  itbl = comp->itbl;
  idx = ematch_instr_table_alloc(itbl);
  instr = &itbl->data[idx];

  instr->op = EMATCH_INIT;

  int_hmap_t *W;
  uint32_t j, n, offset;

  n = app->arity - 1;
  offset = comp->o;

  instr->f = app->arg[0];
  instr->o = offset;

  W = &comp->W;
  assert(comp->V.nelems == 0);

  term_table_t *terms;
  int32_t *next;
  term_t fx;

  terms = comp->terms;
  next = &instr->next;
  for(j=0; j<n; j++) {
    fx = app->arg[j+1];
    if (term_kind(terms, fx) == APP_TERM) {
      next = ematch_compile_filter(comp, offset+j+1, composite_term_arg(terms, fx, 0), next);
    }
    int_hmap_add(W, offset+j+1, fx);
  }
  comp->o += n+1;

#if TRACE
  printf("    (pre) instr%d: init(%s, %d, instr%d)\n", idx, yices_term_to_string(instr->f, 120, 1, 0), instr->o, instr->next);
//  ematch_print_W(comp, "(func: post)");
#endif

  *next = ematch_compile(comp);

#if TRACE
  printf("    instr%d: init(%s, %d, instr%d)\n", idx, yices_term_to_string(instr->f, 120, 1, 0), instr->o, instr->next);
#endif

  // Undo changes to comp
//  int_hmap_pair_t *ip;
//  for(j=0; j<n; j++) {
//    ip = int_hmap_find(W, offset+j+1);
//    assert(ip != NULL);
//    int_hmap_erase(W, ip);
//  }
  comp->o -= (n+1);

  return idx;
}

/*
 * Compile pattern to an instruction sequence
 * - returns an index in the instruction table
 */
static int32_t ematch_compile_pattern(ematch_compile_t *comp, term_t pat) {
  int32_t idx;
  term_table_t *terms;
  term_kind_t kind;

  assert(comp->W.nelems == 0);
  assert(comp->V.nelems == 0);

  idx = -1;
  terms = comp->terms;
  kind = term_kind(terms, pat);
  if (kind == APP_TERM) {
#if TRACE
    printf("  pattern: ");
    yices_pp_term(stdout, pat, 120, 1, 0);
#endif

    idx = ematch_compile_func(comp, app_term_desc(terms, pat));

#if TRACE
    printf("  code: instr%d\n", idx);
#endif
  } else {
    printf("Unsupported pattern term (kind %d): ", kind);
    yices_pp_term(stdout, pat, 120, 1, 0);
    assert(false);
  }

  return idx;
}


/*
 * Initialize pattern compiler
 */
static void init_ematch_compiler(ematch_compile_t *comp, ematch_instr_table_t *itbl, term_table_t *terms) {
  init_int_hmap(&comp->W, 0);
  init_int_hmap(&comp->V, 0);

  comp->o = 0;
  comp->itbl = itbl;
  comp->terms = terms;
}

/*
 * Reset pattern compiler
 */
static void reset_ematch_compiler(ematch_compile_t *comp) {
  int_hmap_reset(&comp->W);
  int_hmap_reset(&comp->V);

  comp->o = 0;
  comp->itbl = NULL;
  comp->terms = NULL;
}

/*
 * Delete pattern compiler
 */
static void delete_ematch_compiler(ematch_compile_t *comp) {
  delete_int_hmap(&comp->W);
  delete_int_hmap(&comp->V);

  comp->o = 0;
  comp->itbl = NULL;
  comp->terms = NULL;
}



/****************
 *   EMATCHING  *
 ***************/

/*
 * Initialize ematching
 */
void init_ematch(ematch_globals_t *em, term_table_t *terms, pattern_table_t *ptbl) {
  em->ptbl = ptbl;
  init_ematch_instr_table(&em->itbl);
  init_ematch_compiler(&em->comp, &em->itbl, terms);
  init_int_hmap(&em->pattern2code, 0);
  init_ivector(&em->reg, 10);
  init_ematch_stack(&em->bstack);
}

/*
 * Reset ematching
 */
void reset_ematch(ematch_globals_t *em) {
  reset_ematch_instr_table(&em->itbl);
  reset_ematch_compiler(&em->comp);
  int_hmap_reset(&em->pattern2code);
  ivector_reset(&em->reg);
  reset_ematch_stack(&em->bstack);
}

/*
 * Delete ematching
 */
void delete_ematch(ematch_globals_t *em) {
  delete_ematch_instr_table(&em->itbl);
  delete_ematch_compiler(&em->comp);
  delete_int_hmap(&em->pattern2code);
  delete_ivector(&em->reg);
  delete_ematch_stack(&em->bstack);
}

/*
 * Compile all patterns and fill in the pattern2code map
 */
void ematch_compile_all_patterns(ematch_globals_t *em) {
  ematch_compile_t *comp;
  int_hmap_t *pc;
  uint32_t i;
  term_t t;
  int_hmap_pair_t *ip;
  pattern_table_t *ptbl;
  pattern_t *pat;

  ptbl = em->ptbl;
  comp =  &em->comp;
  pc = &em->pattern2code;

  for(i=0; i<ptbl->npatterns; i++) {
    pat = &ptbl->data[i];
    t = pat->p;
    ip = int_hmap_get(pc, t);
    if (ip->val < 0) {
      ip->val = ematch_compile_pattern(comp, t);
      pat->code = ip->val;
    }
  }
}
