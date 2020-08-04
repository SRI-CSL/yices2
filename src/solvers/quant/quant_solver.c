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
 * SOLVER FOR QUANTIFIERS
 */



#include <inttypes.h>

#include "io/tracer.h"
#include "solvers/quant/quant_solver.h"
#include "solvers/quant/quant_ematching.h"
#include "utils/hash_functions.h"
#include "utils/index_vectors.h"
#include "utils/int_array_sort2.h"
#include "utils/int_hash_classes.h"
#include "utils/memalloc.h"
#include "utils/pointer_vectors.h"
#include "utils/ptr_array_sort2.h"
#include "utils/ptr_partitions.h"
#include "terms/term_explorer.h"
#include "yices.h"
#include "context/internalization_codes.h"
#include "context/quant_context_utils.h"
#include "terms/term_substitution.h"
#include "utils/prng.h"

#define EM_VERBOSE 0

#define TRACE 0
#define TRACE_LIGHT 0

#if TRACE || TRACE_LIGHT

#include <stdio.h>

#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/egraph/egraph_printer.h"

#endif


/**********************
 *  PRINTING SUPPORT  *
 *********************/

# if 0
static void quant_solver_print_pattern(FILE *f, quant_solver_t *solver, uint32_t i) {
  pattern_t *pat;
  uint32_t n;

  assert(i < solver->ptbl.npatterns);

  pat = solver->ptbl.data + i;

  fprintf(f, "    pattern @%d: ", i);
  yices_pp_term(f, pat->p, 120, 1, 0);

  n = iv_len(pat->pvars);
  fprintf(f, "      pvars (#%d): ", n);
  yices_pp_term_array(f, n, pat->pvars, 120, 1, 0, 1);

  n = iv_len(pat->fun);
  fprintf(f, "      fun (#%d): ", n);
  yices_pp_term_array(f, n, pat->fun, 120, 1, 0, 1);

  n = iv_len(pat->fapps);
  fprintf(f, "      fapps (#%d): ", n);
  yices_pp_term_array(f, n, pat->fapps, 120, 1, 0, 1);

  n = iv_len(pat->consts);
  fprintf(f, "      consts (#%d): ", n);
  yices_pp_term_array(f, n, pat->consts, 120, 1, 0, 1);

  fprintf(f, "\n");

}

static void quant_solver_print_cnstr(FILE *f, quant_solver_t *solver, uint32_t i) {
  quant_cnstr_t *qcnstr;
  uint32_t j, n;

  assert(i < solver->qtbl.nquant);

  qcnstr = solver->qtbl.data + i;
  fprintf(f, "\nqcnstr[%d]:\n", i);

  fprintf(f, "  en: ");
  yices_pp_term(f, qcnstr->enable, 120, 1, 0);

  fprintf(f, "  expr: ");
  yices_pp_term(f, qcnstr->t, 120, 1, 0);

  n = iv_len(qcnstr->uvars);
  fprintf(f, "      uvars (#%d): ", n);
  yices_pp_term_array(f, n, qcnstr->uvars, 120, 1, 0, 1);

  n = iv_len(qcnstr->fun);
  fprintf(f, "      fun (#%d): ", n);
  yices_pp_term_array(f, n, qcnstr->fun, 120, 1, 0, 1);

  n = iv_len(qcnstr->fapps);
  fprintf(f, "      fapps (#%d): ", n);
  yices_pp_term_array(f, n, qcnstr->fapps, 120, 1, 0, 1);

  n = iv_len(qcnstr->consts);
  fprintf(f, "      consts (#%d): ", n);
  yices_pp_term_array(f, n, qcnstr->consts, 120, 1, 0, 1);

  n = iv_len(qcnstr->patterns);
  fprintf(f, "  patterns (#%d):\n", n);
  for (j=0; j<n; j++)
    quant_solver_print_pattern(f, solver, qcnstr->patterns[j]);

  fprintf(f, "\n");

}
#endif


/**************************
 *  PROBLEM CONSTRUCTION  *
 *************************/

/*
 * Infer patterns for term t
 *   infer new patterns and add them to patterns vector
 */
static void quant_infer_patterns(quant_solver_t *solver, term_t t, ivector_t *patterns, ivector_t *uvars) {
  ivector_t prospectives;
  term_t x;
  uint32_t i, n;

#if TRACE
  printf("  Inferring pattern for ");
  yices_pp_term(stdout, t, 120, 1, 0);
#endif

  init_ivector(&prospectives, 4);

  quant_infer_single_pattern(solver->prob->terms, t, uvars, &prospectives);
  if (prospectives.size == 0) {
    quant_infer_multi_pattern(solver->prob->terms, t, uvars, &prospectives);
  }

  ivector_remove_duplicates(&prospectives);

  n = prospectives.size;
  if (n != 0) {
#if TRACE
    printf("    found #%d prospectives: ", n);
    yices_pp_term_array(stdout, n, prospectives.data, 120, 1, 0, 1);
#endif

//    n = 1;    // restrict to only the first inferred pattern
    for(i=0; i<n; i++) {
      x = prospectives.data[i];
      ivector_push(patterns, x);
    }

#if TRACE
    printf("    added #%d patterns\n", n);
#endif
  }

  delete_ivector(&prospectives);
}


/*
 * Preprocess pattern, add pattern to pattern table, and return its index
 */
static int32_t quant_preprocess_pattern(quant_solver_t *solver, term_t t, term_t pat) {
  int_hmap_pair_t *r;
  r = int_hmap_get(&solver->aux_map, pat);
  if (r->val >= 0) {
    return r->val;
  }

  ivector_t pv, f, fa, c;
  int32_t i;

  init_ivector(&pv, 5);
  init_ivector(&f, 5);
  init_ivector(&fa, 5);
  init_ivector(&c, 5);

  quant_process_pattern_term(solver->prob->terms, pat, &pv, &f, &fa, &c);
  ivector_remove_duplicates(&pv);
  ivector_remove_duplicates(&f);
  ivector_remove_duplicates(&fa);
  ivector_remove_duplicates(&c);

  i = pattern_table_add_pattern(&solver->ptbl, pat, pv.data, pv.size, f.data, f.size,
                           fa.data, fa.size, c.data, c.size);

  delete_ivector(&pv);
  delete_ivector(&f);
  delete_ivector(&fa);
  delete_ivector(&c);

#if 0
  printf("    Adding pattern:\n");
  quant_solver_print_pattern(stdout, solver, i);
#endif

  r->val = i;
  return i;
}

/*
 * Setup patterns for term t
 *   if patterns present, try pruning
 *   else, infer patterns
 *   add all the final patterns and push their indices in out vector
 */
static void quant_setup_patterns(quant_solver_t *solver, term_t t, ivector_t *patterns, ivector_t *uvars, ivector_t *out) {
  uint32_t i, n;
  term_t *data;
  term_t x;
  int32_t idx;

  n = patterns->size;
  if (n == 0) {
    quant_infer_patterns(solver, t, patterns, uvars);
    n = patterns->size;
  }
#if 0
  printf("  Total #%d patterns\n", n);
#endif

  data = patterns->data;
  for (i=0; i<n; i++) {
    x = data[i];

    idx = quant_preprocess_pattern(solver, t, x);

    assert(idx >= 0);
    ivector_push(out, idx);
    assert(x == solver->ptbl.data[idx].p);
  }
}

/*
 * Preprocess problem constraint
 */
static int32_t quant_preprocess_assertion_with_pattern(quant_solver_t *solver, term_t t, ivector_t *patterns) {
  quant_table_t *qtbl;
  int32_t i;
  ivector_t v;
  quant_cnstr_t *cnstr;
  ivector_t pv, f, fa, c;
  bool valid;
  char name[16];

  qtbl = &solver->qtbl;
  init_ivector(&v, 1);
  init_ivector(&pv, 5);
  init_ivector(&f, 5);
  init_ivector(&fa, 5);
  init_ivector(&c, 5);

  quant_process_pattern_term(solver->prob->terms, t, &pv, &f, &fa, &c);
  ivector_remove_duplicates(&pv);
  ivector_remove_duplicates(&f);
  ivector_remove_duplicates(&fa);
  ivector_remove_duplicates(&c);

  quant_setup_patterns(solver, t, patterns, &pv, &v);
  ivector_remove_duplicates(&v);

  i = quant_table_add_cnstr(qtbl, t, v.data, v.size);
  cnstr = qtbl->data + i;

  cnstr->enable = new_uninterpreted_term(solver->prob->terms, bool_type(solver->prob->terms->types));
  sprintf (name, "quant$%d", i);
  yices_set_term_name(cnstr->enable, name);

  cnstr->uvars = make_index_vector(pv.data, pv.size);
  cnstr->fun = make_index_vector(f.data, f.size);
  cnstr->fapps = make_index_vector(fa.data, fa.size);
  cnstr->consts = make_index_vector(c.data, c.size);

  valid = quant_table_check_cnstr(qtbl, &solver->ptbl, i);
  if (!valid) {
#if TRACE_LIGHT
    printf("\nError in assertion + pattern for:\n");
    quant_solver_print_cnstr(stdout, solver, i);
#endif

    ivector_reset(patterns);
    ivector_reset(&v);
    delete_index_vector(cnstr->patterns);

    quant_setup_patterns(solver, t, patterns, &pv, &v);
    cnstr->patterns = make_index_vector(v.data, v.size);

    valid = quant_table_check_cnstr(qtbl, &solver->ptbl, i);
#if TRACE_LIGHT
    printf("\nNew assertion + pattern for:\n");
    quant_solver_print_cnstr(stdout, solver, i);
#endif
    assert(valid);
  }

  delete_ivector(&v);
  delete_ivector(&pv);
  delete_ivector(&f);
  delete_ivector(&fa);
  delete_ivector(&c);

#if TRACE_LIGHT
  quant_solver_print_cnstr(stdout, solver, i);
#endif

  return i;
}

/*
 * Preprocess problem
 */
static void quant_preprocess_prob(quant_solver_t *solver) {
  ef_prob_t *prob;
  ptr_hmap_t *patterns;
  ptr_hmap_pair_t *r;

  prob = solver->prob;
  patterns = prob->patterns;
  int_hmap_reset(&solver->aux_map);

  if (patterns != NULL) {
    for (r = ptr_hmap_first_record(patterns);
         r != NULL;
         r = ptr_hmap_next_record(patterns, r)) {
      quant_preprocess_assertion_with_pattern(solver, r->key, r->val);
    }
  }
}

/*
 * Assert all enable constraints
 */
static void ematch_assert_all_enables(quant_solver_t *solver) {
  quant_table_t *qtbl;
  uint32_t i, n;
  quant_cnstr_t *cnstr;
  context_t *ctx;

  qtbl = &solver->qtbl;
  n = qtbl->nquant;
  ctx = solver->em.ctx;

  for(i=0; i<n; i++) {
    cnstr = qtbl->data + i;
    assert_formula(ctx, cnstr->enable);
  }
}

/*
 * Attach problem to solver
 */
void quant_solver_attach_prob(quant_solver_t *solver, ef_prob_t *prob, context_t *ctx) {
  assert(solver->prob == NULL);

  solver->prob = prob;
  quant_preprocess_prob(solver);
  learner_setup(&solver->learner);
//  assert(0);

  ematch_attach_tbl(&solver->em, solver->prob->terms, &solver->ptbl, &solver->qtbl, ctx);
  ematch_compile_all_patterns(&solver->em);

  ematch_attach_egraph(&solver->em, solver->egraph);

  ematch_assert_all_enables(solver);
}


/**********************
 *  STATISTIC RECORD  *
 *********************/

static void init_quant_solver_statistics(quant_solver_stats_t *stat) {
  stat->num_quantifiers = 0;
  stat->num_patterns = 0;

  stat->num_instances = 0;
  stat->num_instances_per_search = 0;
  stat->num_instances_per_round = 0;

  stat->num_rounds_per_search = 0;
  stat->num_search = 0;

  stat->max_instances = DEFAULT_MAX_INSTANCES;
  stat->max_instances_per_search = DEFAULT_MAX_INSTANCES_PER_SEARCH;
  stat->max_instances_per_round = DEFAULT_MAX_INSTANCES_PER_ROUND;

  stat->max_rounds_per_search = DEFAULT_MAX_ROUNDS_PER_SEARCH;
  stat->max_search = DEFAULT_MAX_SEARCH;
}

static inline void reset_quant_solver_statistics(quant_solver_stats_t *stat) {
  init_quant_solver_statistics(stat);
}

static inline void ematch_reset_start_stats(quant_solver_t *solver) {
  solver->stats.num_search++;
  solver->stats.num_instances_per_search = 0;
  solver->stats.num_rounds_per_search = 0;

  learner_reset_round(&solver->learner, true);
}

static inline void ematch_reset_round_stats(quant_solver_t *solver) {
  solver->stats.num_instances_per_round = 0;
}

static inline bool ematch_reached_instance_limit(quant_solver_t *solver) {
  return (solver->stats.num_instances >= solver->stats.max_instances) ||
         (solver->stats.num_instances_per_search >= solver->stats.max_instances_per_search) ||
         (solver->stats.num_instances_per_round >= solver->stats.max_instances_per_round);
}

static inline bool ematch_reached_round_limit(quant_solver_t *solver) {
  return (solver->stats.num_rounds_per_search >= solver->stats.max_rounds_per_search);
}

static inline bool ematch_reached_search_limit(quant_solver_t *solver) {
  return (solver->stats.num_search >= solver->stats.max_search);
}


/***********************
 *  EMATCHING SUPPORT  *
 **********************/

/*
 * Apply the substitution defined by var and value to term t
 * - n = size of arrays var and value
 * - return code < 0 means that an error occurred during the substitution
 *   (cf. apply_term_subst in term_substitution.h).
 */
static term_t term_substitution(quant_solver_t *solver, term_t *var, term_t *value, uint32_t n, term_t t) {
  term_subst_t subst;
  term_t g;
  int_hmap_pair_t *p;
  uint32_t i;
  term_t x;

  subst.mngr = solver->prob->manager;
  subst.terms = solver->prob->terms;
  init_int_hmap(&subst.map, 0);
  init_subst_cache(&subst.cache);
  init_istack(&subst.stack);
  subst.rctx = NULL;

  for (i=0; i<n; i++) {
    x = var[i];
    p = int_hmap_get(&subst.map, x);
    p->val = value[i];

    assert(is_pos_term(x));
    assert(good_term(subst.terms, x));
    assert(term_kind(subst.terms, x) == VARIABLE);
    assert(good_term(subst.terms, p->val));
  }

  g = apply_term_subst(&subst, t);
  delete_term_subst(&subst);

  return g;
}

/*
 * Find the term mapped to a given occurence
 */
static term_t find_intern_mapping(intern_tbl_t *tbl, occ_t rhs) {
  return intern_tbl_reverse_map(tbl, rhs);

  term_table_t *terms;
  uint32_t i, n;
  term_t r;
  int32_t code;
  bool negate;

  negate = is_neg_occ(rhs);
  if (negate)
    rhs = opposite_occ(rhs);

  terms = tbl->terms;
  n = tbl->map.top;
  for (i=0; i<n; i++) {
    if (good_term_idx(terms, i) && intern_tbl_is_root_idx(tbl, i)) {
      r = pos_term(i);
      if (intern_tbl_root_is_mapped(tbl, r)) {
        code = intern_tbl_map_of_root(tbl, r);
        if (code_is_valid(code) &&
            code_is_eterm(code) &&
            code2occ(code) == rhs) {
          return negate ? opposite_term(r) : r;
        }
      }
    }
  }

  return NULL_TERM;
}


/*
 * Instantiate constraint cnstr with match at index idx
 */
static bool ematch_cnstr_instantiate(quant_solver_t *solver, uint32_t cidx, pattern_t *pat, uint32_t midx) {
  quant_cnstr_t *cnstr;
  int_hset_t *instances;
  ematch_globals_t *em;
  context_t *ctx;
  intern_tbl_t *intern;
  instance_table_t *instbl;
  instance_t * inst;
  term_t t;
  uint32_t i, n;
  term_t rhst;
  occ_t rhs;
  uint32_t term_cost;

  assert(cidx < solver->qtbl.nquant);
  cnstr = solver->qtbl.data + cidx;

  instances = &cnstr->instances;
  if (int_hset_member(instances, midx)) {
#if TRACE
    printf("\n  already done with match%d\n", midx);
#endif
//    assert(0);
    return false;
  }

  em = &solver->em;
  ctx = em->ctx;
  intern = &ctx->intern;
  instbl = &em->instbl;
  t = cnstr->t;
  term_cost = ctx->terms->nelems;

  assert(midx < instbl->ninstances);
  inst = instbl->data + midx;

#if TRACE
  printf("S%d:R%d EMATCHED: #%d cnstr%d::match%d\n",
      solver->stats.num_search,
      solver->stats.num_rounds_per_search,
      solver->stats.num_instances_per_round, cidx, midx);
#endif

#if 0
  printf("\nInstantiating %s\n", yices_term_to_string(t, 120, 1, 0));
#endif
//  assert(is_boolean_term(ctx->terms, t));
//  assert(intern_tbl_is_root(&ctx->intern, t));
//  assert(term_is_true(ctx, t));

  n = inst->nelems;
  assert(n == iv_len(pat->pvars));

  term_t *keys = (term_t *) safe_malloc(n * sizeof(term_t));
  term_t *values = (term_t *) safe_malloc(n * sizeof(term_t));
  for(i=0; i<n; i++) {
    rhs = inst->odata[i];
    assert(occ_depth(solver->egraph, rhs) < solver->em.exec.max_vdepth);

    rhst = find_intern_mapping(intern, rhs);
    assert(rhst != NULL_TERM);

    keys[i] = inst->vdata[i];
    values[i] = rhst;

#if 0
    printf("reverse map: ");
    print_occurrence(stdout, rhs);
    printf(" @ depth %d --> ", occ_depth(solver->egraph, rhs));
    yices_pp_term(stdout, rhst, 120, 1, 0);
    printf("\n");
#endif
  }

  t = term_substitution(solver, keys, values, n, t);

  term_cost = ctx->terms->nelems - term_cost;
  if (term_cost > 0) {
    learner_update_term_reward(&solver->learner, term_cost, cidx);
  }

  safe_free(keys);
  safe_free(values);

#if EM_VERBOSE
    printf("EMATCH Instance: ");
    yices_pp_term(stdout, t, 120, 1, 0);
    printf("\n");
#endif

  ivector_push(&solver->round_cnstrs, cidx);
  ivector_push(&solver->round_instances, t);

  int_hset_add(instances, midx);

  return true;
}

/*
 * Add quant instantiate constraint to solver
 */
static void ematch_add_quant_cnstr(quant_solver_t *solver, uint32_t cidx, term_t t) {
  quant_cnstr_t *cnstr;
  context_t *ctx;
  ematch_globals_t *em;
  uint32_t i, n;
  uint32_t lemma_cost;
//  uint32_t term_cost;

  em = &solver->em;
  ctx = em->ctx;

  assert(cidx < solver->qtbl.nquant);
  cnstr = solver->qtbl.data + cidx;
//  term_cost = ctx->terms->nelems;

  quant_assert_formulas(ctx, 1, &t);

//  term_cost = ctx->terms->nelems - term_cost;
//  if (term_cost > 0) {
//    learner_update_term_reward(&solver->learner, term_cost, cidx);
//  }

  if (cnstr->enable_lit == null_literal) {
    cnstr->enable_lit = not(context_internalize(ctx, cnstr->enable));
//    cnstr->enable_lit = context_internalize(ctx, cnstr->enable);
  }

  ivector_t *lits, *ants;
  ivector_t *units;
  literal_t l;

  lits = &solver->base_literals;
  ants = &solver->base_antecedents;
  units = &solver->aux_vector;

  ivector_reset(units);

#if TRACE
  printf("(BEGIN): decision level = %d (base level = %d)\n", solver->decision_level, solver->base_level);
#endif

  lemma_cost = add_all_quant_lemmas(solver->core, cnstr->enable_lit, units);
  if (lemma_cost > 0) {
    learner_update_lemma_reward(&solver->learner, lemma_cost, cidx);
  }

#if TRACE
  printf("(END): decision level = %d (base level = %d)\n", solver->decision_level, solver->base_level);
#endif

  n = units->size;
  for(i=0; i<n; i++) {
    l = units->data[i];
    if (solver->decision_level == solver->base_level) {
      switch(literal_base_value(solver->core, l)) {
      case VAL_FALSE:
        record_unit_theory_conflict(solver->core, l);
        break;
      case VAL_TRUE:
        break;
      default:
        implied_literal(solver->core, l, mk_literal_antecedent(cnstr->enable_lit));
      }
    } else {
#if TRACE
      printf("EMATCH: Delaying unit base clause: { ");
      print_literal(stdout, l);
      printf(" }\n");
#endif
      ivector_push(lits, l);
      ivector_push(ants, cnstr->enable_lit);
    }
  }

  ivector_reset(units);
}

/*
 * Match and learn instances for a given cnstr at index idx
 */
static void ematch_process_cnstr(quant_solver_t *solver, uint32_t cidx) {
  ematch_globals_t *em;
  ematch_exec_t *exec;
  pattern_table_t *ptbl;
  quant_table_t *qtbl;
  uint32_t npat, i, j, n;
  quant_cnstr_t *cnstr;
  int32_t *patterns;
  pattern_t *pat;
  ivector_t *matches;
  smt_status_t status;
  uint32_t oldcount, nadded;

  em = &solver->em;
  exec =  &em->exec;
  qtbl = em->qtbl;
  ptbl = em->ptbl;

  cnstr = qtbl->data + cidx;
  oldcount = solver->stats.num_instances_per_round;
  nadded = 0;

#if TRACE_LIGHT
  printf("-------------------\n");
  printf("Trying matching cnstr @%d: ", cidx);
  yices_pp_term(stdout, cnstr->t, 120, 1, 0);
#endif

  patterns = cnstr->patterns;
  npat = iv_len(patterns);
  if (npat != 0) {
    for(j=0; j<npat; j++) {
      pat = ptbl->data + patterns[j];

#if TRACE
      printf("\n  Matching pattern @%d: ", patterns[j]);
      yices_pp_term(stdout, pat->p, 120, 1, 0);
#endif

      ematch_exec_pattern(exec, pat, &cnstr->instances);

      matches = &pat->matches;
      n = matches->size;

      for(i=0; i<n; i++) {
        status = smt_status(solver->core);
        if (status != STATUS_SEARCHING) {
#if TRACE
          printf("\nSMT status: %d\n", status);
#endif
          assert(status == STATUS_UNSAT);
          goto done;
        } else if(ematch_reached_instance_limit(solver)) {
#if TRACE
          printf("\nReached max round limit after learning #%d instances\n", solver->stats.num_instances_per_round);
#endif
          goto done;
        } else {
          if (ematch_cnstr_instantiate(solver, cidx, pat, matches->data[i])) {
            solver->stats.num_instances_per_round++;
            solver->stats.num_instances_per_search++;
            solver->stats.num_instances++;
          }
        }
      }
    }
  }

done:
  nadded = (solver->stats.num_instances_per_round - oldcount);
  if (nadded != 0) {
    if (oldcount == 0) {
      ivector_reset(&solver->learner.latest_cnstr);
    }
    learner_add_cnstr(&solver->learner, cidx);
  }

#if TRACE_LIGHT
  if(nadded != 0) {
    printf("Found #%d instances for cnstr @%d\n", nadded, cidx);
  }
#endif
  return;
}


/*
 * Match and learn all instances in serial order
 */
static void ematch_process_cnstr_all(quant_solver_t *solver) {
  quant_table_t *qtbl;
  uint32_t i, n;

#if TRACE_LIGHT
  printf("  Instantiation mode: All\n");
#endif

  qtbl = &solver->qtbl;
  n = qtbl->nquant;

  for(i=0; i<n; i++) {
    if (ematch_reached_instance_limit(solver))
      break;
    ematch_process_cnstr(solver, i);
  }

}

/*
 * Match and learn instances in random order
 */
static void ematch_process_cnstr_random(quant_solver_t *solver) {
  quant_table_t *qtbl;
  uint32_t i, n, randIdx;
  int_hmap_t *aux;
  int_hmap_pair_t *p;
  uint32_t seed;

#if TRACE_LIGHT
  printf("  Instantiation mode: Explore\n");
#endif

  qtbl = &solver->qtbl;
  n = qtbl->nquant;
  aux = &solver->aux_map;
  seed = solver->learner.seed;

  int_hmap_reset(aux);

  for(i=0; i<n; i++) {
    randIdx = random_uint(&seed, n);
    assert(randIdx >=0 && randIdx < n);

    p = int_hmap_get(aux, randIdx);
    if (p->val < 0) {
      if (ematch_reached_instance_limit(solver))
        break;

      p->val = 1;
      ematch_process_cnstr(solver, randIdx);
    } else {
      // already present in aux
      // do nothing
    }
  }

}

/*
 * Match and learn instances based on greedy (priority) order
 */
static void ematch_process_cnstr_greedy(quant_solver_t *solver) {
  quant_table_t *qtbl;
  uint32_t i, n;
  learner_t *learner;
  generic_heap_t *heap;
  ivector_t *aux;

#if TRACE_LIGHT
  printf("  Instantiation mode: Exploit\n");
#endif

  qtbl = &solver->qtbl;
  n = qtbl->nquant;
  learner = &solver->learner;
  heap = &learner->cnstr_heap;
  aux = &solver->aux_vector;

  ivector_reset(aux);

  while(!generic_heap_is_empty(heap)) {
    if (ematch_reached_instance_limit(solver))
      break;

    // pop out top element
    i = generic_heap_get_min(heap);
    assert(i >=0 && i < n);
    ivector_push(aux, i);

    ematch_process_cnstr(solver, i);

    // TODO: possibly modify cnstr priorities here
  }

  // add all popped indices back to heap
  n = aux->size;
  for(i=0; i<n; i++) {
    generic_heap_add(heap, aux->data[i]);
  }

}

/*
 * Match and learn instances based on epsilon-greedy approach
 */
static void ematch_process_cnstr_epsilon_greedy(quant_solver_t *solver) {
  learner_t *learner;
  uint32_t randIdx;

  learner = &solver->learner;
  randIdx = random_uint(&learner->seed, RL_EPSILON_MAX);
  if (randIdx < learner->epsilon) {
    ematch_process_cnstr_random(solver);
  } else {
    ematch_process_cnstr_greedy(solver);
  }

}

/*
 * Match and learn instances
 */
static void ematch_process_all_cnstr(quant_solver_t *solver) {
  uint32_t i, n;

  learner_update_last_round(&solver->learner, true);

#if TRACE_LIGHT
  quant_print_all_cnstr_priority(solver->learner.qtbl, "(begin)");
#endif

  ivector_reset(&solver->round_cnstrs);
  ivector_reset(&solver->round_instances);

  context_enable_quant(solver->em.ctx);
  ematch_reset_round_stats(solver);

  switch(solver->iter_mode) {
  case ITERATE_RANDOM:
    ematch_process_cnstr_random(solver);
    break;
  case ITERATE_GREEDY:
    ematch_process_cnstr_greedy(solver);
    break;
  case ITERATE_EPSILONGREEDY:
    ematch_process_cnstr_epsilon_greedy(solver);
    break;
  default:
    ematch_process_cnstr_all(solver);
  }

  n = solver->round_cnstrs.size;
  assert(n == solver->round_instances.size);
  for(i=0; i<n; i++) {
    ematch_add_quant_cnstr(solver, solver->round_cnstrs.data[i], solver->round_instances.data[i]);
  }

  context_disable_quant(solver->em.ctx);

  learner_reset_round(&solver->learner, false);

#if TRACE_LIGHT
  quant_print_all_cnstr_priority(solver->learner.qtbl, "(end)");
#endif

}


/*****************
 *  FULL SOLVER  *
 ****************/

/*
 * Initialization
 * - core = attached smt_core
 * - gates = gate manager for the core
 * - egraph = attached egraph
 * - ttbl = attached type table
 */
void init_quant_solver(quant_solver_t *solver, smt_core_t *core,
                     gate_manager_t *gates, egraph_t *egraph, type_table_t *ttbl) {

  solver->core = core;
  solver->gate_manager = gates;
  solver->egraph = egraph;
  solver->types = ttbl;

  solver->base_level = 0;
  solver->decision_level = 0;

  init_quant_solver_statistics(&solver->stats);

  solver->prob = NULL;
  init_pattern_table(&solver->ptbl);
  init_quant_table(&solver->qtbl);
  init_ematch(&solver->em);
  init_learner(&solver->learner, &solver->qtbl);
  solver->iter_mode = DEFAULT_ITERATE_MODE;

  init_ivector(&solver->base_literals, 10);
  init_ivector(&solver->base_antecedents, 10);

  init_ivector(&solver->round_cnstrs, 10);
  init_ivector(&solver->round_instances, 10);

  init_ivector(&solver->aux_vector, 10);
  init_ivector(&solver->aux_vector2, 10);
  init_int_hmap(&solver->aux_map, 0);
}


/*
 * Delete the solver
 */
void delete_quant_solver(quant_solver_t *solver) {
  delete_pattern_table(&solver->ptbl);
  delete_quant_table(&solver->qtbl);
  delete_ematch(&solver->em);
  delete_learner(&solver->learner);

  delete_ivector(&solver->base_literals);
  delete_ivector(&solver->base_antecedents);

  delete_ivector(&solver->round_cnstrs);
  delete_ivector(&solver->round_instances);

  delete_ivector(&solver->aux_vector);
  delete_ivector(&solver->aux_vector2);
  delete_int_hmap(&solver->aux_map);
}


/*
 * Reset
 */
void quant_solver_reset(quant_solver_t *solver) {
  solver->base_level = 0;
  solver->decision_level = 0;
  reset_quant_solver_statistics(&solver->stats);

  solver->prob = NULL;
  reset_pattern_table(&solver->ptbl);
  reset_quant_table(&solver->qtbl);
  reset_ematch(&solver->em);
  reset_learner(&solver->learner);

  ivector_reset(&solver->base_literals);
  ivector_reset(&solver->base_antecedents);

  ivector_reset(&solver->round_cnstrs);
  ivector_reset(&solver->round_instances);

  ivector_reset(&solver->aux_vector);
  ivector_reset(&solver->aux_vector2);
  int_hmap_reset(&solver->aux_map);
}


/*
 * Increase the decision level
 */
void quant_solver_increase_decision_level(quant_solver_t *solver) {
  uint32_t k;

  k = solver->decision_level + 1;
  solver->decision_level = k;
  learner_update_decision_reward(&solver->learner);

#if TRACE_LIGHT
  printf("---> QUANTSOLVER:   Increasing decision level to %d\n", k);
  fflush(stdout);
#endif
}


/*
 * Backtrack to back_level:
 */
void quant_solver_backtrack(quant_solver_t *solver, uint32_t back_level) {
  assert(solver->base_level <= back_level && back_level < solver->decision_level);

  learner_update_backtrack_reward(&solver->learner, (solver->decision_level - back_level));
  solver->decision_level = back_level;

#if TRACE_LIGHT
  printf("---> QUANTSOLVER:   Backtracking to level %d\n", back_level);
  fflush(stdout);
#endif

}


/*
 * Push:
 */
void quant_solver_push(quant_solver_t *solver) {
  assert(solver->base_level == solver->decision_level);

  solver->base_level ++;
  quant_solver_increase_decision_level(solver);
  assert(solver->base_level == solver->decision_level);
}


/*
 * Pop:
 */
void quant_solver_pop(quant_solver_t *solver) {
  assert(solver->base_level > 0 && solver->base_level == solver->decision_level);

  solver->base_level --;

  quant_solver_backtrack(solver, solver->base_level);
}


/*
 * Prepare for internalization: do nothing
 */
void quant_solver_start_internalization(quant_solver_t *solver) {
}

/*
 * Start search
 */
void quant_solver_start_search(quant_solver_t *solver) {
#if TRACE_LIGHT
  printf("\n=== START SEARCH ===\n");
  printf("\n\n");
#endif
  ematch_reset_start_stats(solver);
}


/*
 * Propagate: do nothing
 * - all the work is done in final_check
 */
bool quant_solver_propagate(quant_solver_t *solver) {
  bool result;
  uint32_t i, n;
  ivector_t *lits, *ants;
  literal_t l;
  smt_core_t *s;

  result = true;
  lits = &solver->base_literals;
  ants = &solver->base_antecedents;
  s = solver->core;

  n = lits->size;
  assert(ants->size == n);

  // add all delayed base literals (with antecedents)
  if (n != 0) {
#if TRACE
    printf("EMATCH: Propagating %d delayed unit base clauses\n", n);
#endif

    for(i=0; i<n; i++) {
      l = lits->data[i];
#if TRACE
      printf("EMATCH: Propagating literal: ");
      print_literal(stdout, l);
      printf("\n");
#endif

      switch(literal_value(s, l)) {
      case VAL_FALSE:
        record_unit_theory_conflict(s, l);
        result = false;
        break;
      case VAL_TRUE:
        break; // true clause
      case VAL_UNDEF_FALSE:
      case VAL_UNDEF_TRUE:
        implied_literal(s, l, mk_literal_antecedent(ants->data[i]));
        break;
      }
    }

    if (solver->decision_level == solver->base_level) {
      ivector_reset(lits);
      ivector_reset(ants);
    }
  }

  return result;
}



/*
 * FINAL CHECK: deal only with quantifier instantiation.
 *
 */
fcheck_code_t quant_solver_final_check(quant_solver_t *solver) {
  if (solver->stats.num_search == 1) {
#if EM_VERBOSE
    printf("\nEMATCH: initial search\n\n");
#endif
    return FCHECK_SAT;
 }

  if (ematch_reached_round_limit(solver)) {
#if EM_VERBOSE
    printf("\nEMATCH: reached round limit (%d rounds)\n\n", solver->stats.num_rounds_per_search);
#endif
    return FCHECK_SAT;
 }

  if (ematch_reached_search_limit(solver)) {
#if EM_VERBOSE
    printf("\nEMATCH: reached search limit (%d searches)\n\n", solver->stats.num_search);
#endif
    return FCHECK_SAT;
 }

#if EM_VERBOSE
  printf("\n**** QUANTSOLVER: FINAL CHECK ***\n\n");
#endif

#if TRACE
//  print_egraph_terms(stdout, solver->egraph);
////  print_egraph_terms_details(stdout, solver->egraph);
//  printf("\n\n");
//  print_egraph_root_classes(stdout, solver->egraph);
////  print_egraph_root_classes_details(stdout, solver->egraph);
//
//  printf("\n(BEGIN) Intern. mappings:\n");
//  print_context_intern_mapping(stdout, solver->em.ctx);

  printf("\n(BEGIN) Binary clauses:\n");
  print_binary_clauses(stdout, solver->core);

  printf("\n(BEGIN) Problem clauses:\n");
  print_problem_clauses(stdout, solver->core);

  printf("\n(BEGIN) Learnt clauses:\n");
  print_learned_clauses(stdout, solver->core);

  printf("\n(BEGIN) Lemmas:\n");
  print_lemmas(stdout, solver->core);
#endif

//  if (solver->stats.num_rounds_per_search == 8) {
//    assert(0);
//  }

//  ematch_execute_all_patterns(&solver->em);

  ematch_process_all_cnstr(solver);

#if TRACE
//  print_egraph_terms(stdout, solver->egraph);
////  print_egraph_terms_details(stdout, solver->egraph);
//  printf("\n\n");
//  print_egraph_root_classes(stdout, solver->egraph);
////  print_egraph_root_classes_details(stdout, solver->egraph);
//
//  printf("\n(END) Intern. mappings:\n");
//  print_context_intern_mapping(stdout, solver->em.ctx);
//
  printf("\n(END) Binary clauses:\n");
  print_binary_clauses(stdout, solver->core);

  printf("\n(END) Problem clauses:\n");
  print_problem_clauses(stdout, solver->core);

  printf("\n(END) Learnt clauses:\n");
  print_learned_clauses(stdout, solver->core);

  printf("\n(END) Lemmas:\n");
  print_lemmas(stdout, solver->core);
#endif

#if EM_VERBOSE
  printf("S%d:R%d EMATCH: learnt total %d instances (%d new, %d in current search)\n",
      solver->stats.num_search,
      solver->stats.num_rounds_per_search,
      solver->stats.num_instances,
      solver->stats.num_instances_per_round,
      solver->stats.num_instances_per_search);
#endif

  solver->stats.num_rounds_per_search++;

#if EM_VERBOSE
  printf("\n**** QUANTSOLVER: FINAL CHECK DONE ***\n\n");
#endif

  return (solver->stats.num_instances_per_round==0) ? FCHECK_SAT : FCHECK_CONTINUE;
}


/*
 * Clear: nothing to do
 */
void quant_solver_clear(quant_solver_t *solver) {
}



/***************************
 *  INTERFACE DESCRIPTORS  *
 **************************/

/*
 * Control and generic interface for the egraph
 */
static th_ctrl_interface_t fsolver_control = {
  (start_intern_fun_t) quant_solver_start_internalization,
  (start_fun_t) quant_solver_start_search,
  (propagate_fun_t) quant_solver_propagate,
  (final_check_fun_t) quant_solver_final_check,
  (increase_level_fun_t) quant_solver_increase_decision_level,
  (backtrack_fun_t) quant_solver_backtrack,
  (push_fun_t) quant_solver_push,
  (pop_fun_t) quant_solver_pop,
  (reset_fun_t) quant_solver_reset,
  (clear_fun_t) quant_solver_clear,
};

static th_egraph_interface_t fsolver_egraph = {
  NULL, // (assert_eq_fun_t) quant_solver_assert_var_eq,
  NULL, // (assert_diseq_fun_t) quant_solver_assert_var_diseq,
  NULL, // (assert_distinct_fun_t) quant_solver_assert_var_distinct,
  NULL, // (check_diseq_fun_t) quant_solver_check_disequality,
  NULL, // (is_constant_fun_t) quant_solver_var_is_constant,
  NULL, // no need for expand_th_explanation
  NULL, // (reconcile_model_fun_t) quant_solver_reconcile_model,
  NULL, // (prepare_model_fun_t) quant_solver_prepare_model,
  NULL, // (equal_in_model_fun_t) quant_solver_var_equal_in_model,
  NULL, // (gen_inter_lemma_fun_t) quant_solver_gen_interface_lemma, // gen_interface_lemma
  NULL, // (release_model_fun_t) quant_solver_release_model,
  NULL, // build_model_partition,
  NULL, // release_model_partition,
  NULL, // (attach_to_var_fun_t) quant_solver_attach_eterm,
  NULL, // (get_eterm_fun_t) quant_solver_get_eterm_of_var,
  NULL, // (select_eq_polarity_fun_t) quant_solver_select_eq_polarity,
};


/*
 * Quant-theory interface for the egraph
 */
static quant_egraph_interface_t fsolver_quant_egraph = {
  NULL, // (make_quant_var_quant_t) quant_solver_create_var,
};



/*
 * Access to the interface descriptors
 */
th_ctrl_interface_t *quant_solver_ctrl_interface(quant_solver_t *solver) {
  return &fsolver_control;
}

th_egraph_interface_t *quant_solver_egraph_interface(quant_solver_t *solver) {
  return &fsolver_egraph;
}

quant_egraph_interface_t *quant_solver_quant_egraph_interface(quant_solver_t *solver) {
  return &fsolver_quant_egraph;
}

