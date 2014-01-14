/*
 * Process a term t as part of ef-solving:
 * - check whether t is quantifier free
 * - collect the variables of t (treated as universal variables)
 * - collect the uninterpreted constaints of t (treated as existential variables).
 */

#include "ef_analyze.h"


/*
 * Initialize an analyzer structure
 */
void init_ef_analyzer(ef_analyzer_t *ef, term_table_t *terms) {
  ef->terms = terms;
  init_int_queue(&ef->queue, 0);
  init_int_hset(&ef->cache, 128);
}


/*
 * Reset queue and cache
 */
void reset_ef_analyzer(ef_analyzer_t *ef) {
  int_queue_reset(&ef->queue);
  int_hset_reset(&ef->cache);
}


/*
 * Delete
 */
void delete_ef_analyzer(ef_analyzer_t *ef) {
  delete_int_queue(&ef->queue);
  delete_int_hset(&ef->cache);
}


/*
 * Add t to the queue if it's not already visited (i.e., not in the cache)
 * For the purpose of ef analyzer, x and (not x) are the same, so we 
 * always remove the polarity bit of t here.
 */
static void ef_analyzer_push_term(ef_analyzer_t *ef, term_t t) {
  t = unsigned_term(t); // remove polarity bit
  if (int_hset_add(&ef->cache, t)) {
    int_queue_push(&ef->queue, t);
  }
}


/*
 * Explore a composite term: add all its children to the queue
 */
static void ef_analyze_composite(ef_analyzer_t *ef, composite_term_t *d) {
  uint32_t i, n;

  n = d->arity;
  for (i=0; i<n; i++) {
    ef_analyzer_push_term(ef, d->arg[i]);
  }
}


/*
 * Power product
 */
static void ef_analyze_power_product(ef_analyzer_t *ef, pprod_t *p) {
  uint32_t i, n;

  n = p->len;
  for (i=0; i<n; i++) {
    ef_analyzer_push_term(ef, p->prod[i].var);
  }
}


/*
 * Polynomials: skipt the constant part if any
 */
static void ef_analyze_poly(ef_analyzer_t *ef, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) i++;
  while (i < n) {
    ef_analyzer_push_term(ef, p->mono[i].var);
    i++;
  }
}

static void ef_analyze_bvpoly64(ef_analyzer_t *ef, bvpoly64_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) i++;
  while (i < n) {
    ef_analyzer_push_term(ef, p->mono[i].var);
    i++;
  }
}

static void ef_analyze_bvpoly(ef_analyzer_t *ef, bvpoly_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) i++;
  while (i < n) {
    ef_analyzer_push_term(ef, p->mono[i].var);
    i++;
  }
}


/*
 * Process term t:
 * - check whether t is quantifier free
 * - collect its free variables in uvar and its uninterpreted
 *   terms in evar
 */
bool ef_analyze(ef_analyzer_t *ef, term_t t, ivector_t *uvar, ivector_t *evar) {
  term_table_t *terms;
  int_queue_t *queue;

  assert(int_queue_is_empty(&ef->queue) && int_hset_is_empty(&ef->cache));

  terms = ef->terms;
  queue = &ef->queue;

  ef_analyzer_push_term(ef, t);

  while (! int_queue_is_empty(queue)) {
    t = int_queue_pop(queue);
    assert(is_pos_term(t));

    switch (term_kind(terms, t)) {
    case CONSTANT_TERM:
    case ARITH_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
      break;

    case VARIABLE:
      ivector_push(uvar, t);
      break;

    case UNINTERPRETED_TERM:
      ivector_push(evar, t);
      break;

    case ARITH_EQ_ATOM:
    case ARITH_GE_ATOM:
      ef_analyzer_push_term(ef, arith_atom_arg(terms, t));
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
    case APP_TERM:
    case UPDATE_TERM:
    case TUPLE_TERM:
    case EQ_TERM:
    case DISTINCT_TERM:
    case OR_TERM:
    case XOR_TERM:
    case ARITH_BINEQ_ATOM:
    case BV_ARRAY:
    case BV_DIV:
    case BV_REM:
    case BV_SDIV:
    case BV_SREM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR:
    case BV_EQ_ATOM:
    case BV_SGE_ATOM:
      ef_analyze_composite(ef, composite_term_desc(terms, t));
      break;

    case FORALL_TERM:
    case LAMBDA_TERM:
      goto bad_ef_term;

    case SELECT_TERM:
      ef_analyzer_push_term(ef, select_term_arg(terms, t));
      break;

    case BIT_TERM:
      ef_analyzer_push_term(ef, bit_term_arg(terms, t));
      break;

    case POWER_PRODUCT:
      ef_analyze_power_product(ef, pprod_term_desc(terms, t));
      break;

    case ARITH_POLY:
      ef_analyze_poly(ef, poly_term_desc(terms, t));
      break;

    case BV64_POLY:
      ef_analyze_bvpoly64(ef, bvpoly64_term_desc(terms, t));
      break;

    case BV_POLY:
      ef_analyze_bvpoly(ef, bvpoly_term_desc(terms, t));
      break;

    default:
      assert(false);
      break;
    }
  }

  int_hset_reset(&ef->cache);
  return true;

 bad_ef_term:
  int_queue_reset(&ef->queue);
  int_hset_reset(&ef->cache);
  return false;
}
