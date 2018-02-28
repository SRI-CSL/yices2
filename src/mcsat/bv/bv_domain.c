/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

/* #include "bv_bdd.h" */

#include "mcsat/bv/bv_bdd.h"

#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "mcsat/value.h"

#include "terms/terms.h"
#include "yices.h"

#include <cudd.h>

/* Datastructure for a BV variable and its domain (varies during a run).
*/

typedef struct bv_domain_s {

  /* The domain */
  bdds_t* domain;

} bv_domain_t;


varWnodes_t* bv_domain_getvar(bv_domain_t* bvdom){
  return bv_bdds_getvarWnodes(bvdom->domain);
}

bv_domain_t* bv_domain_init(uint32_t bitsize, variable_t var,
                            DdManager* manager, plugin_context_t* ctx){
  bv_domain_t* bvdom     = safe_malloc(sizeof(bv_domain_t));
  varWnodes_t* varWnodes = varWnodes_create(bitsize, var, manager, ctx);
  bvdom->domain          = bdds_create(1, varWnodes);
  /* Initialising the domain to True, can be changed later. */
  bv_bdds_one(bvdom->domain);
  return bvdom;
}

void bv_domain_free(bv_domain_t* bvdom){
  bdds_clear(bvdom->domain);
  bdds_free(bvdom->domain);
  safe_free(bvdom);
}

void bv_domain_print(bv_domain_t* bvdom){
  bdds_print(bvdom->domain);
}

static
void bv_domain_eval(bdds_t* result, term_t t){
  const varWnodes_t* varWnodes = bv_bdds_getvarWnodes(result);
  plugin_context_t* ctx      = bv_varWnodes_getctx(varWnodes);
  /* variable_db_t* var_db      = ctx->var_db; */
  /* const mcsat_trail_t* trail = ctx->trail; */
  term_table_t* terms        = ctx->terms;

  if (ctx_trace_enabled(ctx, "bv_plugin")) {
    ctx_trace_printf(ctx, "bv_domain_eval(...), evaluating, as a bdd array, unit term ");
    ctx_trace_term(ctx, t);
  }
  term_kind_t t_kind         = term_kind(terms, t);
  /* uint32_t bitsize           = term_bitsize(terms, t); */
  /* composite_term_t* composite_term = composite_term_desc(ctx->terms, t); */
  /* uint32_t arity             = composite_term->arity; */

  switch (t_kind) {
  case BV_ARRAY:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
  case SELECT_TERM:
  case BIT_TERM:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM:
  default:
    break;
  }

  /* For now, we output the BDD [1,...,1] */
  bv_bdds_one(result);

}


bv_domain_t* bv_domain_update(bdds_t* bdds, term_t reason, const mcsat_value_t* v, bv_domain_t* bvdom){

  varWnodes_t* varWnodes = bv_bdds_getvarWnodes(bdds);
  assert(varWnodes == bv_bdds_getvarWnodes(bvdom->domain));
  
  switch (v->type) {
  case VALUE_BV: {
    uint32_t bitsize = v->bv_value.bitsize;
    bdds_t* t_bdds = bdds_create(bitsize, varWnodes);
    bdds_t* v_bdds = bdds_create(bitsize, varWnodes);
    bv_domain_eval(t_bdds, reason);
    bdds_cst(v_bdds, v->bv_value);
    bdds_eq(bdds, t_bdds, v_bdds);
    bdds_clear(t_bdds);
    bdds_free(t_bdds);
    bdds_clear(v_bdds);
    bdds_free(v_bdds);
    break;
  }
  case VALUE_BOOLEAN: {
    bv_domain_eval(bdds, reason);
    if (!(v->b))
      bdds_complement(bdds);
    break;
  }
  default:
    assert(false);
  }

  bdds_t* tmp = bdds_create(1, varWnodes);
  bv_bdds_one(tmp);
  bdds_and(tmp, bdds);
  bdds_and(tmp, bvdom->domain);
  
  /* if (bv_bdds_eq(tmp, bvdom->domain)){  Not sure test is ok */
  if (true){
    bdds_clear(tmp);
    bdds_free(tmp);
    return bvdom;
  }

  bv_domain_t* result = safe_malloc(sizeof(bv_domain_t));
  result->domain      = tmp;
  return result;  
  
}

