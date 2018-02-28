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

  /* Variable */
  varWnodes_t* varWnodes;

  /* The domain */
  DdNode* domain;

} bv_domain_t;


const varWnodes_t* bv_domain_getvar(bv_domain_t* domain){
  return domain->varWnodes;
}

bv_domain_t* bv_domain_create(uint32_t bitsize, variable_t var,
                              DdManager* manager, plugin_context_t* ctx){
  bv_domain_t* bvdom = safe_malloc(sizeof(bv_domain_t));
  bvdom->varWnodes   = varWnodes_create(bitsize, var, manager, ctx);
  /* Initialising the domain to True, can be changed later. */
  bvdom->domain      = Cudd_ReadOne(manager);
  Cudd_Ref(bvdom->domain);
  return bvdom;
}

void bv_domain_free(bv_domain_t* bvdom){
  varWnodes_free(bvdom->varWnodes);
  DdManager* manager = bv_varWnodes_manager(bvdom->varWnodes);
  Cudd_RecursiveDeref(manager,bvdom->domain);
  safe_free(bvdom);
}

void bv_domain_print(bv_domain_t* bvdom){
  DdManager* manager = bv_varWnodes_manager(bvdom->varWnodes);
  Cudd_PrintDebug(manager, bvdom->domain, 0, 3);
}


static
void bv_domain_eval(bdds_t* result, term_t t){
  const varWnodes_t* varWnodes = bv_bdds_getvarWnodes(result);
  plugin_context_t* ctx      = bv_varWnodes_getctx(varWnodes);
  /* variable_db_t* var_db      = ctx->var_db; */
  /* const mcsat_trail_t* trail = ctx->trail; */
  term_table_t* terms        = ctx->terms;
  /* term_kind_t t_kind         = term_kind(terms, t); */
  /* /\* uint32_t bitsize           = term_bitsize(terms, t); *\/ */
  /* /\* composite_term_t* composite_term = composite_term_desc(ctx->terms, t); *\/ */
  /* /\* uint32_t arity             = composite_term->arity; *\/ */

  /* switch (t_kind) { */
  /* case BV_ARRAY: */
  /* case BV_DIV: */
  /* case BV_REM: */
  /* case BV_SDIV: */
  /* case BV_SREM: */
  /* case BV_SMOD: */
  /* case BV_SHL: */
  /* case BV_LSHR: */
  /* case BV_ASHR: */
  /* case SELECT_TERM: */
  /* case BIT_TERM: */
  /* case BV_EQ_ATOM: */
  /* case BV_GE_ATOM: */
  /* case BV_SGE_ATOM: */
  /* default: */
  /*   break; */
  /* } */

  uint32_t bitsize = bv_bdds_bitsize(result);
  bvconstant_t b;
  init_bvconstant(&b);
  bvconstant_set_all_zero(&b, bitsize);
  bdds_cst(result, b);
  delete_bvconstant(&b);

}


bv_domain_t* bv_domain_update(bdds_t* bdds, term_t reason, const mcsat_value_t* v, bv_domain_t* domain){

  const varWnodes_t* varWnodes = bv_bdds_getvarWnodes(bdds);
  
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
  
  /* TODO. So far the update has no effect */
  return domain;
}

