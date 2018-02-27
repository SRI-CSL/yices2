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



bv_domain_t* bv_domain_update(bdds_t* bdds, term_t reason, const mcsat_value_t* v, bv_domain_t* domain){

  /* TODO. So far the update has no effect */
  return domain;
}

