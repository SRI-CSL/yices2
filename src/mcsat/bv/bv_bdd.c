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

#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "mcsat/value.h"

#include "terms/terms.h"
#include "yices.h"

#include <cudd.h>

/* Datastructure for a BV variable together with some BDD information:
   First, its bitsize,
   second, the array of pointers to the BDD nodes representing its bits
   (this will be fixed throughout a run).
*/

typedef struct varWnodes_s {

  /* Variable */
  const variable_t* var;

  /* bitsize of the variable */
  uint32_t bitsize;

  /* The array of BDD nodes for the variable's bits, of length bitsize */
  DdNode** bitnodes;

} varWnodes_t;


/* Datastructure for a function from bitvectors to bitvectors:
   each bit of the output is a Boolean function of the input bitvector;
   each bit is therefore represented as a BDD over the bits of the input
*/

typedef struct bdds_s {

  /* Input variable */
  const varWnodes_t* input;
  
  /* bitsize of the output */
  uint32_t bitsize;
  
  /* The array of BDDs, of length bitsize */
  DdNode** data;
  
} bdds_t;



/* Must be called only once during a run for a given variable */

varWnodes_t* varWnodes_create(uint32_t bitsize, const variable_t* var, DdManager* manager){

  varWnodes_t* vn = safe_malloc(sizeof(varWnodes_t));
  vn->var         = var;
  vn->bitsize     = bitsize;

  /* /\* Initialising the domain to True, can be changed later. *\/ */
  /* vn->domain   = Cudd_ReadOne(manager); */
  /* Cudd_Ref(vn->domain); */

  /* /\* The set of constraints that have restricted the domain must be initialised to the empty set *\/   */
  /* init_ivector(&vn->constraints, 42); */

  /* Creating the BDD nodes corresponding to the variable's bits.
     These will never change. */
  vn->bitnodes  = (DdNode**) safe_malloc(bitsize * sizeof(DdNode*));
  DdNode** data = vn->bitnodes;
  
  for(uint32_t i = 0; i < bitsize; i++){
    data[i] = Cudd_bddNewVar(manager);
  }
  return vn;
}

void varWnodes_free(varWnodes_t* vn){
  safe_free(vn->bitnodes);
  safe_free(vn);
}


bdds_t* bdds_create(uint32_t bitsize, varWnodes_t* vn){
  bdds_t* bdds  = safe_malloc(sizeof(bdds_t));
  bdds->bitsize = bitsize;
  bdds->input   = vn;
  bdds->data    = (DdNode**) safe_malloc(bitsize * sizeof(DdNode*));
  return bdds;
}

void bdds_free(bdds_t* bdds){
  assert(bdds->data[0] == NULL);
  safe_free(bdds->data);
  safe_free(bdds);
}


void bdds_clear(bdds_t* bdds, DdManager* manager){
  uint32_t bitsize   = bdds->bitsize;
  DdNode** data      = bdds->data;
  for(uint32_t i = 0; i < bitsize; i++){
    Cudd_RecursiveDeref(manager,data[i]);
    data[i] = NULL;
  }
}

void bdds_cst(bdds_t* bdds, const bvconstant_t* cst, DdManager* manager){

  assert(bdds->bitsize == cst->bitsize);
  uint32_t bitsize   = bdds->bitsize;
  DdNode** data      = bdds->data;
  
  bool b;
  
  for(uint32_t i = 0; i < bitsize; i++){
    assert(data[i] == NULL);
    b = bvconst_tst_bit(cst->data, i);
    data[i] = b ? Cudd_ReadOne(manager) : Cudd_ReadLogicZero(manager);
    Cudd_Ref(data[i]);
  }
}

void bdds_id(bdds_t* bdds){

  assert(bdds->bitsize == bdds->input->bitsize);
  uint32_t bitsize   = bdds->bitsize;
  DdNode** data      = bdds->data;
  DdNode** nodes     = bdds->input->bitnodes;  
  
  for(uint32_t i = 0; i < bitsize; i++){
    assert(data[i] == NULL);
    data[i] = nodes[i];
  }
}

void bdds_complement(bdds_t* bdds, DdManager* manager){

  uint32_t bitsize   = bdds->bitsize;
  DdNode** data      = bdds->data;
  DdNode* previous;
  
  for(uint32_t i = 0; i < bitsize; i++){
    previous = data[i];    
    data[i] = Cudd_Not(data[i]);
    assert(data[i] != previous);
  }
}

void bdds_and(bdds_t* bdds, const bdds_t* a, DdManager* manager){

  assert(bdds->bitsize == a->bitsize);
  uint32_t bitsize   = bdds->bitsize;
  DdNode** data1     = bdds->data;
  DdNode** data2     = a->data;
  DdNode* previous;
  
  for(uint32_t i = 0; i < bitsize; i++){
    previous = data1[i];
    data1[i] = Cudd_bddAnd(manager,data2[i],previous);
    Cudd_Ref(data1[i]);
    Cudd_RecursiveDeref(manager,previous);
  }
}

void bdds_or(bdds_t* bdds, const bdds_t* a, DdManager* manager){

  assert(bdds->bitsize == a->bitsize);
  uint32_t bitsize   = bdds->bitsize;
  DdNode** data1     = bdds->data;
  DdNode** data2     = a->data;
  DdNode* previous;
  
  for(uint32_t i = 0; i < bitsize; i++){
    previous = data1[i];
    data1[i] = Cudd_bddOr(manager,data2[i],previous);
    Cudd_Ref(data1[i]);
    Cudd_RecursiveDeref(manager,previous);
  }
}

void bdds_xor(bdds_t* bdds, const bdds_t* a, DdManager* manager){

  assert(bdds->bitsize == a->bitsize);
  uint32_t bitsize   = bdds->bitsize;
  DdNode** data1     = bdds->data;
  DdNode** data2     = a->data;
  DdNode* previous;
  
  for(uint32_t i = 0; i < bitsize; i++){
    previous = data1[i];
    data1[i] = Cudd_bddXor(manager,data2[i],previous);
    Cudd_Ref(data1[i]);
    Cudd_RecursiveDeref(manager,previous);
  }
}

void bdds_concat(bdds_t* bdds, const bdds_t* a, const bdds_t* b){
  uint32_t bitsize1  = a->bitsize;
  uint32_t bitsize2  = b->bitsize;
  DdNode** data1     = a->data;
  DdNode** data2     = b->data;
  DdNode** data      = bdds->data;

  assert(bdds->bitsize == (bitsize1 + bitsize2));
  uint32_t i;
  for(i=0; i < bitsize1; i++) {
    assert(data[i] == NULL);
    data[i] = data1[i];
  }
  for(i=0; i < bitsize2; i++) {
    assert(data[i] == NULL);
    data[i+bitsize1] = data2[i];
  }
}
