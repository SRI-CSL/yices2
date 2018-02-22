/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef BV_BDD_H_
#define BV_BDD_H_

#include "mcsat/plugin.h"
#include <cudd.h>

/* Datastructure for the BDD manager (one instance in a run) */
/* So far, it's only the CUDD manager,
   but this is also the structure where we can keep the map
   that records, for each BV variable, its current domain.
 */

typedef struct {

  /** BDD manager */
  DdManager* manager;

} bdd_manager_t;


/* Datastructure for a BV variable together with some BDD information:
   First, its bitsize,
   second, the array of pointers to the BDD nodes representing its bits
   (this will be fixed throughout a run),
   third, its current domain, as one BDD (this will evolve during a run).
*/

typedef struct {

  /* Variable */
  const variable_t* var;

  /* bitsize of the variable */
  uint32_t bitsize;

  /* The array of BDD nodes for the variable's bits, of length bitsize */
  DdNode** bitnodes;
  
  /* The current domain for the variable */
  DdNode* domain;

  /* Constraints that have affected the domain */
  ivector_t constraints;
  
} varWnodes_t;



/* Datastructure for a function from bitvectors to bitvectors:
   each bit of the output is a Boolean function of the input bitvector;
   each bit is therefore represented as a BDD over the bits of the input
*/

typedef struct {

  /* Input variable */
  const varWnodes_t* input;
  
  /* bitsize of the output */
  uint32_t bitsize;
  
  /* The array of BDDs, of length bitsize */
  DdNode** data;
  
} bdds_t;

/* Creating and destructing the BDD manager */
extern void bdd_manager_construct(bdd_manager_t* bm);
extern void bdd_manager_destruct(const bdd_manager_t* bm);

/* Creating and destructing var with nodes */
extern void varWnodes_create(varWnodes_t* vn, uint32_t bitsize, const variable_t* var, const bdd_manager_t* bm);
extern void varWnodes_free(varWnodes_t* vn);
  
/* Creating a function from bitvectors to bitvectors,
   defined nowhere (every output bit is NULL) */
extern void bdds_alloc(bdds_t* bdds, uint32_t bitsize, varWnodes_t* vn);

/* Clearing such a function, setting every output bit to NULL (undefined function) */
extern void bdds_clear(bdds_t* bdds, const bdd_manager_t* bm);

/* Destructing a function from bitvectors to bitvectors
   Requires the function to be cleared */
extern void bdds_free(bdds_t* bdds);

/* Now we program functions from bitvectors to bitvectors */

/* The constant function;
   Assumes that the function bdds is previously cleared */
extern void bdds_cst(bdds_t* bdds, const bvconstant_t* cst, const bdd_manager_t* bm);

/* The identity function.
   Assumes that the function bdds is previously cleared
   Makes a copy of the array representing the variable's bits. */
extern void bdds_id(bdds_t* bdds);

/*
 * Bitwise operations: bdds and a must be of same bitsize.
 * - result is in bv
 */
extern void bdds_complement(bdds_t* bdds, const bdd_manager_t* bm);
extern void bdds_and(bdds_t* bdds, const bdds_t* a, const bdd_manager_t* bm);
extern void bdds_or (bdds_t* bdds, const bdds_t* a, const bdd_manager_t* bm);
extern void bdds_xor(bdds_t* bdds, const bdds_t* a, const bdd_manager_t* bm);

/*
 * Concatenation: bdds[0...n-1] = a[0.. n-1] and bdds[n ... n+m-1] = b[0...m-1]
 */
extern void bdds_concat(bdds_t* bdds, const bdds_t* a, const bdds_t* b);



#endif /* BV_BDD_H_ */
