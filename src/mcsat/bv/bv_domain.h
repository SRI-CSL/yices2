/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef BV_DOMAIN_H_
#define BV_DOMAIN_H_

#include "mcsat/plugin.h"
#include "mcsat/bv/bv_bdd.h"
#include <cudd.h>

/* Datastructure for a BV variable and its domain (varies during a run).
*/

typedef struct bv_domain_s bv_domain_t;

/* Creating and destructing var with nodes */
extern bv_domain_t* bv_domain_init(uint32_t bitsize, variable_t var,
                                   DdManager* manager, plugin_context_t* ctx);
extern void         bv_domain_free(bv_domain_t* bvdom);
extern void         bv_domain_print(bv_domain_t* bvdom);

extern varWnodes_t* bv_domain_getvar(bv_domain_t* bvdom);

/*
 * Updating a domain,
 - domain is the domain to be updated
 - reason and v are respectively the term and its assigned value that trigger the domain update
 reason is supposed to be unit in the variable whose domain we consider
 The returned value is a pointer to the new domain: *same pointer as input if domain is unchanged*
 At address bdds, we write the encoding, as a bdds_t, of the new constraint (reason <- v)
 so the output pointer is the conjunction of the old domain with bdds.
 */

extern bv_domain_t* bv_domain_update(bdds_t* bdds, term_t reason, const mcsat_value_t* v, bv_domain_t* domain);

#endif /* BV_BDD_H_ */


