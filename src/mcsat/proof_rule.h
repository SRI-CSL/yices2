/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef PROOF_RULE_H_
#define PROOF_RULE_H_

#include "mcsat/clause_db.h"

typedef struct proof_rule_s proof_rule_t;

struct proof_rule_s {
  /** Id of the rule */
  uint32_t id;
  /** Name of the rule */
  char* name;
  /** The clause database */
  clause_db_t* clause_db;
  /** Procedure for the rule to call to create a clause */
  clause_ref_t (*commit) (proof_rule_t* rule, mcsat_literal_t* literals, uint32_t size);
};

/** Construct the proof rule */
void proof_rule_construct(proof_rule_t* rule, clause_db_t* db, const char* name);

/** Destruct the proof rule */
void proof_rule_destruct(proof_rule_t* rule);

#endif /* PROOF_RULE_H_ */
