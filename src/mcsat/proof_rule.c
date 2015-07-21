/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/proof_rule.h"

#include <string.h>

extern clause_ref_t clause_db_new_clause(clause_db_t* db, uint32_t rule_id, mcsat_literal_t* literals, uint32_t size);
extern uint32_t clause_db_new_proof_rule(clause_db_t* db);

static clause_ref_t proof_rule_commit(proof_rule_t* rule, mcsat_literal_t* literals, uint32_t size) {
  return clause_db_new_clause(rule->clause_db, rule->id, literals, size);
}

void proof_rule_construct(proof_rule_t* rule, clause_db_t* db, const char* name) {
  rule->id = clause_db_new_proof_rule(db);
  rule->name = strdup(name);
  rule->clause_db = db;
  rule->commit = proof_rule_commit;
}

void proof_rule_destruct(proof_rule_t* rule) {
  free(rule->name);
}
