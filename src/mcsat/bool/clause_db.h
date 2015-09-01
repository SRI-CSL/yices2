/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef CLAUSE_DB_H_
#define CLAUSE_DB_H_

#include "mcsat/bool/literal.h"

/**
 * A clause is just a sequence of literals. We keep the literals null
 * terminated. So that we can make the clauses smaller while keeping track of
 * the original size.
 */
typedef struct {
  /** Size of the clause (not real size of the vector, see above) */
  uint32_t size;
  /** The literals */
  mcsat_literal_t literals[];
} mcsat_clause_t;

typedef enum {
  /** This clause is part of a variable definition */
  CLAUSE_DEFINITION,
  /** This clause is a learnt lemma */
  CLAUSE_LEMMA
} mcsat_clause_type_t;

typedef struct {

  /** Type of the clause */
  mcsat_clause_type_t type;

  union {
    /** The variable that is defined */
    variable_t var;
    /** The score of the variable */
    float score;
  };

} mcsat_clause_tag_t;

/**
 * A tagged clause is a clause with additional information. For definitional
 * clauses we keep the variable that is being defined, and for the lemma
 * clauses we keep the score of the clause.
 */
typedef struct {

  /** Tag for the clause */
  mcsat_clause_tag_t tag;

  /** The clause itself */
  mcsat_clause_t clause;

} mcsat_tagged_clause_t;

/**
 * Lemma clauses in addition contains a score.
 */
typedef struct {
  /** Score */
  float score;
  /** The clause itself */
  mcsat_clause_t clause;
} mcsat_lemma_clause_t;


/** Null clause */
#define clause_ref_null 0

/** Clause database type */
typedef struct clause_db_s clause_db_t;

/**
 * The clause database.
 */
struct clause_db_s {

  /** The variable database */
  const variable_db_t* var_db;

  /** Minimal clause ref */
  uint32_t min_size;
  /** Size of the database */
  uint32_t size;
  /** Capacity of the database */
  uint32_t capacity;
  /** The data */
  char* memory;

  /** All the clauses */
  ivector_t clauses;
};

/** Create a new clause database */
void clause_db_construct(clause_db_t* db, const variable_db_t* var_db);

/** Destruct and free the clause database */
void clause_db_destruct(clause_db_t* db);

/** Create a new clause given literals */
clause_ref_t clause_db_new_clause(clause_db_t* db, const mcsat_literal_t* literals, uint32_t size, mcsat_clause_tag_t tag);

/** Print the clause to the stream */
void clause_db_print_clause(const clause_db_t* var_db, clause_ref_t C, FILE* out);

/** Get the actual clause */
mcsat_clause_t* clause_db_get_clause(const clause_db_t* db, clause_ref_t C);

/** Get the tagged clause */
mcsat_tagged_clause_t* clause_db_get_tagged_clause(const clause_db_t* db, clause_ref_t C);

/** Mark all the variables in the marked clauses */
void clause_db_gc_mark(const clause_db_t* db, const gc_info_t* gc_clauses, gc_info_t* gc_vars);

/** Sweep the marked clauses, while outputing any variables that were undefined (clausaly) */
void clause_db_gc_sweep(clause_db_t* db, gc_info_t* gc_clauses, int_mset_t* vars_undefined);

/** Get the tag of the clause */
mcsat_clause_tag_t* clause_db_get_tag(const clause_db_t* db, clause_ref_t C);

/** Get the tag of the clause */
mcsat_clause_tag_t* clause_get_tag(const mcsat_clause_t* clause);

/** Simple checks to ensure clause is OK (not complete) */
bool clause_db_is_clause(const clause_db_t* db, clause_ref_t C, bool assert);

/** Simple checks to ensure the clauses in the vector are OK (not complete) */
bool clause_db_is_clause_vector(const clause_db_t* db, const ivector_t* clauses, bool assert);

/** Print the literals to the output */
void literals_print(const mcsat_literal_t* lits, uint32_t size, const variable_db_t* var_db, FILE* out);

/** Print the clause to the output */
void clause_print(const mcsat_clause_t* C, const variable_db_t* var_db, FILE* out);

/** Swap two literals in a clause */
static inline
void clause_swap_literals(mcsat_clause_t* C, uint32_t i, uint32_t j) {
  mcsat_literal_t tmp;
  tmp = C->literals[i];
  C->literals[i] = C->literals[j];
  C->literals[j] = tmp;
}

#endif /* CLAUSE_DB_H_ */
