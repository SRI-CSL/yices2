/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/bool/clause_db.h"
#include "utils/ptr_vectors.h"
#include "utils/int_array_sort.h"

#include <string.h>

void literals_print(const mcsat_literal_t* lits, uint32_t size, const variable_db_t* var_db, FILE* out) {
  uint32_t i;

  fprintf(out, "[");

  for (i = 0; i < size; ++ i) {
    if (i) {
      fprintf(out, " ");
    }
    if (literal_is_negated(lits[i])) {
      fprintf(out, "~");
    }
    variable_db_print_variable(var_db, literal_get_variable(lits[i]), out);
  }

  fprintf(out, "]");
}

void clause_print(const mcsat_clause_t* C, const variable_db_t* var_db, FILE* out) {
  literals_print(C->literals, C->size, var_db, out);
}

/**
 * Construct the clause given the literals.
 */
static
void clause_construct(mcsat_clause_t* C, const mcsat_literal_t* literals, uint32_t size) {
  uint32_t i;
  C->size = size;
  for (i = 0; i < size; ++ i) {
    C->literals[i] = literals[i];
  }
  C->literals[i] = mcsat_literal_null;
}

static
uint32_t clause_literals_count(mcsat_clause_t* C) {
  mcsat_literal_t* l;
  l = C->literals;
  while (*l != mcsat_literal_null) {
    l ++;
  }
  return l - C->literals;
}


#define INITIAL_CLAUSE_DB_CAPACTIY 10000

/** Align the size */
static inline
uint32_t align(uint32_t size) {
  return (size + 7) & ~((uint32_t)7);
}

void clause_db_construct(clause_db_t* db, const variable_db_t* var_db) {
  db->min_size = align(1);
  db->size = db->min_size;
  db->capacity = INITIAL_CLAUSE_DB_CAPACTIY;
  db->memory = safe_malloc(INITIAL_CLAUSE_DB_CAPACTIY);

  init_ivector(&db->clauses, 0);

  db->var_db = var_db;
}

void clause_db_destruct(clause_db_t* db) {
  delete_ivector(&db->clauses);
  safe_free(db->memory);
}

void clause_db_print_clause(const clause_db_t* db, clause_ref_t ref, FILE* out) {
  const mcsat_clause_t* C = clause_db_get_clause(db, ref);
  clause_print(C, db->var_db, out);
}

mcsat_clause_t* clause_db_get_clause(const clause_db_t* db, clause_ref_t C) {
  return (mcsat_clause_t*) (db->memory + C);
}

mcsat_tagged_clause_t* clause_db_get_tagged_clause(const clause_db_t* db, clause_ref_t C) {
  return (mcsat_tagged_clause_t*) (db->memory + C - offsetof(mcsat_tagged_clause_t, clause));
}

mcsat_clause_tag_t* clause_db_get_tag(const clause_db_t* db, clause_ref_t C) {
  return &((mcsat_tagged_clause_t*) (db->memory + C - offsetof(mcsat_tagged_clause_t, clause)))->tag;
}

mcsat_clause_tag_t* clause_get_tag(const mcsat_clause_t* clause) {
  return &((mcsat_tagged_clause_t*) ((char*) clause - offsetof(mcsat_tagged_clause_t, clause)))->tag;
}

static inline
mcsat_tagged_clause_t* allocate(uint32_t* size, char** mem, uint32_t* mem_size, uint32_t* mem_capacity) {
  char* allocated;
  uint32_t requested;

  // Align the size
  *size = align(*size);

  // Make sure there is enough memory
  requested = *mem_size + *size;
  if (requested > *mem_capacity) {
    while (requested > *mem_capacity) {
      *mem_capacity += (*mem_capacity) >> 1;
    }
    *mem = safe_realloc(*mem, *mem_capacity);
  }

  // Actually allocate
  allocated = *mem + *mem_size;
  *mem_size += *size;

  // Return the clause memory
  return (mcsat_tagged_clause_t*) allocated;
}

static inline
clause_ref_t clause_get_ref(const clause_db_t* db, const mcsat_tagged_clause_t* clause) {
  return (char*)&clause->clause - db->memory;
}

static
bool clause_check(const mcsat_tagged_clause_t* clause, const variable_db_t* var_db, bool assert) {
  const mcsat_literal_t* lit;
  uint32_t i;

  if (clause->tag.type == CLAUSE_DEFINITION) {
    if (!variable_db_is_variable(var_db, clause->tag.var, assert)) {
      assert(!assert);
      return false;
    }
  }

  i = 0;
  lit = clause->clause.literals;
  while (*lit != mcsat_literal_null) {
    if (!variable_db_is_variable(var_db, literal_get_variable(*lit), assert)) {
      assert(!assert);
      return false;
    }
    i ++;
    lit ++;
  }

  return true;
}

static inline
uint32_t clause_size_in_bytes(uint32_t literals_count) {
  return sizeof(mcsat_tagged_clause_t) + sizeof(mcsat_literal_t)*(literals_count + 1);
}

clause_ref_t clause_db_new_clause(clause_db_t* db, const mcsat_literal_t* literals, uint32_t size, mcsat_clause_tag_t tag) {
  mcsat_tagged_clause_t* clause_memory;
  uint32_t clause_size;
  clause_ref_t clause_ref;

  assert(tag.type == CLAUSE_LEMMA || tag.var != variable_null);

  // Allocate the clause (size + 1) for null-termination
  clause_size = clause_size_in_bytes(size);
  clause_memory = allocate(&clause_size, &db->memory, &db->size, &db->capacity);

  // Construct the clause and tag it
  clause_construct(&clause_memory->clause, literals, size);
  clause_memory->tag = tag;

  // Compute the clause reference
  clause_ref = clause_get_ref(db, clause_memory);

  // Remember the clause
  assert(clause_db_is_clause(db, clause_ref, true));
  ivector_push(&db->clauses, clause_ref);

  // Return the reference
  return clause_ref;
}

void clause_db_gc_mark(const clause_db_t* db, const gc_info_t* gc_clauses, gc_info_t* gc_vars) {
  uint32_t i;
  clause_ref_t clause_ref;
  const mcsat_tagged_clause_t* clause;
  const mcsat_literal_t* literal;

  for (i = 0; i < gc_clauses->marked.size; ++ i) {
    clause_ref = gc_clauses->marked.data[i];
    clause = clause_db_get_tagged_clause(db, clause_ref);
    assert(clause_check(clause, db->var_db, true));

    // If the clause is a definition add the variable
    if (clause->tag.type == CLAUSE_DEFINITION) {
      gc_info_mark(gc_vars, clause->tag.var);
      assert(gc_vars->marked.size <= variable_db_size(db->var_db));
    }

    literal = clause->clause.literals;
    while (*literal != mcsat_literal_null) {
      gc_info_mark(gc_vars, literal_get_variable(*literal));
      assert(gc_vars->marked.size <= variable_db_size(db->var_db));
      literal ++;
    }
  }
}

void clause_db_gc_sweep(clause_db_t* db, gc_info_t* gc_clauses, int_mset_t* vars_undefined) {

  uint32_t i, literals_count, clause_size, mem_size_new;
  clause_ref_t clause_ref, clause_ref_new;
  mcsat_tagged_clause_t *clause, *clause_new;

  // Move the clause and update refs
  mem_size_new = db->min_size;
  for (i = 0; i < db->clauses.size; ++ i) {
    // Old clause
    clause_ref = db->clauses.data[i];
    clause = clause_db_get_tagged_clause(db, clause_ref);

    // Check if the clause is to be kept
    if (gc_info_is_marked(gc_clauses, clause_ref)) {
      assert(clause_db_is_clause(db, clause_ref, true));

      // New clause
      literals_count = clause_literals_count(&clause->clause);
      clause_size = clause_size_in_bytes(literals_count);
      clause_new = allocate(&clause_size, &db->memory, &mem_size_new, &db->capacity);
      // Move the clause
      memmove(clause_new, clause, clause_size);
      // Store the new reference
      clause_ref_new = clause_get_ref(db, clause_new);
      gc_info_set_reloc(gc_clauses, clause_ref, clause_ref_new);

      assert(clause_db_is_clause(db, clause_ref_new, true));
      assert(gc_info_get_reloc(gc_clauses, clause_ref) == clause_ref_new);
    } else {
      if (clause->tag.type == CLAUSE_DEFINITION) {
        // Mark the variable as undefined
        int_mset_add(vars_undefined, clause->tag.var);
      }
    }
  }

  // Mark as relocated
  gc_info_set_relocated(gc_clauses);

  // Set the new size
  db->size = mem_size_new;

  // Relocate the list of all clauses
  gc_info_sweep_ivector(gc_clauses, &db->clauses);

  assert(clause_db_is_clause_vector(db, &db->clauses, true));
}

bool clause_db_is_clause(const clause_db_t* db, clause_ref_t C, bool assert) {
  mcsat_tagged_clause_t* clause;

  if (C == clause_ref_null) {
    assert(!assert);
    return false;
  }

  if (C < 0) {
    assert(!assert);
    return false;
  }

  if (C >= db->size) {
    assert(!assert);
    return false;
  }

  clause = clause_db_get_tagged_clause(db, C);

  if (!clause_check(clause, db->var_db, assert)) {
    assert(!assert);
    return false;
  }

  return true;
}

bool clause_db_is_clause_vector(const clause_db_t* db, const ivector_t* clauses, bool assert) {
  uint32_t i;
  for (i = 0; i < clauses->size; ++ i) {
    if (!clause_db_is_clause(db, clauses->data[i], true)) {
      assert(!assert);
      return false;
    }
  }
  return true;
}
