/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef BCP_WATCH_MANAGER_H_
#define BCP_WATCH_MANAGER_H_

#include "mcsat/bool/literal.h"
#include "mcsat/bool/clause_db.h"
#include "utils/int_vectors.h"

typedef struct {
  /** Clause being watched */
  clause_ref_t cref;
  /** Is this a binary clause */
  bool is_binary;
  /** Blocker literal (one of clause literals that we check for being true) */
  mcsat_literal_t blocker;
} bcp_watcher_t;

/** Reference for the watcher */
typedef int32_t bcp_watch_list_element_ref_t;

#define bcp_watch_list_element_ref_null (-1)

typedef struct {
  /** The watcher element */
  bcp_watcher_t watcher;
  /** The next one */
  bcp_watch_list_element_ref_t next;
} bcp_watch_list_element_t;

/**
 * Map from each literal to a list of clauses where we're watching this
 * literal.
 */
typedef struct {

  /** Memory for bcp watchers */
  bcp_watch_list_element_t* memory;

  /** Size of the used cells */
  uint32_t size;

  /** Capacity of the memory */
  uint32_t capacity;

  /** Free list */
  ivector_t free_list;

  /** Map from literals to watchlists */
  ivector_t watch_lists;

  /** List of used variable slots */
  ivector_t variables_list;

} bcp_watch_manager_t;

/** Construct a watch-list manager */
void bcp_watch_manager_construct(bcp_watch_manager_t* wlm);

/** Destruct the watch-list manager */
void bcp_watch_manager_destruct(bcp_watch_manager_t* wlm);

/** Notify of a new variable */
void bcp_watch_manager_new_variable_notify(bcp_watch_manager_t* wlm, variable_t var);

/**
 * Add the given literal
 *
 * variable list to the watch-list of the given watcher variable. */
void bcp_watch_manager_add_to_watch(bcp_watch_manager_t* wlm,
    mcsat_literal_t to_watch, clause_ref_t clause_ref, bool is_binary, mcsat_literal_t blocker);

/** Sweep the clauses given the gc information */
void bcp_watch_manager_sweep(bcp_watch_manager_t* wlm, const gc_info_t* gc_clauses, const gc_info_t* gc_vars);

typedef struct {

  /** The trigger literal */
  mcsat_literal_t l;

  /** The watch-list manager */
  bcp_watch_manager_t* wlm;

  /** The current and previous element */
  bcp_watch_list_element_ref_t wle, wle_prev;

} bcp_remove_iterator_t;

/** Constructs a remove iterator for the given watcher. */
void bcp_remove_iterator_construct(bcp_remove_iterator_t* it, bcp_watch_manager_t* wlm, mcsat_literal_t l);

/** Destruct a remove iterator for the given watcher and removes any elements marked to remove */
void bcp_remove_iterator_destruct(bcp_remove_iterator_t* it);

/** Returns the current watcher */
bcp_watcher_t* bcp_remove_iterator_get_watcher(const bcp_remove_iterator_t* it);

/** Returns true if the iterator is finished */
bool bcp_remove_iterator_done(const bcp_remove_iterator_t* it);

/** Move the iterator to the next list and keep the current list */
void bcp_remove_iterator_next_and_keep(bcp_remove_iterator_t* it);

/** Move the iterator to the next list and remove the current lits */
void bcp_remove_iterator_next_and_remove(bcp_remove_iterator_t* it);


#endif /* BCP_WATCH_MANAGER_H_ */
