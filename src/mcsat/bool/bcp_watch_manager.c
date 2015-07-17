/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/bool/bcp_watch_manager.h"

#define BCP_WATCH_MANAGER_INIT_SIZE 10000

static inline
void bcp_watch_manager_ensure_capacity(bcp_watch_manager_t* wlm, uint32_t capacity) {
  if (capacity >= wlm->capacity) {
    // Resize
    wlm->capacity = capacity + (capacity / 2) + 1;
    wlm->memory = safe_realloc(wlm->memory, wlm->capacity * sizeof(bcp_watch_list_element_t));
  }
}

/** Construct the mangager */
void bcp_watch_manager_construct(bcp_watch_manager_t* wlm) {

  // The memory
  wlm->memory = NULL;
  wlm->size = 0;
  wlm->capacity = 0;
  bcp_watch_manager_ensure_capacity(wlm, BCP_WATCH_MANAGER_INIT_SIZE);

  // Free list
  init_ivector(&wlm->free_list, 0);
  // No lists yet
  init_ivector(&wlm->watch_lists, 0);
  // The used slots
  init_ivector(&wlm->variables_list, 0);
}

void bcp_watch_manager_destruct(bcp_watch_manager_t* wlm) {
  safe_free(wlm->memory);

  delete_ivector(&wlm->free_list);
  delete_ivector(&wlm->watch_lists);
  delete_ivector(&wlm->variables_list);
}

void bcp_watch_manager_new_variable_notify(bcp_watch_manager_t* wlm, variable_t var) {
  ivector_push(&wlm->variables_list, var);
}

/**
 * Get the list element from reference.
 */
static inline
bcp_watch_list_element_t* bcp_watch_manager_get_watcher(bcp_watch_manager_t* wlm, bcp_watch_list_element_ref_t ref) {
  assert(ref < wlm->size);
  return wlm->memory + ref;
}


/**
 * Get a reference to a new watch list element.
 */
static inline
bcp_watch_list_element_ref_t bcp_watch_manager_allocate(bcp_watch_manager_t* wlm,
    clause_ref_t cref, bool is_binary, mcsat_literal_t blocker)
{
  bcp_watch_list_element_t* wle;
  bcp_watch_list_element_ref_t wle_ref;

  // Try from free list first
  if (wlm->free_list.size > 0) {
    // Get the element from free list
    wle_ref = ivector_pop2(&wlm->free_list);
    wle = bcp_watch_manager_get_watcher(wlm, wle_ref);
  } else {
    // Allocate new element
    bcp_watch_manager_ensure_capacity(wlm, wlm->size);
    wle_ref = wlm->size ++;
    assert(wlm->size <= wlm->capacity);
    wle = bcp_watch_manager_get_watcher(wlm, wle_ref);
  }

  // Initialize the element
  assert(wle != NULL);
  wle->watcher.cref = cref;
  wle->watcher.blocker = blocker;
  wle->watcher.is_binary = is_binary;
  wle->next = bcp_watch_list_element_ref_null;

  return wle_ref;
}


static inline
void bcp_watch_manager_ensure_list(bcp_watch_manager_t* wlm, mcsat_literal_t l) {
  uint32_t l_index, k;

  l_index = literal_index(l);

  if (l_index >= wlm->watch_lists.size) {
    k = wlm->watch_lists.size;
    resize_ivector(&wlm->watch_lists, l_index + (l_index >> 1) + 1);
    for (; k <= l_index; ++ k) {
      ivector_push(&wlm->watch_lists, bcp_watch_list_element_ref_null);
    }
  }

  assert(l_index < wlm->watch_lists.size);
}


static inline
bcp_watch_list_element_ref_t bcp_watch_manager_get_list_ref(bcp_watch_manager_t* wlm, mcsat_literal_t l) {
  uint32_t l_index;

  l_index = literal_index(l);

  if (l_index < wlm->watch_lists.size) {
    return wlm->watch_lists.data[l_index];
  } else {
    return bcp_watch_list_element_ref_null;
  }
}

static inline
void bcp_watch_manager_set_list_ref(bcp_watch_manager_t* wlm, mcsat_literal_t l, bcp_watch_list_element_ref_t list_ref) {
  bcp_watch_manager_ensure_list(wlm, l);
  wlm->watch_lists.data[literal_index(l)] = list_ref;
}

void bcp_watch_manager_add_to_watch(bcp_watch_manager_t* wlm,
    mcsat_literal_t to_watch, clause_ref_t cref, bool is_binary, mcsat_literal_t blocker) {

  bcp_watch_list_element_t* wle;
  bcp_watch_list_element_ref_t wle_ref;

  // Allocate a new element
  wle_ref = bcp_watch_manager_allocate(wlm, cref, is_binary, blocker);
  wle = bcp_watch_manager_get_watcher(wlm, wle_ref);

  // Insert into the list of the "to watch" literal
  wle->next = bcp_watch_manager_get_list_ref(wlm, to_watch);
  bcp_watch_manager_set_list_ref(wlm, to_watch, wle_ref);
}

void bcp_remove_iterator_construct(bcp_remove_iterator_t* it, bcp_watch_manager_t* wlm, mcsat_literal_t l) {
  it->l = l;
  it->wlm = wlm;
  it->wle = bcp_watch_manager_get_list_ref(wlm, l);
  it->wle_prev = bcp_watch_list_element_ref_null;
}

void bcp_remove_iterator_destruct(bcp_remove_iterator_t* it) {
  // nothing to do
}

bcp_watcher_t* bcp_remove_iterator_get_watcher(const bcp_remove_iterator_t* it) {
  return &bcp_watch_manager_get_watcher(it->wlm, it->wle)->watcher;
}

bool bcp_remove_iterator_done(const bcp_remove_iterator_t* it) {
  return it->wle == bcp_watch_list_element_ref_null;
}

void bcp_remove_iterator_next_and_keep(bcp_remove_iterator_t* it) {
  assert(it->wle != bcp_watch_list_element_ref_null);
  it->wle_prev = it->wle;
  it->wle = bcp_watch_manager_get_watcher(it->wlm, it->wle)->next;
}

void bcp_remove_iterator_next_and_remove(bcp_remove_iterator_t* it) {
  bcp_watch_list_element_t* wle;
  bcp_watch_list_element_ref_t wle_ref;

  assert(it->wle != bcp_watch_list_element_ref_null);

  // The actuall watcher element
  wle_ref = it->wle;
  wle = bcp_watch_manager_get_watcher(it->wlm, wle_ref);

  if (it->wle_prev == bcp_watch_list_element_ref_null) {
    // No prev, remove from watch table
    bcp_watch_manager_set_list_ref(it->wlm, it->l, wle->next);
  } else {
    // Remove from prev
    bcp_watch_manager_get_watcher(it->wlm, it->wle_prev)->next = wle->next;
  }

  // Add to free list
  ivector_push(&it->wlm->free_list, wle_ref);

  // keep the prev, go to next
  it->wle = wle->next;
}

void bcp_watch_manager_sweep(bcp_watch_manager_t* wlm, const gc_info_t* gc_clauses, const gc_info_t* gc_vars) {

  uint32_t i;
  variable_t var;

  bcp_remove_iterator_t it;
  bcp_watcher_t* w;
  clause_ref_t clause_reloc;

  for (i = 0; i < wlm->variables_list.size; ++ i) {
    var = wlm->variables_list.data[i];

    if (gc_info_get_reloc(gc_vars, var) == variable_null) {
      // Remove the lists for negated literal
      bcp_remove_iterator_construct(&it, wlm, literal_construct(var, true));
      while (!bcp_remove_iterator_done(&it)) {
        bcp_remove_iterator_next_and_remove(&it);
      }
      bcp_remove_iterator_destruct(&it);
      // Remove the lists for non negated literal
      bcp_remove_iterator_construct(&it, wlm, literal_construct(var, false));
      while (!bcp_remove_iterator_done(&it)) {
        bcp_remove_iterator_next_and_remove(&it);
      }
      bcp_remove_iterator_destruct(&it);
    } else {
      // Reloc the clause for negated literals
      bcp_remove_iterator_construct(&it, wlm, literal_construct(var, true));
      while (!bcp_remove_iterator_done(&it)) {
        w = bcp_remove_iterator_get_watcher(&it);
        clause_reloc = gc_info_get_reloc(gc_clauses, w->cref);
        if (clause_reloc == clause_ref_null) {
          bcp_remove_iterator_next_and_remove(&it);
        } else {
          w->cref = clause_reloc;
          bcp_remove_iterator_next_and_keep(&it);
        }
      }
      bcp_remove_iterator_destruct(&it);
      // Reloc the clause for negated literals
      bcp_remove_iterator_construct(&it, wlm, literal_construct(var, false));
      while (!bcp_remove_iterator_done(&it)) {
        w = bcp_remove_iterator_get_watcher(&it);
        clause_reloc = gc_info_get_reloc(gc_clauses, w->cref);
        if (clause_reloc == clause_ref_null) {
          bcp_remove_iterator_next_and_remove(&it);
        } else {
          w->cref = clause_reloc;
          bcp_remove_iterator_next_and_keep(&it);
        }
      }
      bcp_remove_iterator_destruct(&it);
    }

  }

  // Collect the variable vector
  gc_info_sweep_ivector(gc_vars, &wlm->variables_list);

}
