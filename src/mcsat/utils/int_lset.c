/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/utils/int_lset.h"
#include "utils/memalloc.h"

#include <stddef.h>

#define INT_LSET_INIT_SIZE 10000

static inline
void int_lset_ensure_capacity(int_lset_t* lset, uint32_t capacity) {
  if (capacity >= lset->capacity) {
    // Resize
    lset->capacity = capacity + (capacity / 2) + 1;
    lset->memory = safe_realloc(lset->memory, lset->capacity * sizeof(int_lset_element_t));
  }
}

/** Construct the set */
void int_lset_construct(int_lset_t* lset) {

  // The memory
  lset->memory = NULL;
  lset->size = 0;
  lset->capacity = 0;
  int_lset_ensure_capacity(lset, INT_LSET_INIT_SIZE);

  // Free list
  init_ivector(&lset->free_list, 0);
  // No lists yet
  init_ivector(&lset->key_to_list_map, 0);
  // The used slots
  init_ivector(&lset->slot_list, 0);
}

void int_lset_destruct(int_lset_t* lset) {
  safe_free(lset->memory);

  delete_ivector(&lset->free_list);
  delete_ivector(&lset->key_to_list_map);
  delete_ivector(&lset->slot_list);
}

/**
 * Get the list element from reference.
 */
static inline
int_lset_element_t* int_lset_get_element(int_lset_t* lset, int_lset_element_ref_t ref) {
  assert(ref < lset->size);
  return lset->memory + ref;
}

/**
 * Get a reference to a new watch list element.
 */
static inline
int_lset_element_ref_t int_lset_allocate(int_lset_t* lset, int32_t value)
{
  int_lset_element_t* element;
  int_lset_element_ref_t element_ref;

  // Try from free list first
  if (lset->free_list.size > 0) {
    // Get the element from free list
    element_ref = ivector_pop2(&lset->free_list);
    element = int_lset_get_element(lset, element_ref);
  } else {
    // Allocate new element
    int_lset_ensure_capacity(lset, lset->size);
    element_ref = lset->size ++;
    assert(lset->size <= lset->capacity);
    element = int_lset_get_element(lset, element_ref);
  }

  // Initialize the element
  assert(element != NULL);
  element->value = value;

  return element_ref;
}


static inline
void int_lset_ensure_list(int_lset_t* lset, int32_t key) {
  assert(key >= 0);

  uint32_t i;

  if (key >= lset->key_to_list_map.size) {
    i = lset->key_to_list_map.size;
    resize_ivector(&lset->key_to_list_map, key + (key >> 1) + 1);
    for (; i <= key; ++ i) {
      ivector_push(&lset->key_to_list_map, int_lset_element_ref_null_and_never_used);
    }
  }

  assert(key < lset->key_to_list_map.size);
}


static inline
int_lset_element_ref_t int_lset_get_list_ref(const int_lset_t* lset, int32_t key) {
  assert(key >= 0);
  int_lset_element_ref_t ref;

  if (key < lset->key_to_list_map.size) {
    ref = lset->key_to_list_map.data[key];
  } else {
    ref = int_lset_element_ref_null;
  }

  if (ref == int_lset_element_ref_null_and_never_used) {
    ref = int_lset_element_ref_null;
  }

  return ref;
}

static inline
void int_lset_set_list_ref(int_lset_t* lset, int32_t key, int_lset_element_ref_t list_ref) {
  assert(list_ref != int_lset_element_ref_null_and_never_used);

  int_lset_ensure_list(lset, key);
  if (lset->key_to_list_map.data[key] == int_lset_element_ref_null_and_never_used) {
    ivector_push(&lset->slot_list, key);
  }

  lset->key_to_list_map.data[key] = list_ref;
}

void int_lset_add(int_lset_t* lset, int32_t key, int32_t value) {

  int_lset_element_t* element;
  int_lset_element_ref_t element_ref;

  // Allocate a new element
  element_ref = int_lset_allocate(lset, value);
  element = int_lset_get_element(lset, element_ref);

  // Insert into the list of the "to watch" literal
  element->next = int_lset_get_list_ref(lset, key);
  int_lset_set_list_ref(lset, key, element_ref);
}

bool int_lset_has_list(const int_lset_t* lset, int32_t key) {
  return int_lset_get_list_ref(lset, key) != int_lset_element_ref_null;
}

/** Relocate the elements of the lists */
void int_lset_reloc_elements(int_lset_t* lset, const gc_info_t* gc_info) {
  uint32_t i, to_keep;

  int32_t key;
  int32_t *value;
  int_lset_iterator_t it;

  for (i = 0, to_keep = 0; i < lset->slot_list.size; ++ i) {
    key = lset->slot_list.data[i];
    if (int_lset_has_list(lset, key)) {
      int_lset_iterator_construct(&it, lset, key);
      while (!int_lset_iterator_done(&it)) {
        value = int_lset_iterator_get(&it);
        *value = gc_info_get_reloc(gc_info, *value);
        int_lset_iterator_next_and_keep(&it);
      }
      int_lset_iterator_destruct(&it);

      // Keep this slot
      lset->slot_list.data[to_keep ++] = key;
    }
  }

  ivector_shrink(&lset->slot_list, to_keep);
}


void int_lset_iterator_construct(int_lset_iterator_t* it, int_lset_t* lset, int32_t key) {
  it->key = key;
  it->lset = lset;
  it->current = int_lset_get_list_ref(lset, key);
  it->prev = int_lset_element_ref_null;
}

void int_lset_iterator_destruct(int_lset_iterator_t* it) {
  // nothing to do
}

int32_t* int_lset_iterator_get(const int_lset_iterator_t* it) {
  return &int_lset_get_element(it->lset, it->current)->value;
}

bool int_lset_iterator_done(const int_lset_iterator_t* it) {
  return it->current == int_lset_element_ref_null;
}

void int_lset_iterator_next_and_keep(int_lset_iterator_t* it) {
  assert(it->current != int_lset_element_ref_null);
  it->prev = it->current;
  it->current = int_lset_get_element(it->lset, it->current)->next;
}

void int_lset_iterator_next_and_remove(int_lset_iterator_t* it) {
  int_lset_element_t* element;
  int_lset_element_ref_t element_ref;

  assert(it->current != int_lset_element_ref_null);

  // The actually watcher element
  element_ref = it->current;
  element = int_lset_get_element(it->lset, element_ref);

  if (it->prev == int_lset_element_ref_null) {
    // No previous, remove from element table
    int_lset_set_list_ref(it->lset, it->key, element->next);
  } else {
    // Remove from previous
    int_lset_get_element(it->lset, it->prev)->next = element->next;
  }

  // Add to free list
  ivector_push(&it->lset->free_list, element_ref);

  // Keep the previous, go to next
  it->current = element->next;
}

void int_lset_remove(int_lset_t* lset, int32_t key) {
  int_lset_iterator_t it;

  int_lset_iterator_construct(&it, lset, key);
  while (!int_lset_iterator_done(&it)) {
    int_lset_iterator_next_and_remove(&it);
  }
  int_lset_iterator_destruct(&it);
}
