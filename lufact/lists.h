/***********************************************
 *   LISTS AND PERMUTATIONS: INLINE FUNCTIONS  *
 *   TO SCAN LISTS                             *
 **********************************************/

#ifndef __LISTS_H
#define __LISTS_H

#include "matrix_types.h"


/**
 * Check whether list is empty or not
 */
static inline int is_list_empty(list_t *list) {
  return list->data[list->list_id].next < 0;
}

static inline int is_list_nonempty(list_t *list) {
  return list->data[list->list_id].next >= 0;
}



/**
 * Get the first/last element of list.
 * - returns a negative number if the list is empty
 */
static inline int first_of_list(list_t *list) {
  return list->data[list->list_id].next;
}

static inline int last_of_list(list_t *list) {
  return list->data[list->list_id].pre;
}


/**
 * Successor and predecessor of i in list
 */
static inline int next_in_list(list_t *list, int i) {
  return list->data[i].next;
}

static inline int previous_in_list(list_t *list, int i) {
  return list->data[i].pre;
}


#endif
