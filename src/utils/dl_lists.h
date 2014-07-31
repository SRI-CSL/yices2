/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * DOUBLY-LINKED LISTS
 */

#ifndef __DL_LISTS_H
#define __DL_LISTS_H

#include <stdbool.h>

typedef struct dl_list_s dl_list_t;

/*
 * This is intended to be used both as a header structure for the list
 * elements and as the start and end of the list.
 */
struct dl_list_s {
  dl_list_t *next;
  dl_list_t *pre;
};


/*
 * Initialize or reset to the empty list
 */
static inline void clear_list(dl_list_t *l) {
  l->next = l;
  l->pre = l;
}

/*
 * Check emptiness
 */
static inline bool empty_list(dl_list_t *l) {
  assert(l->next != l || l->pre == l);
  return l->next == l;
}

/*
 * Insert element e as successor of l
 */
static inline void list_insert_next(dl_list_t *l, dl_list_t *e) {
  dl_list_t *aux;

  aux = l->next;
  aux->pre = e;
  l->next = e;
  e->next = aux;
  e->pre = l;
}

/*
 * Insert element e as predecessor of l
 */
static inline void list_insert_pre(dl_list_t *l, dl_list_t *e) {
  dl_list_t *aux;

  aux = l->pre;
  aux->next = e;
  l->pre = e;
  e->next = l;
  e->pre = aux;
}


/*
 * Remove element e from its list
 */
static inline void list_remove(dl_list_t *e) {
  dl_list_t *n, *p;

  n = e->next;
  p = e->pre;
  p->next = n;
  n->pre = p;
}


/*
 * Put e back into a list (after call to list_remove)
 */
static inline void list_restore(dl_list_t *e) {
  dl_list_t *n, *p;

  n = e->next;
  p = e->pre;
  p->next = e;
  n->pre = e;
}


#endif /* __DL_LISTS_H */
