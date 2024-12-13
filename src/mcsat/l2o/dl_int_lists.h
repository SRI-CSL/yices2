/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * DOUBLY-LINKED LISTS where each nodes contains a int_32
 */

#ifndef __DL_LISTS_H
#define __DL_LISTS_H

#include <stdbool.h>

typedef struct dl_int_list_s dl_int_list_t;

/*
 * This is intended to be used both as a header structure for the list
 * elements and as the start and end of the list.
 */
struct dl_int_list_s {
  dl_int_list_t *next;
  dl_int_list_t *pre;
  int32_t elem;
};


/*
 * Initialize or reset to the empty list
 */
static inline void clear_list(dl_int_list_t *l) {
  l->next = l;
  l->pre = l;
}

/*
 * Check emptiness
 */
static inline bool empty_list(dl_int_list_t *l) {
  assert(l->next != l || l->pre == l);
  return l->next == l;
}

/*
 * Insert element e as successor of l
 */
static inline void list_insert_next(dl_int_list_t *l, dl_int_list_t *e) {
  dl_int_list_t *aux;

  aux = l->next;
  aux->pre = e;
  l->next = e;
  e->next = aux;
  e->pre = l;
}

/*
 * Insert element e as predecessor of l
 */
static inline void list_insert_pre(dl_int_list_t *l, dl_int_list_t *e) {
  dl_int_list_t *aux;

  aux = l->pre;
  aux->next = e;
  l->pre = e;
  e->next = l;
  e->pre = aux;
}


/*
 * Remove element e from its list
 */
static inline void list_remove(dl_int_list_t *e) {
  dl_int_list_t *n, *p;

  n = e->next;
  p = e->pre;
  p->next = n;
  n->pre = p;
}


/*
 * Put e back into a list (after call to list_remove)
 */
static inline void list_restore(dl_int_list_t *e) {
  dl_int_list_t *n, *p;

  n = e->next;
  p = e->pre;
  p->next = e;
  n->pre = e;
}


#endif /* __DL_LISTS_H */
