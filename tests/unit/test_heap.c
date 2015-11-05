/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdint.h>
#include <stdio.h>
#include <float.h>
#include <inttypes.h>

#include "solvers/cdcl/smt_core.h"
#include "utils/assert_utils.h"
#include "utils/memalloc.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

#endif

/*
 * Global heap for testing
 */
static var_heap_t heap;
static uint32_t nvars;


/*
 * Initialize heap for n variables
 * - heap is initially empty: heap_last = 0
 * - heap[0] = -1 is a marker, with activity[-1] higher
 *   than any variable activity.
 * - activity increment and threshold are set to their
 *   default initial value.
 */
static void init_heap(var_heap_t *heap, uint32_t n) {
  uint32_t i;
  double *tmp;

  heap->size = n;
  tmp = (double *) safe_malloc((n+1) * sizeof(double));
  heap->activity = tmp + 1;
  heap->heap_index = (int32_t *) safe_malloc(n * sizeof(int32_t));
  heap->heap = (bvar_t *) safe_malloc((n+1) * sizeof(bvar_t));

  for (i=0; i<n; i++) {
    heap->heap_index[i] = -1;
    heap->activity[i] = 0.0;
  }

  heap->activity[-1] = DBL_MAX;
  heap->heap[0] = -1;
  heap->heap_last = 0;

  heap->act_increment = INIT_VAR_ACTIVITY_INCREMENT;
  heap->inv_act_decay = 1/VAR_DECAY_FACTOR;
}

/*
 * Extend the heap for n variables
 */
static void extend_heap(var_heap_t *heap, uint32_t n) {
  uint32_t old_size, i;
  double *tmp;

  old_size = heap->size;
  assert(old_size < n);
  heap->size = n;
  tmp = heap->activity - 1;
  tmp = (double *) safe_realloc(tmp, (n+1) * sizeof(double));
  heap->activity = tmp + 1;
  heap->heap_index = (int32_t *) safe_realloc(heap->heap_index, n * sizeof(int32_t));
  heap->heap = (int32_t *) safe_realloc(heap->heap, (n+1) * sizeof(int32_t));

  for (i=old_size; i<n; i++) {
    heap->heap_index[i] = -1;
    heap->activity[i] = 0.0;
  }
}

/*
 * Free the heap
 */
static void delete_heap(var_heap_t *heap) {
  safe_free(heap->activity - 1);
  safe_free(heap->heap_index);
  safe_free(heap->heap);
}


/*
 * Reset: remove all variables from the heap and set their activities to 0
 */
static void reset_heap(var_heap_t *heap) {
  uint32_t i, n;

  n = heap->size;
  for (i=0; i<n; i++) {
    heap->heap_index[i] = -1;
    heap->activity[i] = 0.0;
  }
  heap->heap_last = 0;
}

/*
 * Move x up in the heap.
 * i = current position of x in the heap (or heap_last if x is being inserted)
 */
static void update_up(var_heap_t *heap, bvar_t x, uint32_t i) {
  double ax, *act;
  int32_t *index;
  bvar_t *h, y;
  uint32_t j;

  h = heap->heap;
  index = heap->heap_index;
  act = heap->activity;

  ax = act[x];

  j = i >> 1;    // parent of i
  y = h[j];      // variable at position j in the heap

  // The loop terminates since act[h[0]] = DBL_MAX
  while (act[y] < ax) {
    // move y down, into position i
    h[i] = y;
    index[y] = i;

    // move i and j up
    i = j;
    j >>= 1;
    y = h[j];
  }

  // i is the new position for variable x
  h[i] = x;
  index[x] = i;
}


/*
 * Remove element at index i in the heap.
 * Replace it by the current last element.
 */
static void update_down(var_heap_t *heap, uint32_t i) {
  double ax, *act;
  int32_t* index;
  bvar_t *h, x, y;
  uint32_t j, last;

  h = heap->heap;
  index = heap->heap_index;
  act = heap->activity;
  last = heap->heap_last;
  heap->heap_last = last - 1;

  assert(i <= last && act[h[i]] >= act[h[last]]);

  if (last == i) return;  // last element was removed

  ax = act[h[last]]; // activity of last heap element.

  j = 2 * i;      // left child of i

  while (j + 1 < last) {
    // find child of i with highest activity.
    x = h[j];
    y = h[j+1];
    if (act[y] > act[x]) {
      j++;
      x = y;
    }

    // x = child of node i of highest activity
    // j = position of x in the heap (j = 2i or j = 2i+1)
    if (ax >= act[x]) {
      // We're done: store last element in position i
      y = h[last];
      h[i] = y;
      index[y] = i;
      return;
    }

    // Otherwise, move x up, into heap[i]
    h[i] = x;
    index[x] = i;

    // go down one step.
    i = j;
    j <<= 1;
  }

  // Final steps: j + 1 >= last:
  // x's position is either i or j.
  y = h[last];
  if (j < last) {
    x = h[j];
    if (ax >= act[x]) {
      h[i] = y;
      index[y] = i;
    } else {
      h[i] = x;
      index[x] = i;
      h[j] = y;
      index[y] = j;
    }
  } else {
    h[i] = y;
    index[y] = i;
  }

}


/*
 * Insert x into the heap, using its current activity.
 * No effect if x is already in the heap.
 * - x must be between 0 and nvars - 1
 */
static inline void heap_insert(var_heap_t *heap, bvar_t x) {
  if (heap->heap_index[x] < 0) {
    // x not in the heap
    heap->heap_last ++;
    update_up(heap, x, heap->heap_last);
  }
}

/*
 * Remove x from the heap
 */
static void heap_remove(var_heap_t *heap, bvar_t x) {
  int32_t i, j;
  bvar_t y;

  i = heap->heap_index[x];
  if (i < 0) return; // x is not in the heap

  heap->heap_index[x] = -1;

  j = heap->heap_last;
  y = heap->heap[j]; // last variable

  if (heap->activity[x] >= heap->activity[y]) {
    update_down(heap, i);
  } else {
    // replace x by y and update
    heap->heap[i] = y;
    heap->heap_last --;
    update_up(heap, y, i);
  }
}


/*
 * Get and remove top element
 * - returns null_var (i.e., -1) if the heap is empty.
 */
static inline bvar_t heap_get_top(var_heap_t *heap) {
  bvar_t top;

  if (heap->heap_last == 0) {
    return null_bvar;
  }

  // remove top element
  top = heap->heap[1];
  heap->heap_index[top] = -1;

  // repair the heap
  update_down(heap, 1);

  return top;
}

/*
 * Rescale variable activities: divide by VAR_ACTIVITY_THRESHOLD
 * \param heap = pointer to a heap structure
 * \param n = number of variables
 */
static void rescale_var_activities(var_heap_t *heap, uint32_t n) {
  uint32_t i;
  double *act;

  printf("+");
  fflush(stdout);

  act = heap->activity;
  for (i=0; i<n; i++) {
    act[i] *= INV_VAR_ACTIVITY_THRESHOLD;
  }
  heap->act_increment *= INV_VAR_ACTIVITY_THRESHOLD;
}

/*
 * Increase activity of variable x
 */
static void incr_bvar_activity(var_heap_t *heap, bvar_t x) {
  int32_t i;

  if ((heap->activity[x] += heap->act_increment) > VAR_ACTIVITY_THRESHOLD) {
    rescale_var_activities(heap, nvars);
  }

  // move x up if it's in the heap
  i = heap->heap_index[x];
  if (i >= 0) {
    update_up(heap, x, i);
  }
}



/*
 * Check consistency
 */
static void check_heap(var_heap_t *heap, uint32_t nvars) {
  int32_t i;
  double *act;
  bvar_t x, y;

  act = heap->activity;
  for (i=1; i<=heap->heap_last; i++) {
    x = heap->heap[i];
    assert(heap->heap_index[x] == i);

    y = heap->heap[i/2];
    assert_true(act[x] <= act[y]); // cf. assert_utils.h
  }

  y = nvars;
  for (x=0; x<y; x++) {
    i = heap->heap_index[x];
    if (i >= 0) {
      assert(heap->heap[i] == x);
    }
  }
}

static void print_heap(var_heap_t *heap, char *msg) {
  int32_t i;
  bvar_t x;

  printf("%s\n", msg);
  for (i=1; i<=heap->heap_last; i++) {
    x = heap->heap[i];
    printf("Heap[%2"PRId32"]: var: %3"PRId32", act: %f\n", i, x, heap->activity[x]);
  }
  printf("\n");
}

int main(void) {
  bvar_t x;
  uint32_t i;

  init_heap(&heap, 20);
  nvars = 20;
  check_heap(&heap, nvars);
  print_heap(&heap, "Empty heap");

  for (x=0; x<20; x++) {
    heap_insert(&heap, x);
    check_heap(&heap, nvars);
  }
  print_heap(&heap, "Initial heap");

  for (i=0; i<100; i++) {
    x = random() % 20;
    incr_bvar_activity(&heap, x);
    check_heap(&heap, nvars);
    if (random() % 10 <= 3) {
      heap.act_increment *= heap.inv_act_decay;
    }
  }
  print_heap(&heap, "Heap 1");

  for (i=0; i<10; i++) {
    x = heap_get_top(&heap);
    check_heap(&heap, nvars);
  }
  print_heap(&heap, "Heap 2");

  for (i=0; i<100; i++) {
    x = random() % 20;
    incr_bvar_activity(&heap, x);
    check_heap(&heap, nvars);
    if (random() % 10 <= 3) {
      heap.act_increment *= heap.inv_act_decay;
    }
  }
  print_heap(&heap, "Heap 3");

  for (i=0; i<100; i++) {
    x = random() % 20;
    heap_insert(&heap, x);
    check_heap(&heap, nvars);
  }
  print_heap(&heap, "Heap 4");

  for (i=0; i<100; i++) {
    x = random() % 20;
    heap_remove(&heap, x);
    check_heap(&heap, nvars);
  }
  print_heap(&heap, "Heap 5");

  for (i=0; i<100; i++) {
    x = random() % 20;
    incr_bvar_activity(&heap, x);
    check_heap(&heap, nvars);
    if (random() % 10 <= 3) {
      heap.act_increment *= heap.inv_act_decay;
    }
  }
  print_heap(&heap, "Heap 6");

  for (i=0; i<100; i++) {
    x = random() % 20;
    heap_insert(&heap, x);
    check_heap(&heap, nvars);
  }
  print_heap(&heap, "Heap 7");

  extend_heap(&heap, 1000);
  nvars = 1000;

 repeat:
  for (x=20; x<1000; x++) {
    heap_insert(&heap, x);
    check_heap(&heap, nvars);
  }

  for (i=0; i<500; i++) {
    x = random() % 1000;
    incr_bvar_activity(&heap, x);
    check_heap(&heap, nvars);
    if (random() % 10 <= 3) {
      heap.act_increment *= heap.inv_act_decay;
    }
  }

  for (i=0; i<100; i++) {
    x = heap_get_top(&heap);
    check_heap(&heap, nvars);
  }

  for (i=0; i<500; i++) {
    x = random() % 1000;
    incr_bvar_activity(&heap, x);
    check_heap(&heap, nvars);
    if (random() % 10 <= 3) {
      heap.act_increment *= heap.inv_act_decay;
    }
  }

  for (i=0; i<300; i++) {
    x = random() % 1000;
    heap_insert(&heap, x);
    check_heap(&heap, nvars);
  }

  for (i=0; i<500; i++) {
    x = random() % 1000;
    heap_remove(&heap, x);
    check_heap(&heap, nvars);
  }

  for (i=0; i<100; i++) {
    x = random() % 1000;
    incr_bvar_activity(&heap, x);
    check_heap(&heap, nvars);
    if (random() % 10 <= 3) {
      heap.act_increment *= heap.inv_act_decay;
    }
  }

  for (i=0; i<500; i++) {
    x = random() % 1000;
    heap_insert(&heap, x);
    check_heap(&heap, nvars);
  }


  x = random() % 2000;
  if (x >= 1) {
    printf(".");
    fflush(stdout);
    reset_heap(&heap);
    goto repeat;
  }

  printf("\n");
  delete_heap(&heap);

  return 0;
}
