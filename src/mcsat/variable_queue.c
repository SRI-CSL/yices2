/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/variable_queue.h"

#include "utils/dprng.h"

#include <float.h>

#define VAR_DECAY_FACTOR              (0.95)
#define VAR_ACTIVITY_THRESHOLD        (1e100)
#define INV_VAR_ACTIVITY_THRESHOLD    (1e-100)
#define INIT_VAR_ACTIVITY_INCREMENT   (1.0)

#define VAR_QUEUE_INITIAL_SIZE        (100)

void var_queue_construct(var_queue_t *queue) {
  uint32_t i;
  double *tmp;

  tmp = (double *) safe_malloc((VAR_QUEUE_INITIAL_SIZE+2) * sizeof(double));
  queue->activity = tmp + 2;
  queue->heap_index = (int32_t *) safe_malloc(VAR_QUEUE_INITIAL_SIZE * sizeof(int32_t));
  queue->heap = (variable_t *) safe_malloc((VAR_QUEUE_INITIAL_SIZE+1) * sizeof(variable_t));

  for (i=0; i<VAR_QUEUE_INITIAL_SIZE; i++) {
    queue->heap_index[i] = -1;
    queue->activity[i] = 0.0;
  }

  queue->activity[-2] = -1.0;
  queue->activity[-1] = DBL_MAX;
  queue->heap[0] = -1;

  queue->heap_last = 0;
  queue->size = VAR_QUEUE_INITIAL_SIZE;
  queue->vmax = 0;

  queue->act_increment = INIT_VAR_ACTIVITY_INCREMENT;
  queue->inv_act_decay = 1/VAR_DECAY_FACTOR;
}

void var_queue_extend(var_queue_t *queue, uint32_t n) {
  uint32_t old_size, i;
  double *tmp;

  old_size = queue->size;
  assert(old_size < n);
  tmp = queue->activity - 2;
  tmp = (double *) safe_realloc(tmp, (n+2) * sizeof(double));
  queue->activity = tmp + 2;
  queue->heap_index = (int32_t *) safe_realloc(queue->heap_index, n * sizeof(int32_t));
  queue->heap = (int32_t *) safe_realloc(queue->heap, (n+1) * sizeof(int32_t));
  queue->size = n;

  for (i=old_size; i<n; i++) {
    queue->heap_index[i] = -1;
    queue->activity[i] = 0.0;
  }
}

void var_queue_destruct(var_queue_t *queue) {
  safe_free(queue->activity - 2);
  safe_free(queue->heap_index);
  safe_free(queue->heap);
}

static
void var_queue_update_up(var_queue_t *queue, variable_t x, uint32_t i) {
  double ax, *act;
  int32_t *index;
  variable_t *h, y;
  uint32_t j;

  h = queue->heap;
  index = queue->heap_index;
  act = queue->activity;

  ax = act[x];

  for (;;) {
    j = i >> 1;    // parent of i
    y = h[j];      // variable at position j in the heap

    // The loop terminates since act[h[0]] = DBL_MAX
    if (act[y] >= ax) break;

    // move y down, into position i
    h[i] = y;
    index[y] = i;

    // move i up
    i = j;
  }

  // i is the new position for variable x
  h[i] = x;
  index[x] = i;
}

static
void var_queue_update_down(var_queue_t *queue) {
  double *act;
  int32_t *index;
  variable_t *h;
  variable_t x, y, z;
  double ax, ay, az;
  uint32_t i, j, last;

  last = queue->heap_last;
  queue->heap_last = last - 1;
  if (last <= 1 ) { // empty heap.
    assert(queue->heap_last == 0);
    return;
  }

  h = queue->heap;
  index = queue->heap_index;
  act = queue->activity;

  z = h[last];   // last element
  h[last] = -2;  // set end marker: act[-2] is negative
  az = act[z];   // activity of the last element

  i = 1;      // root
  j = 2;      // left child of i
  while (j < last) {
    /*
     * find child of i with highest activity.
     * Since h[last] = -2, we don't check j+1 < last
     */
    x = h[j];
    y = h[j+1];
    ax = act[x];
    ay = act[y];
    if (ay > ax) {
      j++;
      x = y;
      ax = ay;
    }

    // x = child of node i of highest activity
    // j = position of x in the heap (j = 2i or j = 2i+1)
    if (az >= ax) break;

    // move x up, into heap[i]
    h[i] = x;
    index[x] = i;

    // go down one step.
    i = j;
    j <<= 1;
  }

  h[i] = z;
  index[z] = i;
}

/**
 * Insert x into the heap, using its current activity.
 * No effect if x is already in the heap.
 * - x must be between 0 and nvars - 1
 */
void var_queue_insert(var_queue_t *queue, variable_t x) {
  assert(x >= 0);
  assert(x < queue->size);
  if (queue->heap_index[x] < 0) {
    // x not in the heap
    queue->heap_last ++;
    var_queue_update_up(queue, x, queue->heap_last);
  }
}


/** Check whether the heap is empty. */
bool var_queue_is_empty(var_queue_t *queue) {
  return queue->heap_last == 0;
}


/** Get and remove top element (the heap must not be empty) */
variable_t var_queue_pop(var_queue_t *queue) {
  variable_t top;

  assert(queue->heap_last > 0);

  // remove top element
  top = queue->heap[1];
  queue->heap_index[top] = -1;

  // repair the heap
  var_queue_update_down(queue);

  return top;
}

/** Get random element (the heap must not be empty) */
variable_t var_queue_random(var_queue_t *queue, double* seed) {
  assert(queue->heap_last > 0);
  return queue->heap[irand(seed, queue->heap_last)+1];
}

/** Rescale variable activities: divide by VAR_ACTIVITY_THRESHOLD. */
void var_queue_rescale_activities(var_queue_t *queue) {
  uint32_t i, n;
  double *act;

  n = queue->size;
  act = queue->activity;
  for (i=0; i<n; i++) {
    act[i] *= INV_VAR_ACTIVITY_THRESHOLD;
  }
  queue->act_increment *= INV_VAR_ACTIVITY_THRESHOLD;
}


/** Increase activity of variable x (factor times). */
void var_queue_bump_variable(var_queue_t *heap, variable_t x, uint32_t factor) {
  int32_t i;

  assert(factor > 0);
  assert(x < heap->size);

  if ((heap->activity[x] += factor * heap->act_increment) > VAR_ACTIVITY_THRESHOLD) {
    var_queue_rescale_activities(heap);
  }

  // move x up if it's in the heap
  i = heap->heap_index[x];
  if (i >= 0) {
    var_queue_update_up(heap, x, i);
  }
}

double var_queue_get_activity(const var_queue_t* queue, variable_t x) {
  assert(x < queue->size);
  return queue->activity[x];
}

void var_queue_set_activity(var_queue_t* queue, variable_t x, double a) {
  assert(x < queue->size);
  assert(queue->heap_index[x] < 0);
  queue->activity[x] = a;
}

int var_queue_cmp_variables(var_queue_t *queue, variable_t x, variable_t y) {
  assert(x < queue->size);
  assert(y < queue->size);

  double diff = queue->activity[x] - queue->activity[y];

  if (diff < 0) {
    return -1;
  }
  if (diff > 0) {
    return 1;
  }

  return 0;
}

/** Decay. */
void var_queue_decay_activities(var_queue_t *queue) {
  queue->act_increment *= queue->inv_act_decay;
}

/** Sweep the variables */
void var_queue_gc_sweep(var_queue_t* queue, const gc_info_t* gc_vars) {

  ivector_t vars;
  init_ivector(&vars, 0);

  assert(gc_vars->is_id);

  // pop all the variable and put them back in
  while (!var_queue_is_empty(queue)) {
    variable_t x = var_queue_pop(queue);
    if (gc_info_get_reloc(gc_vars, x) != variable_null) {
      ivector_push(&vars, x);
    }
  }
  uint32_t var_i;
  for (var_i = 0; var_i < vars.size; ++ var_i) {
    variable_t x = vars.data[var_i];
    var_queue_insert(queue, x);
  }

  delete_ivector(&vars);
}
