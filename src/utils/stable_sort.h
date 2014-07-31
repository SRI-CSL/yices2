/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STABLE-SORT
 */

/*
 * This stable-sort implementation is based on Tim Peters' timsort
 * (used by Python) with the 'galloping' part omitted. It's intended
 * for sorting arrays of pointers, using a user-provided comparison
 * function.
 *
 * References
 * ----------
 *  http://bugs.python.org/file4451/timsort.txt
 *  http://hg.python.org/cpython/file/default/Objects/listobject.c
 *
 *
 * Overview
 * --------
 * The algorithm is a merge sort that processes an array A of N
 * elements from left to right. The processed part is a prefix
 * A[0 ... K-1] of A where K <= N; the unprocessed part is A[K ... N-1].
 *
 * The processed part is divided in a sequence of segments or runs, where
 * each run is sorted in increasing order. Assuming we have n segments,
 * then we store the start index of each of them as:
 *   s[0] = 0 = start of the first run
 *   s[1] = start of the second run
 *    ...
 *   s[n-1] = start of the n-th segment
 *   s[n] = start of the unprocessed section of A = K
 *
 * Array s[0 ... n] is used as a stack. New segments are pushed by increasing n.
 *
 * The size of a segment i is then d[i] = s[i+1] - s[i] for i=0 to n-1.
 * The algorithm maintains the following invariant:
 *   d[n-1] > 0  (last segment is non empty)
 *   d[n-2] > d[n-1]
 *   d[n-3] > d[n-2] + d[n-1]
 *     ...
 *   d[0]   > d[1] + ... + d[n-1]
 *
 * It follows that d[i] >= 2^(n-i-1) and K = d[0] + ... + d[n-1] >= 2^n
 * The maximal array size we can handle is 2^32-1 so we need no more than
 * 32 segments. We use a fixed size array or 33 elements to store s[0] ... s[n].
 *
 * The algorithm works as follows:
 * 1) initially, set K=0, n=0, s[0] = 0.
 * 2) while K < N:
 *    - find or construct an initial run in A[K ... N-1]
 *    - assume this run is A[K ... M-1]
 *      (i.e., we have A[K] <= A[K-1] <= ... <= A[M-1])
 *    - push M on top of the segment stack
 *    - the stack is then of the form s[0] .... s[n] where s[n] = M
 *    - if d[n-1] >= d[n-2] or d[n-1] + d[n-2] >= d[n-3] then
 *      restore the invariant by merging consecutive runs.
 *    - K := M
 * 3) Finish the sort by merging all successive runs, starting with
 *    the last two.
 *
 * To find the initial run in A[K ... N-1]
 * - search for the longest increasing run starting from K
 *     A[K] <= A[K+1] <= ... <= A[M-1] > A[M]
 *   or for the longest strictly decreasing run
 *     A[K] > A[K+1 > ... > A[M-1] <= A[M]
 * - this gives us a run A[K ... M-1]
 *   if the run is striclty decreasing, reverse its elements
 *   to turn it into an increasing run.
 * - if the run is too short (i.e., M - K <= min_run)
 *   then extend it by sorting A[K .. M-1, ... K + min_run - 1]
 *   using an insertion sort.
 *
 * min_run is between 32 and 64. It's computed so that N/min_run is either
 * a power of two or close but smaller than a power of two.
 *
 * Data structures
 * ---------------
 * - we keep a pointer to the array A
 * - the ordering function cmp
 * - the stack seg of 33 indices + the number of segments n
 * - an auxiliary array used when merging successive runs
 *   (its size is at most N/2)
 */

#ifndef __STABLE_SORT_H
#define __STABLE_SORT_H

#include <stdint.h>
#include <stdbool.h>

/*
 * Sorter structure:
 * - data = array to store
 * - nelems = size of this array
 * - cmp = ordering function
 * - aux = auxiliary external pointer passed to cmp
 *
 * - seg = segment stack
 * - nsegs = number of segments
 *   seg[i] = start of segment i for i=0 ... nsegs -1
 *   seg[nsegs] = start of the unprocessed part of A
 * - buffer = pointer to the auxiliary buffer
 *   bsize = size of this buffer
 * - b = fixed-sized array used as buffer (to save calls to malloc
 *   until we need a larger buffer).
 *
 * Elements in data are void* pointers.
 * The comparison function takes three arguments:
 *   cmp(aux, x, y)
 * where aux = the auxiliary pointer.
 * - cmp(aux, x, y) must return true if x <= y in the ordering.
 */

// maximal number of runs/segments
#define MAX_SEGMENTS 34

// size of the fixed buffer b:
#define FIXED_BUFFER_SIZE 256

// maximal size of the buffer (we could make this larger on 64bit machines)
#define MAX_BUFFER_SIZE (UINT32_MAX/sizeof(void *))

typedef bool (*cmp_fun_t)(const void *aux, const void *x, const void *y);

typedef struct stable_sorter_s {
  cmp_fun_t cmp;
  void *aux;
  void **data;
  uint32_t nelems;

  uint32_t seg[MAX_SEGMENTS];
  uint32_t nsegs;
  void **buffer;
  uint32_t bsize;
  void *b[FIXED_BUFFER_SIZE];
} stable_sorter_t;


/*
 * Initialize a sorter structure:
 * - cmp = ordering function
 * - aux = auxiliary object
 * - data is set to NULL and nelems to 0
 */
extern void init_stable_sorter(stable_sorter_t *sorter, void *aux, cmp_fun_t cmp);


/*
 * Delete: free all internal memory
 */
extern void delete_stable_sorter(stable_sorter_t *sorter);


/*
 * Sort array a of n elements
 * - sorter must be initialized with the right comparison function
 */
extern void apply_sorter(stable_sorter_t *sorter, void **a, uint32_t n);


/*
 * Direct stable sort of a using the given comparison function
 * - this initializes then delete an internal sorter object
 */
extern void stable_sort(void **a, uint32_t n, void *aux, cmp_fun_t cmp);


#endif /* __STABLE_SORT_H */
