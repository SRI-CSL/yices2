/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

// Force assert
#ifdef NDEBUG
#undef NDEBUG
#endif

#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/cputime.h"
#include "utils/ptr_sets.h"

/*
 * Check that the counters s->nelems and s->ndeleted are correct
 */
static bool good_ptr_set(ptr_set_t *s) {
  void *p;
  uint32_t i, n;
  uint32_t elems, deleted;

  elems = 0;
  deleted = 0;

  n = s->size;
  for (i=0; i<n; i++) {
    p = s->data[i];
    if (p == DELETED_PTR_ELEM) {
      deleted ++;
    } else if (p != NULL) {
      elems ++;
    }
  }

  return (elems == s->nelems) && (deleted == s->ndeleted);
}


/*
 * Check that s has the same content as defined by arrays a and flag
 * - n = size of both arrays
 * - all elements of a must be distinct
 * - the expected set is the set of all a[i]'s such that flag[i] is true
 */
static bool check_ptr_set_content(ptr_set_t *s, void *a[], bool flag[], uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (ptr_set_member(s, a[i]) != flag[i]) {
      return false;
    }
  }

  return true;
}


/*
 * Show the content of set s
 */
static void print_ptr_set(FILE *f, ptr_set_t *s) {
  void *p;
  uint32_t i, n, k;

  if (s == NULL) {
    fputs("{}\n", f);
  } else {
    fputc('{', f);
    n = s->size;
    k = 0;
    for (i=0; i<n; i++) {
      p = s->data[i];
      if (p != NULL && p != DELETED_PTR_ELEM) {
	if (k >= 8) {
	  fputs("\n ", f);
	  k = 0;
	}
	k ++;
	fprintf(f, " %p", p);
      }
    }
    fputs(" }\n", f);
  }
}

static void show_ptr_set_details(FILE *f, ptr_set_t *s) {
  fprintf(f, "Set: %p\n", s);
  if (s != NULL) {
    fprintf(f, "  size = %"PRIu32"\n", s->size);
    fprintf(f, "  nelems = %"PRIu32"\n", s->nelems);
    fprintf(f, "  ndeleted = %"PRIu32"\n", s->ndeleted);
  }
  fprintf(f, "  content:\n");
  print_ptr_set(f, s);
  fprintf(f, "\n");
}


/*
 * Test speed: add all elements of a to s then remove then all
 */
static void speed_test(ptr_set_t **s, void *a[], uint32_t n) {
  double start, end;
  uint32_t i, j;

  start = get_cpu_time();
  for (i=0; i<2000; i++) {
    j = n;
    while (j > 0) {
      j --;
      ptr_set_add(s, a[j]);
    }
    while (j < n) {
      ptr_set_add(s, a[j]);
      j ++;
    }
    while (j > 0) {
      j --;
      ptr_set_remove(s, a[j]);
    }
    while (j < n) {
      ptr_set_remove(s, a[j]);
      j ++;
    }    
  }

  end = get_cpu_time();
  printf("Speed test: %"PRIu32" add/remove operations in %.3f s\n", 4 * n * 2000, time_diff(end, start));  
}


/*
 * GLOBAL ARRAY
 */
#define TEST_SIZE 300

static void *test_data[TEST_SIZE];
static bool flag[TEST_SIZE];

static void init_test_data(void) {
  uint32_t i, n;

  n = TEST_SIZE;
  for (i=0; i<n; i++) {
    test_data[i] = (void *) &test_data[i];
    flag[i] = false;
  }
}


int main(void) {
  ptr_set_t *test;
  uint32_t i;

  init_test_data();

  test = NULL;
  printf("Initial set\n");
  show_ptr_set_details(stdout, test);
  printf("\n");

  for (i=0; i<100; i++) {
    ptr_set_add(&test, test_data[i]);
    flag[i] = true;
  }
  assert(good_ptr_set(test));
  assert(check_ptr_set_content(test, test_data, flag, 300));
	 
  printf("Content: after 100 additions\n");
  show_ptr_set_details(stdout, test);
  printf("\n");

  for (i=0; i<50; i++) {
    ptr_set_remove(&test, test_data[i]);
    flag[i] = false;
  }
  assert(good_ptr_set(test));
  assert(check_ptr_set_content(test, test_data, flag, 300));

  printf("Content: after 50 removals\n");
  show_ptr_set_details(stdout, test);
  printf("\n");

  for (i=50; i<100; i++) {
    ptr_set_remove(&test, test_data[i]);
    flag[i] = false;
  }
  assert(good_ptr_set(test));
  assert(check_ptr_set_content(test, test_data, flag, 300));

  printf("Content: after 50 removals\n");
  show_ptr_set_details(stdout, test);
  printf("\n");

  i = 300;
  while (i > 0) {
    i --;
    ptr_set_add(&test, test_data[i]);
    flag[i] = true;
  }
  assert(good_ptr_set(test));
  assert(check_ptr_set_content(test, test_data, flag, 300));
	 
  printf("Content: after 300 additions\n");
  show_ptr_set_details(stdout, test);
  printf("\n");

  for (i=100; i<200; i++) {
    ptr_set_remove(&test, test_data[i]);
    flag[i] = false;
  }
  assert(good_ptr_set(test));

  printf("Content: after 100 removals\n");
  show_ptr_set_details(stdout, test);
  printf("\n");

  for (i=200; i<300; i++) {
    ptr_set_remove(&test, test_data[i]);
    flag[i] = false;
  }
  assert(good_ptr_set(test));
  assert(check_ptr_set_content(test, test_data, flag, 300));

  printf("Content: after 100 removals\n");
  show_ptr_set_details(stdout, test);
  printf("\n");

  for (i=200; i<300; i++) {
    ptr_set_add(&test, test_data[i]);
    flag[i] = true;
  }
  assert(good_ptr_set(test));
  assert(check_ptr_set_content(test, test_data, flag, 300));

  printf("Content: after 100 additions\n");
  show_ptr_set_details(stdout, test);
  printf("\n");

  for (i=0; i<100; i += 2) {
    ptr_set_remove(&test, test_data[i]);
    flag[i] = false;
  }
  for (i=200; i<300; i += 2) {
    ptr_set_remove(&test, test_data[i]);
    flag[i] = false;
  }
  printf("Content: after removing half of the elements\n");
  show_ptr_set_details(stdout, test);
  printf("\n");

  assert(good_ptr_set(test));
  assert(check_ptr_set_content(test, test_data, flag, 300));

  for (i=0; i<300; i++) {
    if (flag[i]) {
      ptr_set_remove(&test, test_data[i]);
      flag[i] = false;
    }
  }
  printf("Final cleanup: removed all elements\n");
  show_ptr_set_details(stdout, test);
  printf("\n");

  assert(good_ptr_set(test));
  assert(check_ptr_set_content(test, test_data, flag, 300));

  speed_test(&test, test_data, 300);

  free_ptr_set(test);

  return 0;
}
