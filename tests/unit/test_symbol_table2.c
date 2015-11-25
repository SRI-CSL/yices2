/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST SYMBOL TABLE
 * - try bad use cases: lots of identical strings added to the table
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

#include "utils/cputime.h"
#include "utils/memsize.h"
#include "utils/symbol_tables.h"

static char buffer[1000];
static char **words;
static uint32_t n_words;
static uint32_t size_words;
static stbl_t sym_table;


static void words_from_file(const char *filename) {
  FILE *f;
  char *str, *tmp;
  uint32_t i, n, len;

  size_words = 0;
  n_words = 0;

  f = fopen(filename, "r");
  if (f == NULL) {
    perror(filename);
    exit(1);
  }

  i = 0;
  n = 100;
  words = (char **) malloc(n * sizeof(char *));
  if (words == NULL) goto malloc_failed;
  size_words = n;

  buffer[99] = '\0';
  buffer[100] = '\0';
  str = fgets(buffer, 99, f);
  while (str != NULL) {
    len = strlen(str);
    // remove \n if present
    if (str[len - 1] == '\n') {
      len --;
      str[len] = '\0';
    }
    tmp = (char *) malloc(len + 1);
    if (tmp == NULL) goto malloc_failed;
    strcpy(tmp, str);
    if (i == n) {
      n += 100;
      words = (char **) realloc(words, n * sizeof(char *));
      if (words == NULL) goto malloc_failed;
      size_words = n;
    }
    words[i] = tmp;
    i ++;

    str = fgets(buffer, 99, f);
  }
  fclose(f);

  n_words = i;
  return;

 malloc_failed:
  fprintf(stderr, "Malloc failed\n");
  exit(1);
}

static void clear_words(void) {
  uint32_t j;

  for (j=0; j<n_words; j++) free(words[j]);
  free(words);
}

static int32_t new_val(uint32_t i, uint32_t j) {
  return 100000 * j + i;
}

int main(int argc, char *argv[]) {
  uint32_t i, j, n;
  double runtime, memused;
  int32_t x, *val;

  if (argc != 2) {
    fprintf(stderr, "Usage: %s filename\n", argv[0]);
    fprintf(stderr, "  filename must contain a set of strings, one per line, less than 100 char long\n");
    fflush(stderr);
    exit(1);
  }
  words_from_file(argv[1]);

  init_stbl(&sym_table, 0);

  val = (int32_t *) malloc(n_words * sizeof(int32_t));
  if (val == NULL) {
    fprintf(stderr, "Failed to allocate array val\n");
    exit(1);
  }

  for (i=0; i<n_words; i++) {
    x = stbl_find(&sym_table, words[i]);
    if (x < 0) {
      stbl_add(&sym_table, words[i], i);
      val[i] = i;
    } else {
      val[i] = x;
    }
  }

  printf("\n--- checking ---\n");
  for (i=0; i<n_words; i++) {
    x = stbl_find(&sym_table, words[i]);
    if (x != val[i]) {
      printf("*** Error: %s, val = %"PRId32", should be %"PRId32" ***\n", words[i], x, val[i]);
      fflush(stdout);
      exit(1);
    }
  }

  printf("\n*** Added %"PRIu32" words from %s ***\n", n_words, argv[1]);

  // repeated additions of the same symbols with multiple lookups
  // warning: this code does not work (may give a false alarm)
  // if the input file contains duplicates.
  n = (n_words < 200) ?  n_words : 200;
  printf("\n*** Repeated symbol addition ***\n");
  runtime = get_cpu_time();
  for (i=0; i<10000; i++) {
    for (j=0; j<n; j++) {
      stbl_add(&sym_table, words[j], new_val(i, j));
    }
    for (j=0; j<n; j++) {
      x = stbl_find(&sym_table, words[j]);
      if (x != new_val(i, j)) {
	printf("*** Error: %s, val = %"PRId32", should be %"PRId32" ***\n", words[j], x, new_val(i, j));
	fflush(stdout);
	exit(1);
      }
    }
    for (j=0; j<n; j++) {
      x = stbl_find(&sym_table, words[j]);
      if (x != new_val(i, j)) {
	printf("*** Error: %s, val = %"PRId32", should be %"PRId32" ***\n", words[j], x, new_val(i, j));
	fflush(stdout);
	exit(1);
      }
    }
    for (j=0; j<n_words; j++) {
      x = stbl_find(&sym_table, words[j]);
    }
    for (j=0; j<n; j++) {
      x = stbl_find(&sym_table, words[j]);
      if (x != new_val(i, j)) {
	printf("*** Error: %s, val = %"PRId32", should be %"PRId32" ***\n", words[j], x, new_val(i, j));
	fflush(stdout);
	exit(1);
      }
    }
    for (j=0; j<n_words; j++) {
      x = stbl_find(&sym_table, words[j]);
    }
  }


  runtime = get_cpu_time() - runtime;
  memused = mem_size() / (1024 * 1024);
  printf("Adding 10000 times the same %"PRIu32" words + repeated lookups\n", n);
  printf("Runtime: %.4f s\n", runtime);
  printf("Table size: %"PRIu32" (nelems = %"PRIu32", ndeleted = %"PRIu32")\n",
	sym_table.size, sym_table.nelems, sym_table.ndeleted);
  if (memused > 0) {
    printf("Memory used: %.2f MB\n", memused);
  }

  clear_words();
  free(val);
  delete_stbl(&sym_table);

  return 0;
}
