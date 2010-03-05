#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <inttypes.h>

#include "hash_functions.h"
#include "cputime.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

#endif


#define N 1024
#define MASK (N - 1)

static int stat[N];
static int hist[30];
static char buffer[1000];

static char **words;
static uint32_t n_words;
static uint32_t size_words;


static void histogram() {
  int i, j, last, over;

  for (i=0; i<30; i++) {
    hist[i] = 0;
  }
  over = 0;
  last = 0;

  for (i=0; i<N; i++) {
    j = stat[i];
    if (j >= 30) {
      over ++;
    } else {
      hist[j] ++;
      if (j > last) {
	last = j;
      }
    }
  }

  for (i=0; i<= last; i++) {
    printf("%2d elem --> %4d values\n", i, hist[i]);
  }
  if (over>0) {
    printf("more    --> %4d values\n", over);
  }
  printf("\n");
}


#if 0
// Not used anymore
static void show_stats() {
  int sum, max, min, sum_squares, i;
  double mean, var;

  sum = 0;
  max = 0;
  min = 0x7fffffff;
  sum_squares = 0;
  for (i=0; i<N; i++) {
    sum += stat[i];
    sum_squares += stat[i] * stat[i];
    if (stat[i] < min) min = stat[i];
    if (stat[i] > max) max = stat[i];    
  }

  mean = ((double) sum)/N;
  var = sqrt(((double) sum_squares)/N - (mean * mean));

  printf("mean:     %8.3f\n", mean);
  printf("variance: %8.3f\n", var);
  printf("min:      %8d\n", min);
  printf("max:      %8d\n", max);  
}
#endif

static void prefix_test(char *prefix, int n) {
  int i;
  uint32_t h;

  printf("\n--- prefix %s (%d suffixes) ---\n\n", prefix, n);
  for (i=0; i<N; i++) stat[i] = 0;
  for (i=0; i<n; i++) {
    sprintf(buffer, "%s%d", prefix, i);
    h = hash_string(buffer) & MASK;
    stat[h] ++;
  }

  printf("naive hash\n");
  histogram();

  for (i=0; i<N; i++) stat[i] = 0;
  for (i=0; i<n; i++) {
    sprintf(buffer, "%s%d", prefix, i);
    h = jenkins_hash_string_ori(buffer, 0x17838abc) & MASK;
    stat[h] ++;
  }

  printf("Jenkins hash\n");
  histogram();

  for (i=0; i<N; i++) stat[i] = 0;
  for (i=0; i<n; i++) {
    sprintf(buffer, "%s%d", prefix, i);
    h = jenkins_hash_string_var(buffer, 0x17838abc) & MASK;
    stat[h] ++;
  }

  printf("Jenkins hash variant\n");
  histogram();

  for (i=0; i<N; i++) stat[i] = 0;
  for (i=0; i<n; i++) {
    h = ((uint32_t) random()) & MASK;
    stat[h] ++;
  }

  printf("Random distribution\n");
  histogram();
}


static void words_from_file(char *filename) {
  FILE *f;
  char *str, *tmp;
  uint32_t i, n, len;

  size_words = 0;
  n_words = 0;

  f = fopen(filename, "r");
  if (f == NULL) {
    perror(filename);
    return;
  }

  i = 0;
  n = 100;
  words = (char **) malloc(n * sizeof(char *));
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
    strcpy(tmp, str);
    if (i == n) {
      n += 100;
      words = (char **) realloc(words, n * sizeof(char *));
      size_words = n;
    }
    words[i] = tmp;
    i ++;

    str = fgets(buffer, 99, f);
  }
  fclose(f);

  n_words = i;
}

static void clear_words() {
  uint32_t j;

  for (j=0; j<n_words; j++) free(words[j]);
  free(words);  
}

static void file_test(char *filename) {
  uint32_t i, j, h;
  double runtime;

  printf("\n--- File %s (%"PRIu32" strings) ---\n", filename, n_words);

  runtime = get_cpu_time();
  for (i=0; i<100000; i++) {
    for (j=0; j<N; j++) stat[j] = 0;
    for (j=0; j<n_words; j++) {
      h = hash_string(words[j]) & MASK;
      stat[h] ++;
    }
  }
  runtime = get_cpu_time() - runtime;
  printf("\nNaive hash:    %.4f s\n\n", runtime);
  histogram();  

  runtime = get_cpu_time();
  for (i=0; i<100000; i++) {
    for (j=0; j<N; j++) stat[j] = 0;
    for (j=0; j<n_words; j++) {
      h = jenkins_hash_string_ori(words[j], 0x17838abc) & MASK;
      stat[h] ++;
    }
  }
  runtime = get_cpu_time() - runtime;
  printf("\nJenkins hash:    %.4f s\n\n", runtime);
  histogram();

  runtime = get_cpu_time();
  for (i=0; i<100000; i++) {
    for (j=0; j<N; j++) stat[j] = 0;
    for (j=0; j<n_words; j++) {
      h = jenkins_hash_string_var(words[j], 0x17838abc) & MASK;
      stat[h] ++;
    }
  }
  runtime = get_cpu_time() - runtime;
  printf("\nJenkins hash variant: %.4f\n\n", runtime);
  histogram();
}

int main() {
  prefix_test("x", 100);
  prefix_test("x_", 100);
  prefix_test("y", 500);
  prefix_test("z", 1000);
  prefix_test("a", 2000);

  prefix_test("alpha", 600);
  prefix_test("x$4a", 900);
  prefix_test("aaaBBiwbcbue", 600);
  prefix_test("df093hc328vcc3h22gc", 900);
  prefix_test("9190ru09hnf93", 600);
  prefix_test("u_3f=hfho2bxgf", 900);

  words_from_file("data2.txt");
  file_test("data2.txt");
  clear_words();

  return 0;
}
