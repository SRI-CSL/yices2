/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <inttypes.h>

#include "utils/cputime.h"
#include "utils/hash_functions.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

#endif


#define N 262144
#define MASK (N - 1)
#define HIST 1000

static int stat[N];
static int hist[HIST];
static char buffer[1000];

static char **words;
static uint32_t n_words;
static uint32_t size_words;


/*
 * Simple hash for strings
 */
static uint32_t hash_string(char *s) {
  uint32_t h, x;

  h = 0;
  x = *s;
  while (x != 0) {
    h = 31 * h + x;
    s ++;
    x = *s;
  }

  return h;
}


/*
 * Original jenkins's hash functions (lookup2)
 */

/* Jenkins's lookup2.c code */
#define mix(a, b, c)                \
{                                   \
  a -= b; a -= c; a ^= (c>>13);     \
  b -= c; b -= a; b ^= (a<<8);      \
  c -= a; c -= b; c ^= (b>>13);     \
  a -= b; a -= c; a ^= (c>>12);     \
  b -= c; b -= a; b ^= (a<<16);     \
  c -= a; c -= b; c ^= (b>>5);      \
  a -= b; a -= c; a ^= (c>>3);      \
  b -= c; b -= a; b ^= (a<<10);     \
  c -= a; c -= b; c ^= (b>>15);     \
}

static uint32_t jenkins_hash_byte_ori(char *k, uint32_t len, uint32_t initval) {
  uint32_t a, b, c, n;

  a = b = 0x9e3779b9;
  c = initval;
  n = len;

  while (n >= 12) {
    a += (k[0] +((uint32_t)k[1]<<8) +((uint32_t)k[2]<<16) +((uint32_t)k[3]<<24));
    b += (k[4] +((uint32_t)k[5]<<8) +((uint32_t)k[6]<<16) +((uint32_t)k[7]<<24));
    c += (k[8] +((uint32_t)k[9]<<8) +((uint32_t)k[10]<<16)+((uint32_t)k[11]<<24));
    mix(a, b, c);
    k += 12;
    n -= 12;
   }

  c += len;
  switch (n) {
  case 11: c+=((uint32_t)k[10]<<24);
  case 10: c+=((uint32_t)k[9]<<16);
  case 9 : c+=((uint32_t)k[8]<<8);
    /* the first byte of c is reserved for the length */
  case 8 : b+=((uint32_t)k[7]<<24);
  case 7 : b+=((uint32_t)k[6]<<16);
  case 6 : b+=((uint32_t)k[5]<<8);
  case 5 : b+=k[4];
  case 4 : a+=((uint32_t)k[3]<<24);
  case 3 : a+=((uint32_t)k[2]<<16);
  case 2 : a+=((uint32_t)k[1]<<8);
  case 1 : a+=k[0];
    /* case 0: nothing left to add */
  }
  mix(a, b, c);

  return c;
}



/*
 * Hash of a character string.
 */
static uint32_t jenkins_hash_string_ori(char *s, uint32_t seed) {
  uint32_t n;
  n = strlen(s);
  return jenkins_hash_byte_ori(s, n, seed);
}


/*
 * Variant of Jenkins's original lookup2 hash function
 * for null-terminated strings.
 */
static uint32_t jenkins_hash_byte_var1(const uint8_t *s, uint32_t seed) {
  uint32_t a, b, c, x;

  a = b = 0x9e3779b9;
  c = seed;

  for (;;) {
    x = *s ++;
    if (x == 0) return c;
    a += x;
    a <<= 8;
    x = *s ++;
    if (x == 0) break;
    a += x;
    a <<= 8;
    x = *s ++;
    if (x == 0) break;
    a += x;
    a <<= 8;
    x = *s ++;
    if (x == 0) break;
    a += x;

    x = *s ++;
    if (x == 0) break;
    b += x;
    b <<= 8;
    x = *s ++;
    if (x == 0) break;
    b += x;
    b <<= 8;
    x = *s ++;
    if (x == 0) break;
    b += x;
    b <<= 8;
    x = *s ++;
    if (x == 0) break;
    b += x;

    x = *s ++;
    if (x == 0) break;
    c += x;
    c <<= 8;
    x = *s ++;
    if (x == 0) break;
    c += x;
    c <<= 8;
    x = *s ++;
    if (x == 0) break;
    c += x;
    c <<= 8;
    x = *s ++;
    if (x == 0) break;
    c += x;

    mix(a, b, c);
  }

  mix(a, b, c);

  return c;
}



/*
 * Histogram:
 * - input stat[x] = number of elements whose hash code is equal to x
 * - hist[i] = number of elements x such that stat[x] = i
 */
static void histogram(void) {
  int i, j, last, over;

  for (i=0; i<HIST; i++) {
    hist[i] = 0;
  }
  over = 0;
  last = 0;

  for (i=0; i<N; i++) {
    j = stat[i];
    if (j >= HIST) {
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
static void show_stats(void) {
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


/*
 * Test n strings with the same prefix
 */
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
    h = jenkins_hash_byte_var((uint8_t *) buffer, 0x17838abc) & MASK;
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


/*
 * Test strings read from a file
 */
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
    if (len > 0) {
      // remove \n if present
      if (str[len - 1] == '\n') {
	len --;
	str[len] = '\0';
      }
      tmp = (char *) malloc(len + 1);
      if (tmp == NULL) {
	fprintf(stderr, "malloc failed after %"PRIu32" words; skipping the rest of the file.\n", i);
	break;
      }
      strcpy(tmp, str);
      if (i == n) {
	n += 100;
	words = (char **) realloc(words, n * sizeof(char *));
	size_words = n;
      }
      words[i] = tmp;
      i ++;
    }
    str = fgets(buffer, 99, f);
  }
  fclose(f);

  n_words = i;
}

static void clear_words(void) {
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
      h = jenkins_hash_byte_var1((uint8_t *) words[j], 0x17838abc) & MASK;
      stat[h] ++;
    }
  }
  runtime = get_cpu_time() - runtime;

  printf("\nJenkins hash variant1: %.4f\n\n", runtime);
  histogram();

  runtime = get_cpu_time();
  for (i=0; i<100000; i++) {
    for (j=0; j<N; j++) stat[j] = 0;
    for (j=0; j<n_words; j++) {
      // this variant is in src/utils/hash_functions.c
      h = jenkins_hash_byte_var((uint8_t *) words[j], 0x17838abc) & MASK;
      stat[h] ++;
    }
  }
  runtime = get_cpu_time() - runtime;
  printf("\nJenkins hash variant2: %.4f\n\n", runtime);
  histogram();
}

int main(int argc, char *argv[]) {
  char *filename;

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

  if (argc == 2) {
    filename = argv[1];
    words_from_file(filename);
    file_test(filename);
    clear_words();
  }

  return 0;
}
