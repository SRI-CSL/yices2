#include <stdio.h>
#include <stdint.h>

#include "hash_functions.h"
#include "hash_functions_ori.h"
#include "cputime.h"


#define N 2048
#define MASK (N - 1)

static char *test[] = {
  "abchbj",
  "hjnd2qb367",
  "x10", "x11", "x12", "x13", "x14", 
  "x15", "x16", "x17", "x18", "x19",
  "alpha", "beta", "gamma", "delta", "epsilon", "eta", "phi", "iota", 
  "kappa", "psi", "mu", "nu", "omega", "omicron", "theta",
  "January", "February", "March", "April", "May", "June", "July",
  "August", "September", "October", "November", "December",
  "Janvier", "Fevrier", "Mars", "Avril", "May", "Juin", "Juillet",
  "Aout", "Septembre", "Octobre", "Novembre", "Decembre",
  "monday-1", "tuesday-2", "wednesday-3", "thursday-4", "friday-5",
  "saturday-6", "sunday-7",
};


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


int main() {
  int i, n;
  uint32_t h;
  double runtime;

  runtime = get_cpu_time();
  for (n=0; n<1000000; n++) {
    for (i=0; i<58; i++) {
      h = hash_string(test[i]) & MASK;
    }
  }
  runtime = get_cpu_time() - runtime;
  printf("naive hash:   %u calls\n", 10000000 * 58);
  printf("cpu time:     %.4f s\n", runtime);

  runtime = get_cpu_time();
  for (n=0; n<1000000; n++) {
    for (i=0; i<58; i++) {
      h = jenkins_hash_string_ori(test[i], 0x17838abc) & MASK;
    }
  }
  runtime = get_cpu_time() - runtime;
  printf("jenkins hash:  %u calls\n", 10000000 * 58);
  printf("cpu time:      %.4f s\n", runtime);

  runtime = get_cpu_time();
  for (n=0; n<1000000; n++) {
    for (i=0; i<58; i++) {
      h = jenkins_hash_string_var(test[i], 0x17838abc) & MASK;
    }
  }
  runtime = get_cpu_time() - runtime;
  printf("jenkins hash2: %u calls\n", 10000000 * 58);
  printf("cpu time:      %.4f s\n", runtime);

  return 0;
}
