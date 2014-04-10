/*
 * Test the division and remainder operations
 * on bitvector constants.
 */

#include <stdio.h>
#include <inttypes.h>

#include <gmp.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <pthread.h>

#include "bv_constants.h"
#include "bv64_constants.h"


/*
 * Test x divided by y
 * - both stored as uin64_t, interpreted as n-bit constants
 */
static void test_bv64(FILE* output, uint64_t x, uint64_t y, uint32_t n) {
  uint64_t udiv, urem, sdiv, srem, smod;

  x = norm64(x, n);
  y = norm64(y, n);
  udiv = bvconst64_udiv2z(x, y, n);
  urem = bvconst64_urem2z(x, y, n);
  sdiv = bvconst64_sdiv2z(x, y, n);
  srem = bvconst64_srem2z(x, y, n);
  smod = bvconst64_smod2z(x, y, n);

  fprintf(output, "udiv(%"PRIu64", %"PRIu64") = %"PRIu64", ", x, y, udiv);
  fprintf(output, "urem(%"PRIu64", %"PRIu64") = %"PRIu64", ", x, y, urem);
  fprintf(output, "sdiv(%"PRIu64", %"PRIu64") = %"PRIu64", ", x, y, sdiv);
  fprintf(output, "srem(%"PRIu64", %"PRIu64") = %"PRIu64", ", x, y, srem);
  fprintf(output, "smod(%"PRIu64", %"PRIu64") = %"PRIu64"\n", x, y, smod);
}



static inline uint32_t bv32(uint32_t *x) {
  return bvconst_get32(x);
}

static inline uint64_t bv64(uint32_t *x) {
  return bvconst_get64(x);
}

/*
 * Test x divided by y
 * - both stored as word vectors, interpreted as n-bit constants
 * - n must be no more than 64;
 */
static void test_bv(FILE* output, uint32_t *x, uint32_t *y, uint32_t n) {
  uint32_t udiv[2], urem[2];
  uint32_t sdiv[2], srem[2], smod[2];

  assert(0 < n && n <= 64);

  bvconst_normalize(x, n);
  bvconst_normalize(y, n);

  bvconst_udiv2z(udiv, n, x, y);
  bvconst_normalize(udiv, n);
  bvconst_urem2z(urem, n, x, y);
  bvconst_normalize(urem, n);
  bvconst_sdiv2z(sdiv, n, x, y);
  bvconst_normalize(sdiv, n);
  bvconst_srem2z(srem, n, x, y);
  bvconst_normalize(srem, n);
  bvconst_smod2z(smod, n, x, y);
  bvconst_normalize(smod, n);

  if (n <= 32) {
    fprintf(output, "udiv(%"PRIu32", %"PRIu32") = %"PRIu32", ", bv32(x), bv32(y), bv32(udiv));
    fprintf(output, "urem(%"PRIu32", %"PRIu32") = %"PRIu32", ", bv32(x), bv32(y), bv32(urem));
    fprintf(output, "sdiv(%"PRIu32", %"PRIu32") = %"PRIu32", ", bv32(x), bv32(y), bv32(sdiv));
    fprintf(output, "srem(%"PRIu32", %"PRIu32") = %"PRIu32", ", bv32(x), bv32(y), bv32(srem));
    fprintf(output, "smod(%"PRIu32", %"PRIu32") = %"PRIu32"\n", bv32(x), bv32(y), bv32(smod));
  } else {
    fprintf(output, "udiv(%"PRIu64", %"PRIu64") = %"PRIu64", ", bv64(x), bv64(y), bv64(udiv));
    fprintf(output, "urem(%"PRIu64", %"PRIu64") = %"PRIu64", ", bv64(x), bv64(y), bv64(urem));
    fprintf(output, "sdiv(%"PRIu64", %"PRIu64") = %"PRIu64", ", bv64(x), bv64(y), bv64(sdiv));
    fprintf(output, "srem(%"PRIu64", %"PRIu64") = %"PRIu64", ", bv64(x), bv64(y), bv64(srem));
    fprintf(output, "smod(%"PRIu64", %"PRIu64") = %"PRIu64"\n", bv64(x), bv64(y), bv64(smod));
  }
}

void* test_thread(void* arg){
  FILE* output = (FILE *)arg;

  uint32_t i, j;
  uint32_t x[2], y[2];
  uint64_t a, b;

  fprintf(output, "--- bit size = 5 ---\n");
  for (i=0; i<32; i++) {
    for (j=0; j<32; j++) {
      a = i;
      b = j;
      test_bv64(output, a, b, 5);
      x[0] = i; x[1] = 0;
      y[0] = j; y[1] = 0;
      test_bv(output, x, y, 5);
      fprintf(output, "---\n");
    }
  }

  return NULL;
}

#define NTHREADS  2


int main() {
  int retcode, thread;
  char  buff[1024];
  FILE*  outfp[NTHREADS];
  pthread_t tids[NTHREADS];

  printf("%d threads\n", NTHREADS);

  for(thread = 0; thread < NTHREADS; thread++){
    snprintf(buff, 1024, "/tmp/test_bvconst_divisions_mt_%d.txt", thread);
    printf("Logging thread %d to %s\n", thread, buff);
    outfp[thread] = fopen(buff, "w");
    if(outfp[thread] == NULL){
      fprintf(stderr, "fopen failed: %s\n", strerror(errno));
      exit(0);
    }
    retcode =  pthread_create(&tids[thread], NULL, test_thread, outfp[thread]);
    if(retcode){
      fprintf(stderr, "pthread_create failed: %s\n", strerror(retcode));
      exit(0);
    }
  }

  printf("threads away\n\n");


  for(thread = 0; thread < NTHREADS; thread++){
    retcode = pthread_join(tids[thread], NULL);
    if(retcode){
      fprintf(stderr, "pthread_join failed: %s\n", strerror(retcode));
    }
    fclose(outfp[thread]);
  }

  return 0;
}

