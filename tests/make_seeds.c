#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#ifdef MINGW

static inline long int random(void) {
  return rand();
}

#endif


#define N 10000

int main() {
  FILE *f;
  int i;

  f = fopen("seeds", "w");
  if (f == NULL) {
    perror("seeds");
    exit(1);
  }

  for (i=0; i<N; i++) {
    fprintf(f, "%d\n", (int) random());
  }
  fclose(f);
  return 0;
}
