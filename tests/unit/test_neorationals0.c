/*
 * Test of neorational functions
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>
#include <limits.h>
#include <inttypes.h>
#include <gmp.h>



#include "terms/neorationals.h"


int main(int argc, char* argv[]){
  neorational_t nq;

  mpq_t *q = new_mpq();


  neoq_init(&nq);

  set_ratgmp(&nq, q);

  fprintf(stderr, "%p\n", q);

  fprintf(stderr, "is_ratgmp %d\n", is_ratgmp(&nq));

  mpq_t * foo = get_gmp(&nq);

  fprintf(stderr, "%p\n", (void *)foo);

  neoq_clear(&nq);

  fprintf(stderr, "is_rat32 %d\n", is_rat32(&nq));
  fprintf(stderr, "is_ratgmp %d\n", is_ratgmp(&nq));
  fprintf(stderr, "rat32 num %d\n", get_num(&nq));
  fprintf(stderr, "rat32 den %d\n", get_den(&nq));


  return 0;
}
