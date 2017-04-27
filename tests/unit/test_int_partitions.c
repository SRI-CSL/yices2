/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <stdio.h>
#include <inttypes.h>

#include "utils/hash_functions.h"
#include "utils/index_vectors.h"
#include "utils/int_partitions.h"



/*
 * Hash code for an integer x
 */
static uint32_t hash(void *aux, int32_t x) {
  return jenkins_hash_int32(x % 61);
}


/*
 * Equality test
 */
static bool match(void *aux, int32_t x, int32_t y) {
  return x % 61 == y % 61;
}


/*
 * Print record r
 */
static void print_ipart_record(ipart_rec_t *r) {
  printf("[hash = %08"PRIx32", cid = %"PRId32", data = %"PRId32"]", r->hash, r->cid, r->data);
}


/*
 * Print vector v
 */
static void print_ipart_vector(int32_t *v) {
  uint32_t i, n;

  n = iv_size(v);
  for (i=0; i<n; i++) {
    printf(" %"PRId32, v[i]);
  }
}


/*
 * Print hash table + classes
 */
static void print_ipart(ipart_t *ip) {
  ipart_rec_t *d;
  uint32_t i, n;

  printf("ip %p\n", ip);
  printf("  size = %"PRIu32"\n", ip->size);
  printf("  nelems = %"PRIu32"\n", ip->nelems);
  printf("  csize = %"PRIu32"\n", ip->csize);
  printf("  nclasses = %"PRIu32"\n", ip->nclasses);

  n = ip->nelems;
  if (n > 0) {
    printf("  Content\n");
    d = ip->records;
    n = ip->size;
    for (i=0; i<n; i++) {
      if (d->data != not_an_index) {
	printf("   rec[%"PRIu32"]: ", i);
	print_ipart_record(d);
	printf("\n");
      }
      d ++;
    }
  }

  n = ip->nclasses;
  if (n > 0) {
    printf("  Classes\n");
    for (i=0; i<n; i++) {
      printf("   class[%"PRIu32"]: ", i);
      print_ipart_vector(ip->classes[i]);
      printf("\n");
    }
  }
}




/*
 * Global partition table
 */
static ipart_t ip;



int main(void) {
  int32_t i;

  init_int_partition(&ip, 16, NULL, (ipart_hash_fun_t) hash, (ipart_match_fun_t) match);
  printf("=== Init ===\n");
  print_ipart(&ip);
  printf("\n\n");

  for (i=0; i<100; i++) {
    int_partition_add(&ip, i);
    if (i % 10 == 9) {
      printf("=== Added %"PRIu32" objects ===\n", i+1);
      print_ipart(&ip);
      printf("\n\n");
    }
  }

  printf("=== Final ===\n");
  print_ipart(&ip);
  printf("\n\n");


  reset_int_partition(&ip);
  printf("=== After reset ===\n");
  print_ipart(&ip);
  printf("\n\n");

  for (i=0; i<140; i++) {
    int_partition_add(&ip, 200-i);
    if (i % 10 == 9) {
      printf("=== Added %"PRIu32" objects ===\n", i+1);
      print_ipart(&ip);
      printf("\n\n");
    }
  }

  printf("=== Final ===\n");
  print_ipart(&ip);
  printf("\n\n");

  delete_int_partition(&ip);

  return 0;
}
