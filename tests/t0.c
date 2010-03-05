#include <inttypes.h>
#include <stdio.h>

#include <gmp.h>
#include "term_printer.h"
#include "yices.h"

int main() {
  int i;

  yices_init();
  
  type_t ybool = yices_bool_type();
  type_t yint = yices_int_type();
  type_t yreal = yices_real_type();
  type_t bv[5];
  for (i=0; i<5; i++) {
    bv[i] = yices_bv_type(3 +  8 * i);
  }

  printf("bool type = %" PRId32 "\n", ybool);
  printf("int type = %" PRId32 "\n", yint);
  printf("real type = %" PRId32 "\n", yreal);
  for (i=0; i<5; i++) {
    printf("bv[%d] type = %" PRId32 "\n", 3 + 8 * i, bv[i]);
  }
  
  printf("\n--- Checking hconsing ---\n");
  printf("bool type = %" PRId32 "\n", yices_bool_type());
  printf("int type = %" PRId32 "\n", yices_int_type());
  printf("real type = %" PRId32 "\n", yices_real_type());
  for (i=0; i<5; i++) {
    printf("bv[%d] type = %" PRId32 "\n", 3 + 8 * i, yices_bv_type(3 + 8 * i));
  }

  // v: uninterpreted (bitvector 3)
  printf("\n--- bitvector test ---\n");
  term_t v = yices_new_uninterpreted_term(bv[0]);
  term_t w = yices_new_uninterpreted_term(bv[0]);
  printf("new bv terms: ");
  print_term_id(stdout, v);
  printf("::");
  print_type_id(stdout, bv[0]);
  printf("\n");
  print_term_id(stdout, w);
  printf("::");
  print_type_id(stdout, bv[0]);
  printf("\n");

  bvlogic_buffer_t *b = yices_new_bvlogic_buffer();
  int32_t code = yices_bvlogic_set_term(b, v);
  if (code < 0) {
    printf("*** Error ***\n");
    exit(1);
  }
  yices_bvlogic_not(b);
  printf("\n--- buffer: (bv-not ");
  print_term_id(stdout, v);
  printf(") ---\n");
  print_bvlogic_buffer(stdout, b);
  printf("\n");

  code = yices_bvlogic_and_term(b, w);
  if (code < 0) {
    printf("*** Error ***\n");
    exit(1);
  }
  printf("\n--- buffer: (bv-and ");
  print_term_id(stdout, w);
  printf(" (bv-not ");
  print_term_id(stdout, v);
  printf(")) ---\n");
  print_bvlogic_buffer(stdout, b);
  printf("\n");

  printf("\n--- bit expressions ---\n");
  for (i=0; i<b->nbits; i++) {
    print_bit_expr(stdout, b->bit[i]);
    printf("\n");
  }

  term_t u = yices_bvlogic_term(b);
  printf("\n--- resulting term ---\n");
  print_term_id(stdout, u);
  printf(" = ");
  print_term(stdout, u);
  printf("\n\n");

  printf("*** ALL TERMS ***\n");
  print_all_terms(stdout);

  printf("\n*** ALL TYPES ***\n");
  print_all_types(stdout);

  yices_free_bvlogic_buffer(b);  
  yices_cleanup();
  return 0;
}
