#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "varproducts.h"
#include "memalloc.h"


static void print_varexp_array(FILE *f, varexp_t *a, int32_t n) {
  int32_t i, d;

  if (n == 0) {
    fprintf(f, "[]");
    return;
  }
  d = a[0].exp;
  fprintf(f, "[x_%"PRId32, a[0].var);
  if (d != 1) {
    fprintf(f, "^%"PRId32, d);
  }
  for (i=1; i<n; i++) {
    d = a[i].exp;
    fprintf(f, " x_%"PRId32, a[i].var);
    if (d != 1) {
      fprintf(f, "^%"PRId32, d);
    }
  }
  fprintf(f, "]");
}

static void print_vpbuffer(FILE *f, vpbuffer_t *b, uint32_t level) {
  fprintf(f, "vpbuffer %p\n", b);
  fprintf(f, "  size = %"PRId32"\n", b->size);
  fprintf(f, "  len = %"PRId32"\n", b->len);
  fprintf(f, "  product = ");
  print_varexp_array(f, b->prod, b->len);
  fprintf(f, "\n");
}

static void print_varprod(FILE *f, varprod_t *p, uint32_t level) {
  fprintf(f, "varprod %p\n", p);
  fprintf(f, "  len = %"PRId32"\n", p->len);
  fprintf(f, "  product = ");
  print_varexp_array(f, p->prod, p->len);
  fprintf(f, "\n");
}




vpbuffer_t buffer;
varprod_t *p1, *p2, *p3, *p4, *p5;

int main() {
  init_vpbuffer(&buffer, 0);

  p1 = vpbuffer_getprod(&buffer);
  printf("p1 = []\n");
  print_varprod(stdout, p1, 10);
  printf("degree: %"PRId32"\n\n", varprod_degree(p1));

  vpbuffer_reset(&buffer);
  vpbuffer_mul_var(&buffer, 0);
  vpbuffer_mul_var(&buffer, 1);
  vpbuffer_mul_var(&buffer, 0);  
  p2 = vpbuffer_getprod(&buffer);
  printf("p2 = x_0 * x_1 * x_0\n");
  print_varprod(stdout, p2, 10);
  printf("degree: %"PRId32"\n\n", varprod_degree(p2));

  vpbuffer_set_varprod(&buffer, p2);
  vpbuffer_mul_varprod(&buffer, p1);
  p3 = vpbuffer_getprod(&buffer);
  printf("p3 = p1 * p2:\n");
  print_varprod(stdout, p3, 10);
  printf("degree: %"PRId32"\n\n", varprod_degree(p3));

  vpbuffer_set_varprod(&buffer, p2);
  vpbuffer_mul_varexp(&buffer, 1, 2);
  vpbuffer_mul_varexp(&buffer, 4, 3);
  p4 = vpbuffer_getprod(&buffer);
  printf("p4 = p2 * x_1^2 * x_4^3\n");
  print_varprod(stdout, p4, 10);
  printf("degree: %"PRId32"\n\n", varprod_degree(p4));  

  vpbuffer_set_varexp(&buffer, 3, 2);
  vpbuffer_mul_varexp(&buffer, 1, 4);
  p5 = vpbuffer_getprod(&buffer);
  printf("p5 = x_3^2 * x_1^4\n");
  print_varprod(stdout, p5, 10);
  printf("degree: %"PRId32"\n\n", varprod_degree(p5));

  printf("eq p1 p1: %d\n", varprod_equal(p1, p1));
  printf("eq p1 p2: %d\n", varprod_equal(p1, p2));
  printf("eq p2 p1: %d\n", varprod_equal(p2, p1));
  printf("eq p2 p3: %d\n", varprod_equal(p2, p3));
  printf("eq p3 p2: %d\n", varprod_equal(p3, p2));
  printf("eq p2 p4: %d\n", varprod_equal(p2, p3));

  printf("eq p2 p5: %d\n", varprod_equal(p2, p5));
  printf("eq p4 p2: %d\n", varprod_equal(p4, p2));
  printf("eq p4 p5: %d\n", varprod_equal(p4, p5));  

  printf("divides p1 p1: %d\n", varprod_divides(p1, p1));
  printf("divides p1 p2: %d\n", varprod_divides(p1, p2));
  printf("divides p2 p1: %d\n", varprod_divides(p2, p1));
  printf("divides p2 p3: %d\n", varprod_divides(p2, p3));
  printf("divides p2 p2: %d\n", varprod_divides(p3, p2));  
  printf("divides p2 p3: %d\n", varprod_divides(p2, p3));
  printf("divides p2 p2: %d\n", varprod_divides(p3, p2));  

  printf("divides p2 p5: %d\n", varprod_divides(p2, p5));
  printf("divides p2 p4: %d\n", varprod_divides(p2, p4));  
  printf("divides p5 p2: %d\n", varprod_divides(p5, p2));
  printf("divides p4 p2: %d\n", varprod_divides(p4, p2));  
  printf("divides p4 p5: %d\n", varprod_divides(p4, p5));
  printf("divides p5 p4: %d\n", varprod_divides(p5, p4));

  printf("\n");
  if (varprod_divisor(&buffer, p1, p3)) {
    printf("p1 divides p3\n");
    printf("divisor;\n");
    print_vpbuffer(stdout, &buffer, 10);
  } else {
    printf("p1 does not divide p3\n");
  }

  printf("\n");
  if (varprod_divisor(&buffer, p2, p3)) {
    printf("p2 divides p3\n");
    printf("divisor;\n");
    print_vpbuffer(stdout, &buffer, 10);
  } else {
    printf("p2 does not divide p3\n");
  }

  printf("\n");
  if (varprod_divisor(&buffer, p4, p5)) {
    printf("p4 divides p5\n");
    printf("divisor;\n");
    print_vpbuffer(stdout, &buffer, 10);
  } else {
    printf("p4 does not divide p5\n");
  }

  printf("\n");
  if (varprod_divisor(&buffer, p2, p5)) {
    printf("p2 divides p5\n");
    printf("divisor;\n");
    print_vpbuffer(stdout, &buffer, 10);
  } else {
    printf("p2 does not divide p5\n");
  }

  printf("\n");
  if (varprod_divisor(&buffer, p3, p4)) {
    printf("p3 divides p4\n");
    printf("divisor;\n");
    print_vpbuffer(stdout, &buffer, 10);
  } else {
    printf("p3 does not divide p4\n");
  }


  safe_free(p1);
  safe_free(p2);
  safe_free(p3);
  safe_free(p4);
  safe_free(p5);

  delete_vpbuffer(&buffer);
  return 0;
}
