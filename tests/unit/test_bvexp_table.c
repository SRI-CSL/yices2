/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>

#include "solvers/bv/bv_vartable.h"
#include "solvers/bv/bvexp_table.h"
#include "solvers/bv/bvsolver_printer.h"


/*
 * Print the polynomial attached to variable x in table
 */
static void print_def(FILE *f, bvexp_table_t *table, thvar_t x) {
  bv_vartable_t *vtbl;
  void *def;
  uint32_t n;

  vtbl = table->vtbl;
  n = bvvar_bitsize(vtbl, x);
  def = bvexp_get_def(table, x);

  print_bv_solver_var(f, NULL, x);
  fputs(" = ", f);
  if (def == NULL) {
    fputs("<none>", f);
  } else if (n <= 64) {
    print_bvexp64(f, def, n);
  } else {
    print_bvexp(f, def, n);
  }
  fputc('\n', f);
}



/*
 * Print the content of table
 */
static void print_bvexp_table(FILE *f, bvexp_table_t *table) {
  uint32_t i, n;


  n = table->nvars;
  fprintf(f, "Table %p: %"PRIu32" variables\n", table, n);
  for (i=1; i<n; i++) {
    print_def(f, table, i);
  }
  fputs("----\n", f);
}




/*
 * Test: check whether b is present in the table
 * if not add it
 */
static void test_buffer64(bvexp_table_t *table, bvarith64_buffer_t *b) {
  bvmlist64_t *p;
  thvar_t x;
  uint32_t h, n;

  printf("=== test64 ===\n");
  n = b->bitsize;

  printf("poly = ");
  print_bvexp64(stdout, b->list, n);
  printf("\n");

  h = hash_bvmlist64(b->list, n);
  printf("hash code = %"PRIu32"\n", h);

  x = bvexp_table_find64(table, b, h);
  if (x < 0) {
    printf("not in table\n");
    x = make_bvvar(table->vtbl, n);
    bvexp_table_add64(table, x, b, h);
    printf("adding variable: ");
    print_def(stdout, table, x);
  } else {
    printf("found matching variable: ");
    print_def(stdout, table, x);
    p = bvexp_def64(table, x);
    if (p == NULL || !equal_bvmlists64(b->list, p) || bvvar_bitsize(table->vtbl, x) != n) {
      printf("BUG\n");
      exit(1);
    }
  }
  printf("\n");
}


static void test_buffer(bvexp_table_t *table, bvarith_buffer_t *b) {
  bvmlist_t *p;
  thvar_t x;
  uint32_t h, n;

  printf("=== test ===\n");
  n = b->bitsize;

  printf("poly = ");
  print_bvexp(stdout, b->list, n);
  printf("\n");

  h = hash_bvmlist(b->list, n);
  printf("hash code = %"PRIu32"\n", h);

  x = bvexp_table_find(table, b, h);
  if (x < 0) {
    printf("not in table\n");
    x = make_bvvar(table->vtbl, n);
    bvexp_table_add(table, x, b, h);
    printf("adding variable: ");
    print_def(stdout, table, x);
  } else {
    printf("found matching variable: ");
    print_def(stdout, table, x);
    p = bvexp_def(table, x);
    if (p == NULL || !equal_bvmlists(b->list, p, n) || bvvar_bitsize(table->vtbl, x) != n) {
      printf("BUG\n");
      exit(1);
    }
  }
  printf("\n");
}



/*
 * Global variables for testing
 */
static bv_vartable_t vtbl;
static bvexp_table_t table;
static bvarith64_buffer_t b1, b2;
static bvarith_buffer_t c1, c2;


int main(void) {
  thvar_t x, y, z;

  init_bvconstants();
  init_bv_vartable(&vtbl);
  init_bvexp_table(&table, &vtbl);
  bvexp_init_buffer64(&table, &b1);
  bvexp_init_buffer64(&table, &b2);
  bvexp_init_buffer(&table, &c1);
  bvexp_init_buffer(&table, &c2);

  printf("=== Initial table ===\n");
  print_bvexp_table(stdout, &table);
  printf("\n");

  x = make_bvvar(&vtbl, 10);
  y = make_bvvar(&vtbl, 10);
  z = make_bvvar(&vtbl, 10);

  // 2 + x + y
  bvarith64_buffer_prepare(&b1, 10);
  bvarith64_buffer_add_const(&b1, 2);
  bvarith64_buffer_add_var(&b1, x);
  bvarith64_buffer_add_var(&b1, y);
  bvarith64_buffer_normalize(&b1);
  test_buffer64(&table, &b1);

  bvarith64_buffer_prepare(&b1, 10);
  bvarith64_buffer_add_const(&b1, 2);
  bvarith64_buffer_add_var(&b1, x);
  bvarith64_buffer_add_var(&b1, y);
  bvarith64_buffer_normalize(&b1);
  test_buffer64(&table, &b1);

  // (x + z) * (y - z)
  bvarith64_buffer_prepare(&b1, 10);
  bvarith64_buffer_add_var(&b1, x);
  bvarith64_buffer_add_var(&b1, z);
  bvarith64_buffer_prepare(&b2, 10);
  bvarith64_buffer_add_var(&b2, y);
  bvarith64_buffer_sub_var(&b2, z);
  bvarith64_buffer_mul_buffer(&b1, &b2);
  bvarith64_buffer_normalize(&b1);
  test_buffer64(&table, &b1);

  bvarith64_buffer_prepare(&b1, 10);
  bvarith64_buffer_add_var(&b1, x);
  bvarith64_buffer_add_var(&b1, z);
  bvarith64_buffer_prepare(&b2, 10);
  bvarith64_buffer_add_var(&b2, y);
  bvarith64_buffer_sub_var(&b2, z);
  bvarith64_buffer_mul_buffer(&b1, &b2);
  bvarith64_buffer_normalize(&b1);
  test_buffer64(&table, &b1);

  // x * y * z^2
  bvarith64_buffer_prepare(&b1, 10);
  bvarith64_buffer_add_var(&b1, z);
  bvarith64_buffer_square(&b1);
  bvarith64_buffer_mul_var(&b1, y);
  bvarith64_buffer_mul_var(&b1, x);
  bvarith64_buffer_normalize(&b1);
  test_buffer64(&table, &b1);

  bvarith64_buffer_prepare(&b1, 10);
  bvarith64_buffer_add_var(&b1, z);
  bvarith64_buffer_square(&b1);
  bvarith64_buffer_mul_var(&b1, y);
  bvarith64_buffer_mul_var(&b1, x);
  bvarith64_buffer_normalize(&b1);
  test_buffer64(&table, &b1);


  // Large coefficients
  x = make_bvvar(&vtbl, 100);
  y = make_bvvar(&vtbl, 100);
  z = make_bvvar(&vtbl, 100);


  // 1 + x + y
  bvarith_buffer_prepare(&c1, 100);
  bvarith_buffer_set_one(&c1);
  bvarith_buffer_add_var(&c1, x);
  bvarith_buffer_add_var(&c1, y);
  bvarith_buffer_normalize(&c1);
  test_buffer(&table, &c1);

  bvarith_buffer_prepare(&c1, 100);
  bvarith_buffer_set_one(&c1);
  bvarith_buffer_add_var(&c1, x);
  bvarith_buffer_add_var(&c1, y);
  bvarith_buffer_normalize(&c1);
  test_buffer(&table, &c1);

  // (x + z) * (y - z)
  bvarith_buffer_prepare(&c1, 100);
  bvarith_buffer_add_var(&c1, x);
  bvarith_buffer_add_var(&c1, z);
  bvarith_buffer_prepare(&c2, 100);
  bvarith_buffer_add_var(&c2, y);
  bvarith_buffer_sub_var(&c2, z);
  bvarith_buffer_mul_buffer(&c1, &c2);
  bvarith_buffer_normalize(&c1);
  test_buffer(&table, &c1);

  bvarith_buffer_prepare(&c1, 100);
  bvarith_buffer_add_var(&c1, x);
  bvarith_buffer_add_var(&c1, z);
  bvarith_buffer_prepare(&c2, 100);
  bvarith_buffer_add_var(&c2, y);
  bvarith_buffer_sub_var(&c2, z);
  bvarith_buffer_mul_buffer(&c1, &c2);
  bvarith_buffer_normalize(&c1);
  test_buffer(&table, &c1);

  // x * y * z^2
  bvarith_buffer_prepare(&c1, 100);
  bvarith_buffer_add_var(&c1, z);
  bvarith_buffer_square(&c1);
  bvarith_buffer_mul_var(&c1, y);
  bvarith_buffer_mul_var(&c1, x);
  bvarith_buffer_normalize(&c1);
  test_buffer(&table, &c1);

  bvarith_buffer_prepare(&c1, 100);
  bvarith_buffer_add_var(&c1, z);
  bvarith_buffer_square(&c1);
  bvarith_buffer_mul_var(&c1, y);
  bvarith_buffer_mul_var(&c1, x);
  bvarith_buffer_normalize(&c1);
  test_buffer(&table, &c1);

  printf("=== Final table ===\n");
  print_bvexp_table(stdout, &table);
  printf("\n");


  // remove two variables
  bvexp_table_remove_vars(&table, 11);
  printf("=== After removing two variables ===\n");
  print_bvexp_table(stdout, &table);
  printf("\n");

  // recheck: 1 + x + y
  bvarith_buffer_prepare(&c1, 100);
  bvarith_buffer_set_one(&c1);
  bvarith_buffer_add_var(&c1, x);
  bvarith_buffer_add_var(&c1, y);
  bvarith_buffer_normalize(&c1);
  test_buffer(&table, &c1);

  // recheck: (x + z) * (y - z)
  bvarith_buffer_prepare(&c1, 100);
  bvarith_buffer_add_var(&c1, x);
  bvarith_buffer_add_var(&c1, z);
  bvarith_buffer_prepare(&c2, 100);
  bvarith_buffer_add_var(&c2, y);
  bvarith_buffer_sub_var(&c2, z);
  bvarith_buffer_mul_buffer(&c1, &c2);
  bvarith_buffer_normalize(&c1);
  test_buffer(&table, &c1);

  bvarith_buffer_prepare(&c1, 100);
  bvarith_buffer_add_var(&c1, x);
  bvarith_buffer_add_var(&c1, z);
  bvarith_buffer_prepare(&c2, 100);
  bvarith_buffer_add_var(&c2, y);
  bvarith_buffer_sub_var(&c2, z);
  bvarith_buffer_mul_buffer(&c1, &c2);
  bvarith_buffer_normalize(&c1);
  test_buffer(&table, &c1);

  printf("=== Final table ===\n");
  print_bvexp_table(stdout, &table);
  printf("\n");



  // cleanup
  delete_bvarith64_buffer(&b1);
  delete_bvarith64_buffer(&b2);
  delete_bvarith_buffer(&c1);
  delete_bvarith_buffer(&c2);
  delete_bvexp_table(&table);
  delete_bv_vartable(&vtbl);
  cleanup_bvconstants();

  return 0;
}
