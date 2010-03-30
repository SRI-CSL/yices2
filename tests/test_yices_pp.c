/*
 * Test pretty printer
 */

#include <stdio.h>
#include <stdint.h>
#include <gmp.h>

#include "rationals.h"
#include "yices_pp.h"

// pretty printer
static yices_pp_t printer;

// default area: width = 40 columns, offset = 0, no truncate, no stretch
static pp_area_t area = {
  40, UINT32_MAX, 0, false, false,
};

// objects to print
static mpz_t z0;
static mpq_t q0;
static rational_t r0;

static uint32_t bv[4] = {
  0xAAAAAAAA, 0x55555555, 0xFFFFFFFF, 0x0000FFFF,
};


/*
 * Test the print atom functions
 */
static void test_atoms(void) {
  pp_string(&printer, "test-string");
  pp_id(&printer, "tau!", 231);
  pp_bool(&printer, true);
  pp_bool(&printer, false);
  pp_int32(&printer, 200);
  pp_int32(&printer, -1209);
  pp_uint32(&printer, 0);
  pp_uint32(&printer, UINT32_MAX);
  pp_mpz(&printer, z0);
  pp_mpq(&printer, q0);
  pp_rational(&printer, &r0);
  pp_bv64(&printer, 0, 55);
  pp_bv64(&printer, UINT64_MAX, 55);
  pp_bv(&printer, bv, 120);

}

/*
 * List of atoms
 */
static void test_list(void) {
  pp_open(&printer, PP_OPEN_PAR);
  test_atoms();
  pp_close(&printer, true);
}



int main() {  
  init_rationals();
  mpz_init(z0);
  mpz_set_str(z0, "12345678900987654321", 10);
  mpq_init(q0);
  mpq_set_str(q0, "1111111111111/431567892334", 10);
  q_init(&r0);
  q_set_int32(&r0, 123, 98765);
  
  init_yices_pp_tables();


  printf("\n*** TEST ATOMS: VMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_VMODE, 0);
  test_atoms();
  delete_yices_pp(&printer);

  printf("\n*** TEST ATOMS HVMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_HVMODE, 0);
  test_atoms();
  delete_yices_pp(&printer);

  printf("\n*** TEST ATOMS HMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_HMODE, 0);
  test_atoms();
  delete_yices_pp(&printer);

  printf("\n*** TEST LIST: VMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_VMODE, 0);
  test_list();
  delete_yices_pp(&printer);

  printf("\n*** TEST LIST HVMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_HVMODE, 0);
  test_list();
  delete_yices_pp(&printer);

  printf("\n*** TEST LIST HMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_HMODE, 0);
  test_list();
  delete_yices_pp(&printer);

  printf("\n*** TEST LIST: VMODE WIDE ***\n");
  area.width = 150;
  init_yices_pp(&printer, stdout, &area, PP_VMODE, 0);
  test_list();
  delete_yices_pp(&printer);

  printf("\n");

  q_clear(&r0);
  mpq_clear(q0);
  mpz_clear(z0);
  cleanup_rationals();

  return 0;
}
