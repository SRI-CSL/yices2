/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test pretty printer
 */

#include <stdio.h>
#include <stdint.h>
#include <gmp.h>

#include "io/yices_pp.h"
#include "terms/rationals.h"

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
  pp_char(&printer, 'X');
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
  pp_string(&printer,
	    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
	    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
	    "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc");
  pp_smt2_bv64(&printer, 0, 55);
  pp_smt2_bv64(&printer, UINT64_MAX, 55);
  pp_smt2_bv(&printer, bv, 120);
}


/*
 * List of atoms
 */
static void test_list(void) {
  pp_open_block(&printer, PP_OPEN_PAR);
  test_atoms();
  pp_close_block(&printer, true);
}


/*
 * Most lists
 */
static void test_list2(void) {
  pp_open_block(&printer, PP_OPEN_PAR);
  test_atoms();
  pp_open_block(&printer, PP_OPEN_PAR);
  test_atoms();
  pp_close_block(&printer, true);
  pp_close_block(&printer, true);

  flush_yices_pp(&printer);

  pp_open_block(&printer, PP_OPEN_PAR);
  pp_open_block(&printer, PP_OPEN_PAR);
  pp_open_block(&printer, PP_OPEN_PAR);
  pp_string(&printer,
	    "ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ"
	    "ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ");
  pp_string(&printer,
	    "YYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYY");
  pp_close_block(&printer, true);
  pp_uint32(&printer, 239094109);
  pp_uint32(&printer, 2193944);
  pp_close_block(&printer, true);
  pp_close_block(&printer, true);

  flush_yices_pp(&printer);
}


int main(void) {
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
  delete_yices_pp(&printer, true);

  printf("\n*** TEST ATOMS HVMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_HVMODE, 0);
  test_atoms();
  delete_yices_pp(&printer, true);

  printf("\n*** TEST ATOMS HMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_HMODE, 0);
  test_atoms();
  delete_yices_pp(&printer, true);

  printf("\n*** TEST LIST: VMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_VMODE, 0);
  test_list();
  delete_yices_pp(&printer, true);

  printf("\n*** TEST LIST HVMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_HVMODE, 0);
  test_list();
  delete_yices_pp(&printer, true);

  printf("\n*** TEST LIST HMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_HMODE, 0);
  test_list();
  delete_yices_pp(&printer, true);

  printf("\n*** TEST LIST: VMODE WIDE ***\n");
  area.width = 150;
  init_yices_pp(&printer, stdout, &area, PP_VMODE, 0);
  test_list();
  delete_yices_pp(&printer, true);

  area.width = 40;
  printf("\n*** TEST LIST2: VMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_VMODE, 0);
  test_list2();
  delete_yices_pp(&printer, true);

  printf("\n*** TEST LIST2 HVMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_HVMODE, 0);
  test_list2();
  delete_yices_pp(&printer, true);

  printf("\n*** TEST LIST2 HMODE ***\n");
  init_yices_pp(&printer, stdout, &area, PP_HMODE, 0);
  test_list2();
  delete_yices_pp(&printer, true);

  printf("\n*** TEST LIST2 VMODE WIDE ***\n");
  area.width = 1500;
  init_yices_pp(&printer, stdout, &area, PP_VMODE, 0);
  test_list2();
  delete_yices_pp(&printer, true);

  printf("\n");

  q_clear(&r0);
  mpq_clear(q0);
  mpz_clear(z0);
  cleanup_rationals();

  return 0;
}
