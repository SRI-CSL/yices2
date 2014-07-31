/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test the string-parsing functions in bv64_constants.
 */


/*
 * Force assert to work even if compiled with debug disabled
 */
#ifdef NDEBUG
# undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>

#include "terms/bv64_constants.h"


/*
 * Test binary format:
 * - n = number of bits
 * - s = array of chars (must be large enough for n+1 characters)
 */
static void test_parse_bvbin(uint32_t n, char *s) {
  int32_t code;
  uint64_t test, check;
  uint32_t i;

  assert(0 < n && n <= 64);

  s[n] = '\0';

  // all zero
  for (i=0; i<n; i++) {
    s[i] = '0';
  }
  check = 0;
  code = bvconst64_set_from_string(&test, n, s);
  assert(code == 0 && test == check);

  // all ones
  for (i=0; i<n; i++) {
    s[i] = '1';
  }
  check = mask64(n); // 000111...11
  code = bvconst64_set_from_string(&test, n, s);
  assert(code == 0 && test == check);

  /*
   * Set one bit is 1, all others to zero.
   * Starting with the high-order bit.
   */
  for (i=0; i<n; i++) {
    s[i] = '0';
  }

  check = 1;
  check <<= n-1;
  for (i=0; i<n; i++) {
    // set s[i] to '1'
    s[i] = '1';
    code = bvconst64_set_from_string(&test, n, s);
    assert(code == 0 && test == check);
    s[i] = '0';
    check >>= 1;
  }


  /*
   * Test error code
   */
  s[n-1] = 'x';
  test = 0x98765432;
  check = test;
  code = bvconst64_set_from_string(&test, n, s);
  assert(code == -1 && test == check); // test should not change

  printf("PASS: %s with n = %"PRIu32"\n", __func__, n);
  fflush(stdout);
}




/*
 * Test hexadecimal format
 * - n = number of characters
 * - s = array of chars (large enough for n+1 characters)
 */
static void test_parse_bvhex(uint32_t n, char *s) {
  int32_t code;
  uint64_t test, check;
  uint32_t i;

  assert(0 < n && n <= 16);

  s[n] = '\0';

  // all zero
  for (i=0; i<n; i++) {
    s[i] = '0';
  }
  check = 0;
  code = bvconst64_set_from_hexa_string(&test, n, s);
  assert(code == 0 && test == check);

  // all ones
  for (i=0; i<n; i++) {
    s[i] = 'f';
  }
  check = mask64(4 * n);
  code = bvconst64_set_from_hexa_string(&test, n, s);
  assert(code == 0 && test == check);

  // all ones: upper case
  for (i=0; i<n; i++) {
    s[i] = 'F';
  }
  check = mask64(4 * n);
  code = bvconst64_set_from_hexa_string(&test, n, s);
  assert(code == 0 && test == check);


  /*
   * Set one digit to '9' all others to '0',
   * starting with the high-order bit.
   */
  for (i=0; i<n; i++) {
    s[i] = '0';
  }

  check = ((uint64_t) 9) << (4 * (n-1));
  for (i=0; i<n; i++) {
    s[i] = '9';
    code = bvconst64_set_from_hexa_string(&test, n, s);
    assert(code == 0 && test == check);
    s[i] = '0';
    check >>= 4;
  }


  /*
   * Set one digit to 'C' all others to '0',
   * starting with the high-order bit.
   */
  for (i=0; i<n; i++) {
    s[i] = '0';
  }

  check = ((uint64_t) 0xE) << (4 * (n-1));
  for (i=0; i<n; i++) {
    s[i] = 'e';
    code = bvconst64_set_from_hexa_string(&test, n, s);
    assert(code == 0 && test == check);
    s[i] = '0';
    check >>= 4;
  }


  /*
   * Set one digit to 'e' all others to '0',
   * starting with the high-order bit.
   */
  for (i=0; i<n; i++) {
    s[i] = '0';
  }

  check = ((uint64_t) 0xC) << (4 * (n-1));
  for (i=0; i<n; i++) {
    s[i] = 'C';
    code = bvconst64_set_from_hexa_string(&test, n, s);
    assert(code == 0 && test == check);
    s[i] = '0';
    check >>= 4;
  }


  /*
   * Test error code
   */
  s[n-1] = 'x';
  test = 0x98765432;
  check = test;
  code = bvconst64_set_from_hexa_string(&test, n, s);
  assert(code == -1 && test == check); // test should not change

  printf("PASS: %s with n = %"PRIu32"\n", __func__, n);
  fflush(stdout);
}





/*
 * Global buffer
 */
static char buffer[65];


int main(void) {
  uint32_t i;

  for (i=1; i<=64; i++) {
    test_parse_bvbin(i, buffer);
  }

  for (i=1; i<=16; i++) {
    test_parse_bvhex(i, buffer);
  }

  return 0;
}
