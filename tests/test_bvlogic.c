#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "bv_constants.h"
#include "bvlogic_expr.h"
#include "bit_expr.h"
#include "memalloc.h"


// mpq_aux.h defines ULONG_SIZE to 8 or 4
#include "mpq_aux.h"

#define GLOBALS 20
#define VARSIZE 16

static node_table_t manager;
static bvlogic_buffer_t buffer;
static bvlogic_expr_t *global[GLOBALS];
static bit_t v[VARSIZE];


// Initialization
static void init() {
  uint32_t i;

  for (i=0; i<GLOBALS; i++) {
    global[i] = NULL;
  }

  init_node_table(&manager, 10);
  init_bvlogic_buffer(&buffer, &manager);

  for (i=0; i<VARSIZE; i++) {
    v[i] = node_table_alloc_var(&manager, -1);
  }
}


static void cleanup() {
  uint32_t i;

  for (i=0; i<GLOBALS; i++) {
    safe_free(global[i]);
    global[i] = NULL;
  }

  delete_bvlogic_buffer(&buffer);
  delete_node_table(&manager);
}


static void print_bit(bit_t b) {
  if (b == true_bit) {
    printf("t");
  } else if (b == false_bit) {
    printf("f");
  } else {
    if (bit_is_neg(b)) printf("~");
    printf("b!%"PRId32, node_of_bit(b));
  }
}

static void print_buffer() {
  uint32_t i, n;

  printf("bvlogic buffer %p\n", &buffer);
  printf("  size = %"PRIu32"\n", buffer.size);
  printf("  nbits = %"PRIu32"\n", buffer.nbits);
  printf("  content\n");
  n = buffer.nbits;
  for (i=0; i<n; i++) {
    printf("  bit[%"PRIu32"] = ", i);
    print_bit(buffer.bit[i]);
    printf("\n");
  }
}

int main() {
  uint32_t c[2];
  uint64_t tst;

  init();
  print_buffer();
  c[0] = ~0;
  c[1] = ~0;
  bvlogic_buffer_set_constant(&buffer, 10, c);
  print_buffer();
  if (bvlogic_buffer_is_constant(&buffer)) {
    printf("Constant buffer\n");
    tst = bvlogic_buffer_get_constant64(&buffer);
    printf("value = %" PRIu64 "\n\n", tst);
  }

  bvlogic_buffer_shift_left0(&buffer, 3);
  print_buffer();
  if (bvlogic_buffer_is_constant(&buffer)) {
    printf("Constant buffer\n");
    tst = bvlogic_buffer_get_constant64(&buffer);
    printf("value = %" PRIu64 "\n\n", tst);
  }

  bvlogic_buffer_shift_right0(&buffer, 3);
  print_buffer();
  if (bvlogic_buffer_is_constant(&buffer)) {
    printf("Constant buffer\n");
    tst = bvlogic_buffer_get_constant64(&buffer);
    printf("value = %" PRIu64 "\n\n", tst);
  }

  bvlogic_buffer_rotate_left(&buffer, 0);
  print_buffer();
  if (bvlogic_buffer_is_constant(&buffer)) {
    printf("Constant buffer\n");
    tst = bvlogic_buffer_get_constant64(&buffer);
    printf("value = %" PRIu64 "\n\n", tst);
  }

  bvlogic_buffer_rotate_left(&buffer, 2);
  print_buffer();
  if (bvlogic_buffer_is_constant(&buffer)) {
    printf("Constant buffer\n");
    tst = bvlogic_buffer_get_constant64(&buffer);
    printf("value = %" PRIu64 "\n\n", tst);
  }

  bvlogic_buffer_extract_subvector(&buffer, 0, 9);
  print_buffer();
  if (bvlogic_buffer_is_constant(&buffer)) {
    printf("Constant buffer\n");
    tst = bvlogic_buffer_get_constant64(&buffer);
    printf("value = %" PRIu64 "\n\n", tst);
  }


  bvlogic_buffer_extract_subvector(&buffer, 3, 9);
  print_buffer();
  if (bvlogic_buffer_is_constant(&buffer)) {
    printf("Constant buffer\n");
    tst = bvlogic_buffer_get_constant64(&buffer);
    printf("value = %" PRIu64 "\n\n", tst);
  }


  cleanup();

  return 0;
}
