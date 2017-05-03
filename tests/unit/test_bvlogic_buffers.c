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
#include <stdlib.h>
#include <inttypes.h>

#include "terms/bit_expr.h"
#include "terms/bv_constants.h"
#include "terms/bvlogic_buffers.h"
#include "utils/memalloc.h"



static node_table_t nodes;
static bvlogic_buffer_t buffer;


// Initialization
static void init(void) {
  init_node_table(&nodes, 10);
  init_bvlogic_buffer(&buffer, &nodes);
}


static void cleanup(void) {
  delete_bvlogic_buffer(&buffer);
  delete_node_table(&nodes);
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

static void print_buffer(void) {
  uint32_t i, n;

  printf("bvlogic buffer %p\n", &buffer);
  printf("  size = %"PRIu32"\n", buffer.size);
  printf("  bitsize = %"PRIu32"\n", buffer.bitsize);
  printf("  content\n");
  n = buffer.bitsize;
  for (i=0; i<n; i++) {
    printf("  bit[%"PRIu32"] = ", i);
    print_bit(buffer.bit[i]);
    printf("\n");
  }
}

int main(void) {
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
