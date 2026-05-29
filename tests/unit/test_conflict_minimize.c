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

/*
 * Unit tests for the pure conflict-minimization recursion core.
 */

#include <stdio.h>
#include <stdbool.h>

#include "mcsat/conflict_minimize.h"
#include "utils/int_hash_map.h"
#include "utils/int_vectors.h"

/*
 * Synthetic reason graph: kind[v] gives the classification, reasons[v] gives
 * the reason-clause variables (used only when kind[v] == REASON).
 */
#define MAX_V 16

typedef struct {
  int kind[MAX_V];
  int reason[MAX_V][MAX_V];
  int reason_len[MAX_V];
} mock_graph_t;

static int mock_classify(void* data, variable_t v) {
  mock_graph_t* g = (mock_graph_t*) data;
  return g->kind[v];
}

static void mock_reason_vars(void* data, variable_t v, ivector_t* out) {
  mock_graph_t* g = (mock_graph_t*) data;
  for (int i = 0; i < g->reason_len[v]; ++i) {
    ivector_push(out, g->reason[v][i]);
  }
}

static conflict_min_graph_t make_graph(mock_graph_t* m) {
  conflict_min_graph_t g;
  g.classify = mock_classify;
  g.reason_vars = mock_reason_vars;
  g.data = m;
  return g;
}

/* v2's reason is {v1}, v1 is base-level => v2 removable. */
static int test_linear_redundant(void) {
  mock_graph_t m = {0};
  m.kind[1] = MCSAT_MIN_KIND_BASE;
  m.kind[2] = MCSAT_MIN_KIND_REASON;
  m.reason[2][0] = 1; m.reason_len[2] = 1;
  conflict_min_graph_t g = make_graph(&m);
  int_hmap_t marks; init_int_hmap(&marks, 0);
  bool r = conflict_min_var_is_removable(&g, &marks, 2, 0, 1000);
  if (r != true) {
    fprintf(stderr, "FAIL: test_linear_redundant (expected true, got %d)\n", (int) r);
    delete_int_hmap(&marks);
    return 1;
  }
  delete_int_hmap(&marks);
  printf("test_linear_redundant: PASS\n");
  return 0;
}

/* v2's reason is {v1}, v1 is a decision => v2 NOT removable. */
static int test_decision_blocks(void) {
  mock_graph_t m = {0};
  m.kind[1] = MCSAT_MIN_KIND_DECISION;
  m.kind[2] = MCSAT_MIN_KIND_REASON;
  m.reason[2][0] = 1; m.reason_len[2] = 1;
  conflict_min_graph_t g = make_graph(&m);
  int_hmap_t marks; init_int_hmap(&marks, 0);
  bool r = conflict_min_var_is_removable(&g, &marks, 2, 0, 1000);
  if (r != false) {
    fprintf(stderr, "FAIL: test_decision_blocks (expected false, got %d)\n", (int) r);
    delete_int_hmap(&marks);
    return 1;
  }
  delete_int_hmap(&marks);
  printf("test_decision_blocks: PASS\n");
  return 0;
}

/* v2's reason is {v1}, v1 is a theory propagation (no clausal reason) => fail. */
static int test_theory_boundary(void) {
  mock_graph_t m = {0};
  m.kind[1] = MCSAT_MIN_KIND_NO_REASON;
  m.kind[2] = MCSAT_MIN_KIND_REASON;
  m.reason[2][0] = 1; m.reason_len[2] = 1;
  conflict_min_graph_t g = make_graph(&m);
  int_hmap_t marks; init_int_hmap(&marks, 0);
  bool r = conflict_min_var_is_removable(&g, &marks, 2, 0, 1000);
  if (r != false) {
    fprintf(stderr, "FAIL: test_theory_boundary (expected false, got %d)\n", (int) r);
    delete_int_hmap(&marks);
    return 1;
  }
  delete_int_hmap(&marks);
  printf("test_theory_boundary: PASS\n");
  return 0;
}

/* v2's reason is {v1}, v1 pre-seeded KEEP (an anchor disjunct) => v2 removable. */
static int test_keep_anchor(void) {
  mock_graph_t m = {0};
  m.kind[1] = MCSAT_MIN_KIND_NO_REASON; /* would fail if not for the KEEP mark */
  m.kind[2] = MCSAT_MIN_KIND_REASON;
  m.reason[2][0] = 1; m.reason_len[2] = 1;
  conflict_min_graph_t g = make_graph(&m);
  int_hmap_t marks; init_int_hmap(&marks, 0);
  int_hmap_add(&marks, 1, MCSAT_MIN_MARK_KEEP);
  bool r = conflict_min_var_is_removable(&g, &marks, 2, 0, 1000);
  if (r != true) {
    fprintf(stderr, "FAIL: test_keep_anchor (expected true, got %d)\n", (int) r);
    delete_int_hmap(&marks);
    return 1;
  }
  delete_int_hmap(&marks);
  printf("test_keep_anchor: PASS\n");
  return 0;
}

/* Chain v3->v2->v1->v0(base); max_depth=1 cuts it off => v3 NOT removable. */
static int test_depth_limit(void) {
  mock_graph_t m = {0};
  m.kind[0] = MCSAT_MIN_KIND_BASE;
  m.kind[1] = MCSAT_MIN_KIND_REASON; m.reason[1][0] = 0; m.reason_len[1] = 1;
  m.kind[2] = MCSAT_MIN_KIND_REASON; m.reason[2][0] = 1; m.reason_len[2] = 1;
  m.kind[3] = MCSAT_MIN_KIND_REASON; m.reason[3][0] = 2; m.reason_len[3] = 1;
  conflict_min_graph_t g = make_graph(&m);
  int_hmap_t marks; init_int_hmap(&marks, 0);
  bool r = conflict_min_var_is_removable(&g, &marks, 3, 0, 1);
  if (r != false) {
    fprintf(stderr, "FAIL: test_depth_limit (expected false, got %d)\n", (int) r);
    delete_int_hmap(&marks);
    return 1;
  }
  delete_int_hmap(&marks);
  printf("test_depth_limit: PASS\n");
  return 0;
}

/* Diamond: v3's reason is {v1, v2}, both base-level => v3 removable
 * (every branch of a multi-literal reason must succeed). */
static int test_diamond(void) {
  mock_graph_t m = {0};
  m.kind[1] = MCSAT_MIN_KIND_BASE;
  m.kind[2] = MCSAT_MIN_KIND_BASE;
  m.kind[3] = MCSAT_MIN_KIND_REASON;
  m.reason[3][0] = 1; m.reason[3][1] = 2; m.reason_len[3] = 2;
  conflict_min_graph_t g = make_graph(&m);
  int_hmap_t marks; init_int_hmap(&marks, 0);
  bool r = conflict_min_var_is_removable(&g, &marks, 3, 0, 1000);
  if (r != true) {
    fprintf(stderr, "FAIL: test_diamond (expected true, got %d)\n", (int) r);
    delete_int_hmap(&marks);
    return 1;
  }
  delete_int_hmap(&marks);
  printf("test_diamond: PASS\n");
  return 0;
}

/* Diamond with one decision branch: v3's reason is {v1(base), v2(decision)}
 * => v3 NOT removable (one failing branch poisons the whole). */
static int test_diamond_one_decision(void) {
  mock_graph_t m = {0};
  m.kind[1] = MCSAT_MIN_KIND_BASE;
  m.kind[2] = MCSAT_MIN_KIND_DECISION;
  m.kind[3] = MCSAT_MIN_KIND_REASON;
  m.reason[3][0] = 1; m.reason[3][1] = 2; m.reason_len[3] = 2;
  conflict_min_graph_t g = make_graph(&m);
  int_hmap_t marks; init_int_hmap(&marks, 0);
  bool r = conflict_min_var_is_removable(&g, &marks, 3, 0, 1000);
  if (r != false) {
    fprintf(stderr, "FAIL: test_diamond_one_decision (expected false, got %d)\n", (int) r);
    delete_int_hmap(&marks);
    return 1;
  }
  delete_int_hmap(&marks);
  printf("test_diamond_one_decision: PASS\n");
  return 0;
}

/* Cross-candidate memoization reuse over a SHARED marks map: first prove v1
 * removable (it gets a REMOVABLE mark), then v2 whose reason is {v1} must be
 * removable by anchoring on v1's REMOVABLE mark (success terminal). */
static int test_removable_reuse(void) {
  mock_graph_t m = {0};
  m.kind[0] = MCSAT_MIN_KIND_BASE;
  m.kind[1] = MCSAT_MIN_KIND_REASON; m.reason[1][0] = 0; m.reason_len[1] = 1;
  m.kind[2] = MCSAT_MIN_KIND_REASON; m.reason[2][0] = 1; m.reason_len[2] = 1;
  conflict_min_graph_t g = make_graph(&m);
  int_hmap_t marks; init_int_hmap(&marks, 0);
  bool r1 = conflict_min_var_is_removable(&g, &marks, 1, 0, 1000);
  bool r2 = conflict_min_var_is_removable(&g, &marks, 2, 0, 1000);
  if (r1 != true || r2 != true) {
    fprintf(stderr, "FAIL: test_removable_reuse (expected true/true, got %d/%d)\n",
            (int) r1, (int) r2);
    delete_int_hmap(&marks);
    return 1;
  }
  delete_int_hmap(&marks);
  printf("test_removable_reuse: PASS\n");
  return 0;
}

int main(void) {
  int fails = 0;
  fails += test_linear_redundant();
  fails += test_decision_blocks();
  fails += test_theory_boundary();
  fails += test_keep_anchor();
  fails += test_depth_limit();
  fails += test_diamond();
  fails += test_diamond_one_decision();
  fails += test_removable_reuse();
  if (fails != 0) {
    fprintf(stderr, "%d conflict_minimize core test(s) FAILED.\n", fails);
    return 1;
  }
  printf("All conflict_minimize core tests passed.\n");
  return 0;
}
