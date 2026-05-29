/*
 * Unit tests for the pure conflict-minimization recursion core.
 */

#include <assert.h>
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
static void test_linear_redundant(void) {
  mock_graph_t m = {0};
  m.kind[1] = MCSAT_MIN_KIND_BASE;
  m.kind[2] = MCSAT_MIN_KIND_REASON;
  m.reason[2][0] = 1; m.reason_len[2] = 1;
  conflict_min_graph_t g = make_graph(&m);
  int_hmap_t marks; init_int_hmap(&marks, 0);
  bool r = conflict_min_var_is_removable(&g, &marks, 2, 0, 1000);
  assert(r == true);
  delete_int_hmap(&marks);
  printf("test_linear_redundant: PASS\n");
}

/* v2's reason is {v1}, v1 is a decision => v2 NOT removable. */
static void test_decision_blocks(void) {
  mock_graph_t m = {0};
  m.kind[1] = MCSAT_MIN_KIND_DECISION;
  m.kind[2] = MCSAT_MIN_KIND_REASON;
  m.reason[2][0] = 1; m.reason_len[2] = 1;
  conflict_min_graph_t g = make_graph(&m);
  int_hmap_t marks; init_int_hmap(&marks, 0);
  bool r = conflict_min_var_is_removable(&g, &marks, 2, 0, 1000);
  assert(r == false);
  delete_int_hmap(&marks);
  printf("test_decision_blocks: PASS\n");
}

/* v2's reason is {v1}, v1 is a theory propagation (no clausal reason) => fail. */
static void test_theory_boundary(void) {
  mock_graph_t m = {0};
  m.kind[1] = MCSAT_MIN_KIND_NO_REASON;
  m.kind[2] = MCSAT_MIN_KIND_REASON;
  m.reason[2][0] = 1; m.reason_len[2] = 1;
  conflict_min_graph_t g = make_graph(&m);
  int_hmap_t marks; init_int_hmap(&marks, 0);
  bool r = conflict_min_var_is_removable(&g, &marks, 2, 0, 1000);
  assert(r == false);
  delete_int_hmap(&marks);
  printf("test_theory_boundary: PASS\n");
}

/* v2's reason is {v1}, v1 pre-seeded KEEP (an anchor disjunct) => v2 removable. */
static void test_keep_anchor(void) {
  mock_graph_t m = {0};
  m.kind[1] = MCSAT_MIN_KIND_NO_REASON; /* would fail if not for the KEEP mark */
  m.kind[2] = MCSAT_MIN_KIND_REASON;
  m.reason[2][0] = 1; m.reason_len[2] = 1;
  conflict_min_graph_t g = make_graph(&m);
  int_hmap_t marks; init_int_hmap(&marks, 0);
  int_hmap_add(&marks, 1, MCSAT_MIN_MARK_KEEP);
  bool r = conflict_min_var_is_removable(&g, &marks, 2, 0, 1000);
  assert(r == true);
  delete_int_hmap(&marks);
  printf("test_keep_anchor: PASS\n");
}

/* Chain v3->v2->v1->v0(base); max_depth=1 cuts it off => v3 NOT removable. */
static void test_depth_limit(void) {
  mock_graph_t m = {0};
  m.kind[0] = MCSAT_MIN_KIND_BASE;
  m.kind[1] = MCSAT_MIN_KIND_REASON; m.reason[1][0] = 0; m.reason_len[1] = 1;
  m.kind[2] = MCSAT_MIN_KIND_REASON; m.reason[2][0] = 1; m.reason_len[2] = 1;
  m.kind[3] = MCSAT_MIN_KIND_REASON; m.reason[3][0] = 2; m.reason_len[3] = 1;
  conflict_min_graph_t g = make_graph(&m);
  int_hmap_t marks; init_int_hmap(&marks, 0);
  bool r = conflict_min_var_is_removable(&g, &marks, 3, 0, 1);
  assert(r == false);
  delete_int_hmap(&marks);
  printf("test_depth_limit: PASS\n");
}

int main(void) {
  test_linear_redundant();
  test_decision_blocks();
  test_theory_boundary();
  test_keep_anchor();
  test_depth_limit();
  printf("All conflict_minimize core tests passed.\n");
  return 0;
}
