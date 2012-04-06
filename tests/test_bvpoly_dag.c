/*
 * DAG of bitvector polynomial expressions
 */

#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

#include "bv64_constants.h"
#include "bv_constants.h"
#include "index_vectors.h"

#include "bvpoly_dag.h"


/*
 * Print a node occurrence n
 */
static void print_nocc(FILE *f, node_occ_t n) {
  if (sign_of_occ(n) == 0) {
    fprintf(f, "+n%"PRId32, (n>>1));
  } else {
    fprintf(f, "-n%"PRId32, (n>>1));
  }
}

// variable occurrence x
static void print_vocc(FILE *f, int32_t x) {
  if (sign_of_occ(x) == 0) {
    fprintf(f, "+u!%"PRId32, (x>>1));
  } else {
    fprintf(f, "-u!%"PRId32, (x>>1));
  }
}


/*
 * 64bit coefficient, n = number of bits
 */
static void print_bvconst64(FILE *f, uint64_t c, uint32_t n) {
  if (c == 1) {
    fputc('1', f);
  } else if (bvconst64_is_minus_one(c, n)) {
    fputs("-1", f);
  } else {
    bvconst64_print(f, c, n);
  }
}


/*
 * Print a node in the dag
 */
static void print_map(FILE *f, int32_t x) {
  if (x < 0) {
    fprintf(f, "not mapped");
  } else {
    fprintf(f, "mapped to ");
    print_vocc(f, x);
  }
}

static void print_leaf_node(FILE *f, bvc_leaf_t *d) {
  fprintf(f, "[LEAF ");
  print_map(f, d->header.map);
  fprintf(f, " (%"PRIu32" bits)]", d->header.bitsize);
}

static void print_offset_node(FILE *f, bvc_offset_t *d) {
  uint32_t n;

  n = d->header.bitsize;
  fprintf(f, "[OFFSET ");
  if (n <= 64) {
    bvconst64_print(f, d->constant.c, n);
  } else { 
    bvconst_print(f, d->constant.w, n);
  }
  fputc(' ', f);
  print_nocc(f, d->nocc);
  fputc(' ', f);
  print_map(f, d->header.map);
  fprintf(f, " (%"PRIu32" bits)]", n);
}

static void print_mono_node(FILE *f, bvc_mono_t *d) {
  uint32_t n;

  n = d->header.bitsize;
  fprintf(f, "[MONO ");
  if (n <= 64) {
    bvconst64_print(f, d->coeff.c, n);
  } else { 
    bvconst_print(f, d->coeff.w, n);
  }
  fputc(' ', f);
  print_nocc(f, d->nocc);
  fputc(' ', f);
  print_map(f, d->header.map);
  fprintf(f, " (%"PRIu32" bits)]", n);
}

static void print_prod_node(FILE *f, bvc_prod_t *d) {
  uint32_t i, n;

  fprintf(f, "[PROD" );
  n = d->len;
  for (i=0; i<n; i++) {
    fputc(' ', f);
    print_nocc(f, d->prod[i].var);
    if (d->prod[i].exp > 1) {
      fprintf(f, "^%"PRId32, d->prod[i].exp);
    }
  }
  fputc(' ', f);
  print_map(f, d->header.map);
  fprintf(f, " (%"PRIu32" bits)]", d->header.bitsize);  
}

static void print_sum_node(FILE *f, bvc_sum_t *d) {
  uint32_t i, n;

  fprintf(f, "[SUM" );
  n = d->len;
  for (i=0; i<n; i++) {
    fputc(' ', f);
    print_nocc(f, d->sum[i]);
  }
  fputc(' ', f);
  print_map(f, d->header.map);
  fprintf(f, " (%"PRIu32" bits)]", d->header.bitsize);    
}

static void print_node_descriptor(FILE *f, bvc_header_t *d) {
  switch (d->tag) {
  case BVC_LEAF:
    print_leaf_node(f, leaf_node(d));
    break;

  case BVC_OFFSET:
    print_offset_node(f, offset_node(d));
    break;

  case BVC_MONO:
    print_mono_node(f, mono_node(d));
    break;

  case BVC_PROD:
    print_prod_node(f, prod_node(d));
    break;

  case BVC_SUM:    
    print_sum_node(f, sum_node(d));
    break;

  default:
    assert(false);
    break;
  }
}


/*
 * Use list a
 */
static void print_use_list(FILE *f, int32_t *a) {
  uint32_t i, n;

  if (a == NULL) {
    fprintf(f, "nil");
  } else {
    n = iv_size(a);
    fprintf(f, "(");
    for (i=0; i<n; i++) {
      if (i > 0) fputc(' ', f);
      fprintf(f, "n%"PRId32, a[i]);
    }
    fprintf(f, ")");
  }
}


/*
 * Print details of node q
 */
static void print_node(FILE *f, bvc_dag_t *dag, node_t q) {
  assert(0 < q && q <= dag->nelems);

  fprintf(f, "Node n%"PRId32"\n", q);
  fprintf(f, "   ");
  print_node_descriptor(f, dag->desc[q]);
  fprintf(f, "\n");
  fprintf(f, "   use list: ");
  print_use_list(f, dag->use[q]);  
  fprintf(f, "\n");
}



/*
 * Print a list of nodes: k = list header
 */
static void print_list(FILE *f, bvc_dag_t *dag, int32_t k) {
  int32_t i;

  i = dag->list[k].next;
  while (i != k) {
    fprintf(f, " n%"PRId32, i);
    i = dag->list[i].next;
  }
}


/*
 * Print dag
 */
static void print_dag(FILE *f, bvc_dag_t *dag) {
  uint32_t i, n;

  n = dag->nelems;
  fprintf(f, "DAG %p: %"PRIu32" nodes\n", dag, n);
  for (i=1; i <= n; i++) {
    print_node(f, dag, i);
  }

  fprintf(f, "Leaf nodes:");
  print_list(f, dag, BVC_DAG_LEAF_LIST);
  fprintf(f, "\n");
  
  fprintf(f, "Elementary nodes:");
  print_list(f, dag, BVC_DAG_ELEM_LIST);
  fprintf(f, "\n");
  
  fprintf(f, "Other nodes:");
  print_list(f, dag, BVC_DAG_DEFAULT_LIST);
  fprintf(f, "\n");
  
  fflush(f);
}



/*
 * Test leaf constructor
 * - b = bitsize
 * - v = variable
 */
static node_occ_t test_leaf(bvc_dag_t *dag, int32_t v, uint32_t b) {
  bvc_leaf_t *d;
  node_occ_t r;
  node_t q;

  r = bvc_dag_leaf(dag, v, b);
  q = r >> 1;

  printf("---> created leaf node n!%"PRId32" for var %"PRId32" (%"PRIu32" bits)\n", q, v, b);
  if (sign_of_occ(r) == 0 && bvc_dag_var_is_present(dag, v) &&
      bvc_dag_nocc_of_var(dag, v) == r && bvc_dag_node_is_leaf(dag, q)) {
    d = bvc_dag_node_leaf(dag, q);
    if (d->header.map != (v << 1) || d->header.bitsize != b) {
      goto error;
    }      
  } else {
    goto error;
  }	

  return r;
  
 error:
  printf("---> ERROR\n");
  fflush(stdout);
  exit(1);

}


/*
 * Test monomial constructor (64bit version) for (a * r)
 * - b = bitsize
 */
static node_occ_t test_mono64(bvc_dag_t *dag, uint64_t a, node_occ_t r, uint32_t b) {
  bvc_mono_t *d;
  node_occ_t tst, chk;
  node_t q;
  uint32_t sign;

  assert(1 <= b && b <= 64);
  a = norm64(a, b);
  tst = bvc_dag_mono64(dag, -1, a, r, b);
  chk = bvc_dag_mono64(dag, -1, a, r, b);

  sign = sign_of_occ(tst);
  q = tst >> 1;

  printf("---> got ");
  print_nocc(stdout, tst);
  printf(" for ");
  print_bvconst64(stdout, a, b);
  printf(" * ");
  print_nocc(stdout, r);
  printf(" (%"PRIu32" bits)\n", b);

  if (tst != chk) {
    printf("---> ERROR: Hash-consing failed\n");
    fflush(stdout);
    exit(1);
  }
  
  if (a == 1) {
    if (tst != r) goto error;
  } else if (a == mask64(b)) {
    if (tst != (r ^ 1)) goto error;
  } else {
    if (! bvc_dag_node_is_mono(dag, q)) goto error;
    d = bvc_dag_node_mono(dag, q);
    if (d->header.bitsize != b) goto error;

    if (sign_of_occ(r) == 0) {
      if (d->nocc != r || 
	  (sign == 0 && d->coeff.c != a) ||
	  (sign == 1 && d->coeff.c != norm64(-a, b))) {
	goto error;
      }
    } else {
      if (d->nocc != (r^1) ||
	  (sign == 0 && d->coeff.c != norm64(-a, b)) ||
	  (sign == 1 && d->coeff.c != a)) {
	goto error;
      }
    }
  }

  return tst;

 error:
  printf("---> ERROR\n");
  fflush(stdout);
  exit(1);
}


/*
 * TEST: create n leaves for variables u!t to u!(t+n)
 * - b = bitsize
 * - store the resulting node occurrences in array a
 */
static void test_make_leaves(bvc_dag_t *dag, int32_t t, uint32_t n, uint32_t b, node_occ_t *a) {
  uint32_t i;

  assert(t > 0);

  printf("\n=== TEST ADD LEAVES ===\n");
  for (i=0; i<n; i++) {
    a[i]  = test_leaf(dag, t+i, b);
  }

  printf("\n=== AFTER ADDING %"PRIu32" LEAVES ===\n", n);
  print_dag(stdout, dag);
  fflush(stdout);
  return;

}



/*
 * TEST: create monomials (64bit coefficients)
 * - r = node occurrence
 * - b = bitsize
 * - store the resulting node occurrences in array a
 */
static void test_make_mono64(bvc_dag_t *dag, node_occ_t r, uint32_t b, node_occ_t *a) {
  uint64_t c;

  a[0] = test_mono64(dag, 1, r, b);
  a[1] = test_mono64(dag, -1, r, b);
  a[2] = test_mono64(dag, 1, (r^1), b);
  a[3] = test_mono64(dag, -1, (r^1), b);

  a[4] = test_mono64(dag, 4, r, b);
  a[5] = test_mono64(dag, -4, r, b);
  a[6] = test_mono64(dag, 4, (r^1), b);
  a[7] = test_mono64(dag, -4, (r^1), b);

  c = min_signed64(b);
  a[8] = test_mono64(dag, c, r, b);
  a[9] = test_mono64(dag, c, (r^1), b);

  a[10] = test_mono64(dag, 6, r, b);
  a[11] = test_mono64(dag, -6, r, b);
  a[12] = test_mono64(dag, 6, r, b);
  a[13] = test_mono64(dag, -6, r, b);
  
  printf("\n");
}




/*
 * GLOBAL DAG
 */
static bvc_dag_t dag;
static node_occ_t leaves[100];
static node_occ_t mono[100];

int main(void) {
  init_bvconstants();
  init_bvc_dag(&dag, 2);

  printf("=== INITIAL DAG ===\n");
  print_dag(stdout, &dag);

  test_make_leaves(&dag, 1, 10, 5, leaves);
  test_make_leaves(&dag, 200, 20, 63, leaves + 10);

  printf("\n=== TEST ADD MONO64 ===\n");

  test_make_mono64(&dag, leaves[0], 5, mono);
  test_make_mono64(&dag, leaves[2], 5, mono);
  test_make_mono64(&dag, leaves[10], 63, mono);
  test_make_mono64(&dag, leaves[11], 63, mono);
  
  printf("=== AFTER MONO64 ===\n");
  print_dag(stdout, &dag);

  reset_bvc_dag(&dag);
  printf("\n=== AFTER RESET ===\n");
  print_dag(stdout, &dag);

  test_make_leaves(&dag, 1, 10, 167, leaves);

  delete_bvc_dag(&dag);
  cleanup_bvconstants();

  return 0;
}
