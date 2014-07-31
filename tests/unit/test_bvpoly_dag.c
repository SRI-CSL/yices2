/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * DAG of bitvector polynomial expressions
 */

#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

#include "terms/bv64_constants.h"
#include "terms/bv_constants.h"
#include "utils/index_vectors.h"
#include "utils/int_array_sort.h"
#include "utils/memalloc.h"
#include "utils/prng.h"

#include "solvers/bv/bvpoly_dag.h"


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

#if 0
// variable occurrence x
static void print_vocc(FILE *f, int32_t x) {
  if (sign_of_occ(x) == 0) {
    fprintf(f, "+u!%"PRId32, (x>>1));
  } else {
    fprintf(f, "-u!%"PRId32, (x>>1));
  }
}
#endif


/*
 * 64bit coefficient, n = number of bits
 */
static void print_bvconst64(FILE *f, uint64_t c, uint32_t n) {
  if (c == 1) {
    fputs("+1", f);
  } else if (bvconst64_is_minus_one(c, n)) {
    fputs("-1", f);
  } else {
    bvconst64_print(f, c, n);
  }
}

static void print_bvconst(FILE *f, uint32_t *c, uint32_t n) {
  uint32_t w;

  w = (n + 31) >> 5;
  if (bvconst_is_one(c, w)) {
    fputs("+1", f);
  } else if (bvconst_is_minus_one(c, n)) {
    fputs("-1", f);
  } else {
    bvconst_print(f, c, n);
  }
}


/*
 * Print a node in the dag
 */
static void print_leaf_node(FILE *f, bvc_leaf_t *d) {
  fprintf(f, "[LEAF u!%"PRId32" (%"PRIu32" bits)]", d->map, d->header.bitsize);
}

static void print_zero_node(FILE *f, bvc_zero_t *d) {
  fprintf(f, "[ZERO (%"PRIu32" bits)]", d->header.bitsize);
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
static void print_node(FILE *f, bvc_dag_t *dag, bvnode_t q) {
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
  if (i == k) {
    fprintf(f, " empty");
  } else {
    do {
      fprintf(f, " n%"PRId32, i);
      i = dag->list[i].next;
    } while (i != k);
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

  fprintf(f, "\nLeaf nodes:");
  print_list(f, dag, BVC_DAG_LEAF_LIST);
  fprintf(f, "\n");

  fprintf(f, "\nElementary nodes:");
  print_list(f, dag, BVC_DAG_ELEM_LIST);
  fprintf(f, "\n");

  fprintf(f, "\nOther nodes:");
  print_list(f, dag, BVC_DAG_DEFAULT_LIST);
  fprintf(f, "\n");

  fflush(f);
}


/*
 * TESTS
 */

/*
 * Test leaf constructor
 * - b = bitsize
 * - v = variable
 */
static node_occ_t test_leaf(bvc_dag_t *dag, int32_t v, uint32_t b) {
  bvc_leaf_t *d;
  node_occ_t r, chk;
  bvnode_t q;

  r = bvc_dag_leaf(dag, v, b);
  chk = bvc_dag_leaf(dag, v, b);
  q = r >> 1;

  if (r != chk) {
    printf("---> ERROR: hash-consing failed\n");
    fflush(stdout);
    exit(1);
  }

  printf("---> created leaf node n!%"PRId32" for var u!%"PRId32" (%"PRIu32" bits)\n", q, v, b);
  if (sign_of_occ(r) == 0 && bvc_dag_node_is_leaf(dag, q)) {
    d = bvc_dag_node_leaf(dag, q);
    if (d->map != v || d->header.bitsize != b) {
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
  bvnode_t q;
  uint32_t sign;

  assert(1 <= b && b <= 64);
  a = norm64(a, b);
  tst = bvc_dag_mono64(dag, a, r, b);
  chk = bvc_dag_mono64(dag, a, r, b);

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

    printf("     decriptor: %p = ", d);
    print_mono_node(stdout, d);
    printf("\n");
  }

  return tst;

 error:
  printf("---> ERROR\n");
  fflush(stdout);
  exit(1);
}


/*
 * Test monomial for (a * r) with large coefficient
 * - b = bitsize (must be no more than 256)
 */
static node_occ_t test_mono(bvc_dag_t *dag, uint32_t *a, node_occ_t r, uint32_t b) {
  uint32_t aux[8];
  bvc_mono_t *d;
  node_occ_t tst, chk;
  bvnode_t q;
  uint32_t w, sign;

  assert(64 < b && b <= 256);

  bvconst_normalize(a, b);
  tst = bvc_dag_mono(dag, a, r, b);
  chk = bvc_dag_mono(dag, a, r, b);

  sign = sign_of_occ(tst);
  q = tst >> 1;

  printf("---> got ");
  print_nocc(stdout, tst);
  printf(" for ");
  print_bvconst(stdout, a, b);
  printf(" * ");
  print_nocc(stdout, r);
  printf(" (%"PRIu32" bits)\n", b);

  if (tst != chk) {
    printf("---> ERROR: Hash-consing failed\n");
    fflush(stdout);
    exit(1);
  }

  w = (b + 31) >> 5;
  if (bvconst_is_one(a, w)) {
    if (tst != r) goto error;
  } else if (bvconst_is_minus_one(a, b)) {
    if (tst != (r ^ 1)) goto error;
  } else {
    if (! bvc_dag_node_is_mono(dag, q)) goto error;
    d = bvc_dag_node_mono(dag, q);
    if (d->header.bitsize != b) goto error;

    // store -a in aux
    bvconst_negate2(aux, w, a);
    bvconst_normalize(aux, b);

    if (sign_of_occ(r) == 0) {
      if (d->nocc != r ||
	  (sign == 0 && bvconst_neq(d->coeff.w, a, w)) ||
	  (sign == 1 && bvconst_neq(d->coeff.w, aux, w))) {
	goto error;
      }
    } else {
      if (d->nocc != (r^1) ||
	  (sign == 0 && bvconst_neq(d->coeff.w, aux, w)) ||
	  (sign == 1 && bvconst_neq(d->coeff.w, a, w))) {
	goto error;
      }
    }

    printf("     decriptor: %p = ", d);
    print_mono_node(stdout, d);
    printf("\n");
  }

  return tst;

 error:
  printf("---> ERROR\n");
  fflush(stdout);
  exit(1);
}



/*
 * Test offset constructor (64bit version) for (a + r)
 */
static node_occ_t test_offset64(bvc_dag_t *dag, uint64_t a, node_occ_t r, uint32_t b) {
  bvc_offset_t *d;
  node_occ_t tst, chk;
  bvnode_t q;

  assert(1 <= b && b <= 64);
  a = norm64(a, b);
  tst = bvc_dag_offset64(dag, a, r, b);
  chk = bvc_dag_offset64(dag, a, r, b);
  q = tst >> 1;

  printf("---> created offset node n!%"PRId32" for ", q);
  print_bvconst64(stdout, a, b);
  printf(" ");
  print_nocc(stdout, r);
  printf(" (%"PRIu32" bits)\n", b);

  if (tst != chk) {
    printf("---> ERROR: Hash-consing failed\n");
    fflush(stdout);
    exit(1);
  }

  if (sign_of_occ(tst) != 0) goto error;
  if (!bvc_dag_node_is_offset(dag, q)) goto error;

  d = bvc_dag_node_offset(dag, q);
  if (d->header.bitsize != b || d->constant.c != a || d->nocc != r ) goto error;

  printf("     decriptor: %p = ", d);
  print_offset_node(stdout, d);
  printf("\n");

  return tst;

 error:
  printf("---> ERROR\n");
  fflush(stdout);
  exit(1);
}


/*
 * Test offset constructor for (a + r): large constant
 */
static node_occ_t test_offset(bvc_dag_t *dag, uint32_t *a, node_occ_t r, uint32_t b) {
  bvc_offset_t *d;
  node_occ_t tst, chk;
  bvnode_t q;
  uint32_t w;

  assert(64 < b);

  bvconst_normalize(a, b);
  tst = bvc_dag_offset(dag, a, r, b);
  chk = bvc_dag_offset(dag, a, r, b);
  q = tst >> 1;

  printf("---> created offset node n!%"PRId32" for ", q);
  print_bvconst(stdout, a, b);
  printf(" ");
  print_nocc(stdout, r);
  printf(" (%"PRIu32" bits)\n", b);

  if (tst != chk) {
    printf("---> ERROR: Hash-consing failed\n");
    fflush(stdout);
    exit(1);
  }

  if (sign_of_occ(tst) != 0) goto error;
  if (!bvc_dag_node_is_offset(dag, q)) goto error;

  w = (b + 31) >> 5;

  d = bvc_dag_node_offset(dag, q);
  if (d->header.bitsize != b || bvconst_neq(d->constant.w, a, w) || d->nocc != r ) goto error;

  printf("     decriptor: %p = ", d);
  print_offset_node(stdout, d);
  printf("\n");

  return tst;

 error:
  printf("---> ERROR\n");
  fflush(stdout);
  exit(1);
}



/*
 * Test sum constructor:
 * - a = array of n node occurrences
 * - b = bitsize
 * - n must be no more than 20
 */
static void copy_array(node_occ_t *aux, node_occ_t *a,  uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    aux[i] = a[i];
  }
}

static bool equal_arrays(node_occ_t *a, node_occ_t *b, uint32_t n) {
  uint32_t i;

  int_array_sort(a, n);
  int_array_sort(b, n);

  for (i=0; i<n; i++) {
    if (a[i] != b[i]) return false;
  }

  return true;
}


static node_occ_t test_sum(bvc_dag_t *dag, node_occ_t *a, uint32_t n, uint32_t b) {
  node_occ_t aux1[20];
  node_occ_t aux2[20];
  bvc_sum_t *d;
  node_occ_t tst, chk;
  bvnode_t q;
  uint32_t i;

  assert(n >= 1 && n <= 20);

  // copy a first since bvc_dag_sum may modify a
  copy_array(aux1, a, n);
  copy_array(aux2, a, n);
  tst = bvc_dag_sum(dag, a, n, b);
  chk = bvc_dag_sum(dag, aux1, n, b);
  q = tst>>1;

  printf("---> got ");
  print_nocc(stdout, tst);
  printf(" for sum");
  for (i=0; i<n; i++) {
    printf(" ");
    print_nocc(stdout, aux2[i]);
  }
  printf(" (%"PRIu32" bits)\n", b);

  if (tst != chk) {
    printf("---> ERROR: Hash-consing failed\n");
    fflush(stdout);
    exit(1);
  }

  if (n == 1) {
    if (tst != aux2[0]) goto error;
  } else {
    if (sign_of_occ(tst) != 0) goto error;
    if (!bvc_dag_node_is_sum(dag, q)) goto error;

    d = bvc_dag_node_sum(dag, q);
    if (d->header.bitsize != b || d->len != n || !equal_arrays(d->sum, aux2, n)) goto error;

    printf("     decriptor: %p = ", d);
    print_sum_node(stdout, d);
    printf("\n");
  }

  return tst;

 error:
  printf("---> ERROR\n");
  fflush(stdout);
  exit(1);
}



/*
 * Test pprod contructor:
 * - node occurrences are in a[0..n-1]
 * - exponents are in e[0...n-1]
 * - b = bitisize
 */
static bool equal_varexp(varexp_t *a, varexp_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i].var != b[i].var || a[i].exp != b[i].exp) {
      return false;
    }
  }

  return true;
}

static bool varexp_is_neg(node_occ_t x, uint32_t e) {
  return (sign_of_occ(x) == 1) && ((e & 1) == 1);
}

static node_occ_t test_pprod(bvc_dag_t *dag, node_occ_t *a, uint32_t *e, uint32_t n, uint32_t b) {
  pp_buffer_t aux;
  pprod_t *pp;
  bvc_prod_t *d;
  bvc_zero_t *z;
  node_occ_t tst, chk;
  bvnode_t q;
  uint32_t i;
  int32_t sign;

  assert(n >= 2 && n <= 20);

  // build the power product for the exponents
  pp = (pprod_t *) safe_malloc(sizeof(pprod_t) + n * sizeof(varexp_t));
  pp->len = n;
  pp->degree = 0;
  for (i=0; i<n; i++) {
    pp->prod[i].var = -1; // not used
    pp->prod[i].exp = e[i];
    pp->degree += e[i];
  }

  tst = bvc_dag_pprod(dag, pp, a, b);
  chk = bvc_dag_pprod(dag, pp, a, b);
  q = tst >> 1;

  printf("---> got ");
  print_nocc(stdout, tst);
  printf(" for product");
  for (i=0; i<n; i++) {
    printf(" ");
    print_nocc(stdout, a[i]);
    if (e[i] > 1) printf("^%"PRIu32, e[i]);
  }
  printf(" (%"PRIu32" bits)\n", b);

  if (tst != chk) {
    printf("---> ERROR: Hash-consing failed\n");
    fflush(stdout);
    exit(1);
  }

  // build the normalized power product in aux
  // keep track of the sign + check whether the product is zero
  init_pp_buffer(&aux, n);
  sign = +1;
  for (i=0; i<n; i++) {
    if (bvc_dag_occ_is_zero(dag, a[i])) {
      sign = 0;
    } else if (varexp_is_neg(a[i], e[i])) {
      sign = -sign;
    }
    pp_buffer_mul_varexp(&aux, unsigned_occ(a[i]), e[i]);
  }
  pp_buffer_normalize(&aux);

  // check results
  if (sign == 0) {
    if (!bvc_dag_node_is_zero(dag, q)) goto error;
    z = bvc_dag_node_zero(dag, q);

    printf("     descriptor: %p = ", z);
    print_zero_node(stdout, z);
    printf("\n");

  } else {
    if (sign == 1 && sign_of_occ(tst) != 0) goto error;
    if (sign == -1 && sign_of_occ(tst) != 1) goto error;
    if (!bvc_dag_node_is_prod(dag, q)) goto error;

    d = bvc_dag_node_prod(dag, q);
    if (d->header.bitsize != b || d->len != aux.len || !equal_varexp(d->prod, aux.prod, aux.len)) goto error;

    printf("     descriptor: %p = ", d);
    print_prod_node(stdout, d);
    printf("\n");
  }

  delete_pp_buffer(&aux);
  safe_free(pp);

  return tst;

 error:
  printf("---> ERROR\n");
  fflush(stdout);
  exit(1);
}




/*
 * RESULT VECTOR
 * - nodes are stored in an array of pairs [node_occ_t, bitsize]
 */
typedef struct test_occ_s {
  node_occ_t nocc;
  uint32_t bitsize;
} test_occ_t;


typedef struct tvector_s {
  test_occ_t *data;
  uint32_t nelems;
  uint32_t size;
} tvector_t;


static tvector_t store;

static void init_store(void) {
  store.data = (test_occ_t *) safe_malloc(100 * sizeof(test_occ_t));
  store.nelems = 0;
  store.size = 100;
}

static void delete_store(void) {
  safe_free(store.data);
  store.data = NULL;
}

static void reset_store(void) {
  store.nelems = 0;
}

static void expand_store(void) {
  uint32_t n;

  n = store.size * 2;
  if (n > (UINT32_MAX/sizeof(test_occ_t))) {
    out_of_memory();
  }

  store.data = (test_occ_t *) safe_realloc(store.data, n * sizeof(test_occ_t));
  store.size = n;
}

static void save_nocc(node_occ_t n, uint32_t b) {
  uint32_t i;

  i = store.nelems;
  if (i == store.size) {
    expand_store();
  }
  assert(i < store.size);
  store.data[i].nocc = n;
  store.data[i].bitsize = b;
  store.nelems = i+1;
}


/*
 * Select a node in the store with bitsize <= 64
 * - copy the node + bitsize in *s
 */
static void select_node64(test_occ_t *s) {
  uint32_t i, j, n;

  assert(store.nelems > 0);

  n = store.nelems;
  i = random_uint32() % n;
  j = i;
  do {
    if (store.data[j].bitsize <= 64) {
      *s = store.data[j];
      return;
    }
    j ++;
    if (j >= n) j = 0;
  } while (j != i);

  // nothing found
  abort();
}


/*
 * Select a node with bitsize > 64
 */
static void select_node(test_occ_t *s) {
  uint32_t i, j, n;

  assert(store.nelems > 0);

  n = store.nelems;
  i = random_uint32() % n;
  j = i;
  do {
    if (store.data[j].bitsize > 64) {
      *s = store.data[j];
      return;
    }
    j ++;
    if (j >= n) j = 0;
  } while (j != i);

  // nothing found
  abort();
}


/*
 * Select a node with bitsize == b
 */
static void select_node_bitsize(test_occ_t *s, uint32_t b) {
  uint32_t i, j, n;

  assert(store.nelems > 0);

  n = store.nelems;
  i = random_uint32() % n;
  j = i;
  do {
    if (store.data[j].bitsize == b) {
      *s = store.data[j];
      return;
    }
    j ++;
    if (j >= n) j = 0;
  } while (j != i);

  // nothing found
  abort();
}



/*
 * Select k nodes of same bitsize from the store
 * - store the bitsize in *bitsize
 * - store the node occurrences in s[0 ... k-1]
 */
static void select_node_array(uint32_t *bitsize, node_occ_t *s, uint32_t k) {
  test_occ_t aux;
  uint32_t i, n, b;

  assert(k > 0 && store.nelems > 0);

  n = store.nelems;
  i = random_uint32() % n;

  // use store.data[i] for s[0]
  s[0] = store.data[i].nocc;
  b = store.data[i].bitsize;
  *bitsize = b;

  // get the rest
  for (i=1; i<k; i++) {
    select_node_bitsize(&aux, b);
    assert(aux.bitsize == b);
    s[i] = aux.nocc;
  }
}




/*
 * TEST: create n leaves
 * - t = variable counter (*t is updated)
 * - b = bitsize
 */
static void test_make_leaves(bvc_dag_t *dag, int32_t *t, uint32_t n, uint32_t b) {
  uint32_t i;
  int32_t v;
  node_occ_t r;

  v = *t;

  assert(v > 0);

  for (i=0; i<n; i++) {
    r = test_leaf(dag, v, b);
    save_nocc(r, b);
    v ++;
  }

  *t = v;
}


/*
 * TEST: try all non-zero 4bit coefficients
 */
static void test_all_mono64(bvc_dag_t *dag) {
  test_occ_t aux;
  node_occ_t r;
  uint64_t a;

  printf("\n=== TEST MONO:  ALL FOUR-BIT COEFFICIENTS ====\n");
  select_node_bitsize(&aux, 4);
  r = aux.nocc;
  for (a=1; a<16; a++) {
    (void) test_mono64(dag, a, r, 4);
  }
  printf("\n");
  for (a=1; a<16; a++) {
    (void) test_mono64(dag, a, r^1, 4);
  }
  printf("\n");
}


/*
 * TEST: try all non-zero 4bit coefficients
 */
static void test_all_offset64(bvc_dag_t *dag) {
  test_occ_t aux;
  node_occ_t r;
  uint64_t a;

  printf("\n=== TEST ALL FOUR-BIT OFFSETS ====\n");
  select_node_bitsize(&aux, 4);
  r = aux.nocc;
  for (a=1; a<16; a++) {
    (void) test_offset64(dag, a, r, 4);
  }
  printf("\n");
  for (a=1; a<16; a++) {
    (void) test_offset64(dag, a, r^1, 4);
  }
  printf("\n");
}


/*
 * TEST: create monomials (64bit coefficients)
 * - t = pair occurrence/bitsize to use
 * - store the resulting node occurrences
 */
static void test_make_mono64(bvc_dag_t *dag, test_occ_t *t) {
  uint64_t c;
  uint32_t b;
  node_occ_t r, tst;

  tst = t->nocc;
  b = t->bitsize;

  r = test_mono64(dag, 1, tst, b);
  save_nocc(r, b);
  r = test_mono64(dag, -1, tst, b);
  save_nocc(r, b);
  r = test_mono64(dag, 1, (tst^1), b);
  save_nocc(r, b);
  r = test_mono64(dag, -1, (tst^1), b);
  save_nocc(r, b);

  r = test_mono64(dag, 4, tst, b);
  save_nocc(r, b);
  r = test_mono64(dag, -4, tst, b);
  save_nocc(r, b);
  r = test_mono64(dag, 4, (tst^1), b);
  save_nocc(r, b);
  r = test_mono64(dag, -4, (tst^1), b);
  save_nocc(r, b);

  c = min_signed64(b);
  r = test_mono64(dag, c, tst, b);
  save_nocc(r, b);
  r = test_mono64(dag, c, (tst^1), b);
  save_nocc(r, b);

  r = test_mono64(dag, 6, tst, b);
  save_nocc(r, b);
  r = test_mono64(dag, -6, tst, b);
  save_nocc(r, b);
  r = test_mono64(dag, 6, tst, b);
  save_nocc(r, b);
  r = test_mono64(dag, -6, tst, b);
  save_nocc(r, b);

  printf("\n");
}


/*
 * TEST: creae monomials with large bitsize
 */
static void test_make_mono(bvc_dag_t *dag, test_occ_t *t) {
  uint32_t aux[8];
  uint32_t w, b;
  node_occ_t r, tst;

  tst = t->nocc;
  b = t->bitsize;

  assert(64 < b && b <= 256);
  w = (b + 31) >> 5;

  bvconst_set_one(aux, w);
  r = test_mono(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set_minus_one(aux, w);
  r = test_mono(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set_one(aux, w);
  r = test_mono(dag, aux, tst^1, b);
  save_nocc(r, b);

  bvconst_set_minus_one(aux, w);
  r = test_mono(dag, aux, tst^1, b);
  save_nocc(r, b);

  bvconst_set32_signed(aux, w, 4);
  r = test_mono(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set32_signed(aux, w, -4);
  r = test_mono(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set32_signed(aux, w, 4);
  r = test_mono(dag, aux, tst^1, b);
  save_nocc(r, b);

  bvconst_set32_signed(aux, w, -4);
  r = test_mono(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set_min_signed(aux, b);
  r = test_mono(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set_min_signed(aux, b);
  r = test_mono(dag, aux, tst^1, b);
  save_nocc(r, b);

  bvconst_set_max_signed(aux, b);
  r = test_mono(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set_max_signed(aux, b);
  r = test_mono(dag, aux, tst^1, b);
  save_nocc(r, b);
}


/*
 * TEST: create offsets (64bit coefficients)
 */
static void test_make_offset64(bvc_dag_t *dag, test_occ_t *t) {
  uint64_t c;
  uint32_t b;
  node_occ_t r, tst;

  tst = t->nocc;
  b = t->bitsize;

  r = test_offset64(dag, 1, tst, b);
  save_nocc(r, b);
  r = test_offset64(dag, -1, tst, b);
  save_nocc(r, b);
  r = test_offset64(dag, 1, (tst^1), b);
  save_nocc(r, b);
  r = test_offset64(dag, -1, (tst^1), b);
  save_nocc(r, b);

  r = test_offset64(dag, 4, tst, b);
  save_nocc(r, b);
  r = test_offset64(dag, -4, tst, b);
  save_nocc(r, b);
  r = test_offset64(dag, 4, (tst^1), b);
  save_nocc(r, b);
  r = test_offset64(dag, -4, (tst^1), b);
  save_nocc(r, b);

  c = min_signed64(b);
  r = test_offset64(dag, c, tst, b);
  save_nocc(r, b);
  r = test_offset64(dag, c, (tst^1), b);
  save_nocc(r, b);

  r = test_offset64(dag, 6, tst, b);
  save_nocc(r, b);
  r = test_offset64(dag, -6, tst, b);
  save_nocc(r, b);
  r = test_offset64(dag, 6, tst, b);
  save_nocc(r, b);
  r = test_offset64(dag, -6, tst, b);
  save_nocc(r, b);

  printf("\n");
}


/*
 * TEST: create offsets with large bitsize
 */
static void test_make_offset(bvc_dag_t *dag, test_occ_t *t) {
  uint32_t aux[8];
  uint32_t w, b;
  node_occ_t r, tst;

  tst = t->nocc;
  b = t->bitsize;

  assert(64 < b && b <= 256);
  w = (b + 31) >> 5;

  bvconst_set_one(aux, w);
  r = test_offset(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set_minus_one(aux, w);
  r = test_offset(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set_one(aux, w);
  r = test_offset(dag, aux, tst^1, b);
  save_nocc(r, b);

  bvconst_set_minus_one(aux, w);
  r = test_offset(dag, aux, tst^1, b);
  save_nocc(r, b);

  bvconst_set32_signed(aux, w, 4);
  r = test_offset(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set32_signed(aux, w, -4);
  r = test_offset(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set32_signed(aux, w, 4);
  r = test_offset(dag, aux, tst^1, b);
  save_nocc(r, b);

  bvconst_set32_signed(aux, w, -4);
  r = test_offset(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set_min_signed(aux, b);
  r = test_offset(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set_min_signed(aux, b);
  r = test_offset(dag, aux, tst^1, b);
  save_nocc(r, b);

  bvconst_set_max_signed(aux, b);
  r = test_offset(dag, aux, tst, b);
  save_nocc(r, b);

  bvconst_set_max_signed(aux, b);
  r = test_offset(dag, aux, tst^1, b);
  save_nocc(r, b);
}



/*
 * TEST: sum of n elements
 */
static void test_make_sum(bvc_dag_t *dag, uint32_t n) {
  node_occ_t aux[n];
  node_occ_t r;
  uint32_t b, i;

  for (i=0; i<10; i++) {
    // get n random test nodes
    select_node_array(&b, aux, n);
    r = test_sum(dag, aux, n, b);
    save_nocc(r, b);
  }
}



/*
 * TEST: products of n elements
 */
static void test_make_product(bvc_dag_t *dag, uint32_t n) {
  node_occ_t a[n];
  uint32_t exp[n];
  uint32_t b, i;
  node_occ_t r;

  // set all exponents to 1
  for (i=0; i<n; i++) {
    exp[i] = 1;
  }

  for (i=0; i<10; i++) {
    select_node_array(&b, a, n);
    r = test_pprod(dag, a, exp, n, b);
    save_nocc(r, b);
  }

  // set some exponents to 2
  for (i=0; i<n; i++) {
    if ((random_uint32() & 0xFFFF) >= 0x8000) {
      exp[i] ++;
    }
  }

  for (i=0; i<10; i++) {
    select_node_array(&b, a, n);
    r = test_pprod(dag, a, exp, n, b);
    save_nocc(r, b);
  }

}



/*
 * GLOBAL DAG
 */
static bvc_dag_t dag;

int main(void) {
  test_occ_t x;
  int32_t ctr;
  uint32_t i;

  init_bvconstants();
  init_store();
  init_bvc_dag(&dag, 2);

  printf("=== INITIAL DAG ===\n");
  print_dag(stdout, &dag);

  ctr = 1;

  printf("\n=== TEST ADD LEAVES ===\n");
  test_make_leaves(&dag, &ctr, 20, 5);
  test_make_leaves(&dag, &ctr, 20, 4);
  test_make_leaves(&dag, &ctr, 20, 63);
  test_make_leaves(&dag, &ctr, 20, 70);
  test_make_leaves(&dag, &ctr, 20, 128);

  printf("\n=== AFTER ADDING LEAVES ===\n");
  print_dag(stdout, &dag);

  test_all_mono64(&dag);

  printf("\n=== TEST ADD MONO ===\n");

  for (i=0; i<4; i++) {
    select_node64(&x);
    test_make_mono64(&dag, &x);
  }

  for (i=0; i<4; i++) {
    select_node(&x);
    test_make_mono(&dag, &x);
  }

  test_all_offset64(&dag);

  printf("\n=== TEST ADD OFFSETS ===\n");

  for (i=0; i<4; i++) {
    select_node64(&x);
    test_make_offset64(&dag, &x);
  }

  for (i=0; i<4; i++) {
    select_node(&x);
    test_make_offset(&dag, &x);
  }

  printf("\n=== AFTER ADD MONO AND OFFSETS ===\n");
  print_dag(stdout, &dag);


  printf("\n=== TEST SUMS ===\n");
  test_make_sum(&dag, 1);
  test_make_sum(&dag, 2);
  test_make_sum(&dag, 4);
  test_make_sum(&dag, 7);
  test_make_sum(&dag, 8);
  test_make_sum(&dag, 10);
  test_make_sum(&dag, 11);

  printf("\n=== AFTER SUMS ===\n");
  print_dag(stdout, &dag);

  printf("\n=== TEST PRODUCTS ===\n");
  test_make_product(&dag, 2);
  test_make_product(&dag, 3);
  test_make_product(&dag, 11);

  printf("\n=== AFTER PRODUCTS ===\n");
  print_dag(stdout, &dag);

  printf("\n=== AFTER RESET ===\n");
  reset_bvc_dag(&dag);
  reset_store();
  ctr = 1;
  print_dag(stdout, &dag);

  test_make_leaves(&dag, &ctr, 20, 167);

  delete_bvc_dag(&dag);
  delete_store();
  cleanup_bvconstants();

  return 0;
}
