#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <assert.h>

#include "types.h"
#include "type_printer.h"
#include "refcount_strings.h"


/*
 * Short cuts
 */
static type_t binary_function_type(type_table_t *tbl, type_t dom1, type_t dom2, type_t range) {
  type_t a[2];

  a[0] = dom1;
  a[1] = dom2;
  return function_type(tbl, range, 2, a);
}

static type_t tuple_type_pair(type_table_t *tbl, type_t t1, type_t t2) {
  type_t a[2];

  a[0] = t1;
  a[1] = t2;
  return tuple_type(tbl, 2, a);
}

static type_t tuple_type_triple(type_table_t *tbl, type_t t1, type_t t2, type_t t3) {
  type_t a[3];

  a[0] = t1;
  a[1] = t2;
  a[2] = t3;
  return tuple_type(tbl, 3, a);
}

static type_table_t table;


/*
 * Print a hash table
 */
static void print_int_hash_table(FILE *f, int_htbl_t *tbl, uint32_t level) {
  uint32_t i;
  int_hrec_t *r;

  fprintf(f, "hash table %p\n", tbl);
  fprintf(f, "  size = %"PRIu32"\n", tbl->size);
  fprintf(f, "  nelems = %"PRIu32"\n", tbl->nelems);
  fprintf(f, "  ndeleted = %"PRIu32"\n", tbl->ndeleted);
  fprintf(f, "  resize threshold = %"PRIu32"\n", tbl->resize_threshold);
  fprintf(f, "  cleanup threshold = %"PRIu32"\n", tbl->cleanup_threshold);
  if (level >= 1) {
    fprintf(f, "  records:\n");
    for (i=0; i<tbl->size; i++) {
      r = tbl->records + i;
      if (r->value >= 0) {
	fprintf(f, "    %"PRIu32": [key = %8x, val = %"PRId32"]\n", i, (unsigned) r->key, r->value);
      }
    }
  }
  if (level >= 2) {
    fprintf(f, "  deleted:\n");
    for (i=0; i<tbl->size; i++) {
      r = tbl->records + i;
      if (r->value == DELETED_VALUE) {
	fprintf(f, "    %"PRIu32": [key = %8x, val = %"PRId32"]\n", i, (unsigned) r->key, r->value);
      }
    }
  }
  if (level >= 100) {
    fprintf(f, "  free:\n");
    for (i=0; i<tbl->size; i++) {
      r = tbl->records + i;
      if (r->value == NULL_VALUE) {
	fprintf(f, "    %"PRIu32": [key = %8x, val = %"PRId32"]\n", i, (unsigned) r->key, r->value);
      }
    }
  }
}



/*
 * Print a symbol table
 */
static void print_symbol_table(FILE *f, stbl_t *table, uint32_t level) {
  uint32_t i, k;
  stbl_rec_t *r;
  stbl_bank_t *b;

  fprintf(f, "symbol table %p\n", table);
  fprintf(f, "  size = %"PRIu32"\n", table->size);
  fprintf(f, "  nelems = %"PRIu32"\n", table->nelems);
  fprintf(f, "  ndeleted = %"PRIu32"\n", table->ndeleted);
  fprintf(f, "  free idx = %"PRIu32"\n", table->free_idx);
  if (level >= 1) {
    for (i=0; i<table->size; i++) {
      r = table->data[i];
      if (r != NULL) {
	fprintf(f, "  bucket %"PRIu32"\n", i);
	do {
	  fprintf(f, "    [hash = %8x, value = %"PRId32", string = %s]\n", (unsigned) r->hash, r->value, r->string);
	  r = r->next;
	} while (r != NULL);
      }
    }
  }

  if (level >= 3) {
    if (table->bnk == NULL) {
      fprintf(f, "  no allocated banks\n");
    }
    k = table->free_idx;
    for (b = table->bnk; b != NULL; b = b->next) {
      fprintf(f, "  bank %p\n", b);
      for (r = b->block + k; r < b->block + STBL_BANK_SIZE; r ++) {
	if (r->string == NULL) {
	  fprintf(f, "    %p: [hash = %8x, value = %"PRId32", string = %p, next = %p]\n", 
		  r, (unsigned) r->hash, r->value, r->string, r->next);
	} else {
	  fprintf(f, "    %p: [hash = %8x, value = %"PRId32", string = %s, next = %p]\n", 
		  r, (unsigned) r->hash, r->value, r->string, r->next);
	}
      }
      k = 0;
    }
  }

  if (level >= 3) {
    r = table->free_rec;
    if (r == NULL) {
      fprintf(f, "  free list: empty\n");
    } else {
      fprintf(f, "  free list:\n");
      do {
	fprintf(f, "    %p: [hash = %8x, value = %"PRId32", string = %p, next = %p]\n", 
		r, (unsigned) r->hash, r->value, r->string, r->next);
	r = r->next;
      } while (r != NULL);
    }
  }  
}





int main() {
  type_t bv10, bv32, i, any, enumtype, ft, unit, tt;
  type_t unit2, unit_pair, finite_pair, finite_fun, unit_fun, finite_fun2;

  printf("*** Initial table ***\n");
  init_type_table(&table, 0);
  print_type_table(stdout, &table);
  printf("\n");

  printf("*** Naming real ***\n");
  set_type_name(&table, real_type(&table), clone_string("R"));
  print_type_table(stdout, &table);
  printf("\n");

  printf("*** Creating bv10 ***\n");
  bv10 = bv_type(&table, 10);
  print_type_table(stdout, &table);
  printf("\n");

  i = bv_type(&table, 10);
  printf("---> bv10: %"PRId32", i: %"PRId32"\n\n", bv10, i);
  assert(i == bv10);

  printf("*** Creating bv32 ***\n");
  bv32 = bv_type(&table, 32);
  set_type_name(&table, bv32, clone_string("bv32"));
  set_type_name(&table, bv32, clone_string("int32"));
  print_type_table(stdout, &table);
  printf("\n");
  i = bv_type(&table, 32);
  printf("---> bv32: %"PRId32", i: %"PRId32"\n\n", bv32, i);
  assert(i == bv32);

  printf("*** Creating any (uninterpreted) ***\n");
  any = new_uninterpreted_type(&table);
  set_type_name(&table, any, clone_string("any"));
  print_type_table(stdout, &table);
  printf("\n");
  printf("---> any: %"PRId32"\n\n", any);

  printf("*** Creating enum (scalar 5) ***\n");
  enumtype = new_scalar_type(&table, 5);
  set_type_name(&table, enumtype, clone_string("enum"));
  print_type_table(stdout, &table);
  printf("\n");
  printf("---> enum: %"PRId32"\n\n", enumtype);

  printf("*** Creating ftype ***\n");
  ft = binary_function_type(&table, enumtype, any, real_type(&table));
  set_type_name(&table, ft, clone_string("ftype"));
  i = binary_function_type(&table, enumtype, any, real_type(&table));
  print_type_table(stdout, &table);
  printf("\n");
  printf("---> ft: %"PRId32", i: %"PRId32"\n\n", ft, i);
  assert(i == ft);

  printf("*** Creating unit (scalar 1) ***\n");
  unit = new_scalar_type(&table, 1);
  set_type_name(&table, unit, clone_string("unit"));
  print_type_table(stdout, &table);
  printf("\n");
  
  printf("*** Creating unit2 (scalar 1) ***\n");
  unit2 = new_scalar_type(&table, 1);
  print_type_table(stdout, &table);
  printf("\n");

  printf("*** Creating unit pair ***\n");
  unit_pair = tuple_type_pair(&table, unit, unit2);
  print_type_table(stdout, &table);
  printf("\n");

  printf("*** Creating finite pair ***\n");
  finite_pair = tuple_type_pair(&table, bool_type(&table), enumtype);
  print_type_table(stdout, &table);
  printf("\n");

  printf("*** Creating finite function ***\n");
  finite_fun = binary_function_type(&table, bool_type(&table), enumtype, bool_type(&table));
  print_type_table(stdout, &table);
  printf("\n");

  printf("*** Creating unit function ***\n");
  unit_fun = binary_function_type(&table, int_type(&table), int_type(&table), unit);
  print_type_table(stdout, &table);
  printf("\n");

  printf("*** Creating large finite function ***\n");
  finite_fun2 = binary_function_type(&table, finite_fun, bool_type(&table), enumtype);
  print_type_table(stdout, &table);
  printf("\n");

 
  printf("*** Testing get_by_name ***\n");
  i = get_type_by_name(&table, "real");
  printf("---> type-by-name real: %"PRId32"\n", i);
  assert(i == NULL_TERM);
  i = get_type_by_name(&table, "R");
  printf("---> type-by-name R: %"PRId32"\n", i);
  assert(i == real_id);
  i = get_type_by_name(&table, "enum");
  printf("---> type-by-name enum: %"PRId32"\n", i);
  assert(i == enumtype);
  i = get_type_by_name(&table, "any");
  printf("---> type-by-name any: %"PRId32"\n", i);
  assert(i == any);
  i = get_type_by_name(&table, "bv32");
  printf("---> type-by-name bv32: %"PRId32"\n", i);
  assert(i == bv32);
  i = get_type_by_name(&table, "int32");
  printf("---> type-by-name int32: %"PRId32"\n", i);
  assert(i == bv32);
  i = get_type_by_name(&table, "ftype");
  printf("---> type-by-name ftype: %"PRId32"\n", i);
  assert(i == ft);
  i = get_type_by_name(&table, "bvxxx2");
  printf("---> type-by-name bvxxx2: %"PRId32"\n", i);
  assert(i == NULL_TYPE);
  printf("\n\n");

  printf("*** Garbage Collection ***\n");
  type_table_gc(&table);
  print_type_table(stdout, &table);
  printf("\n");

  printf("*** removing bv32 and int32 ***\n");
  remove_type_name(&table, "bv32");
  i = get_type_by_name(&table, "bv32");
  printf("---> type-by-name bv32: %"PRId32"\n", i);
  assert(i == NULL_TYPE);
  remove_type_name(&table, "int32");
  i = get_type_by_name(&table, "int32");
  printf("---> type-by-name int32: %"PRId32"\n", i);
  remove_type_name(&table, "int32");
  i = get_type_by_name(&table, "int32");
  printf("---> type-by-name int32: %"PRId32"\n\n", i);
  assert(i == NULL_TYPE);
  print_type_table(stdout, &table);
  printf("\n");

  printf("*** Garbage Collection ***\n");
  type_table_gc(&table);
  print_type_table(stdout, &table);
  printf("\n");

  printf("*** Creating pair type ***\n");
  tt = tuple_type_pair(&table, any, enumtype);
  i = tuple_type_pair(&table, any, enumtype);
  printf("---> tt: %"PRId32", i: %"PRId32"\n\n", tt, i);
  assert(i == tt);
  print_type_table(stdout, &table);
  printf("\n");

  printf("*** Creating triplets ***\n");
  tt = tuple_type_triple(&table, any, int_type(&table), tt);
  i = tuple_type_triple(&table, bv_type(&table, 24), int_type(&table), tt);
  printf("---> tt: %"PRId32", i: %"PRId32"\n\n", tt, i);
  print_type_table(stdout, &table);
  printf("\n");

  // Check hash consing
  i = tuple_type_triple(&table, bv_type(&table, 24), int_type(&table),
			tuple_type_triple(&table, any, int_type(&table), 
					  tuple_type_pair(&table, any, enumtype)));
  printf("\n---> (tuple (bv 24) int (tuple any int (tuple any enum))): %"PRId32"\n\n", i);
  print_type_table(stdout, &table);
  printf("\n");

  // mark last type i:
  type_table_set_gc_mark(&table, i);
  printf("*** Garbage Collection (marked tau!%"PRId32") ***\n", i);
  type_table_gc(&table);
  print_type_table(stdout, &table);
  printf("\n");

  // mark tt
  type_table_set_gc_mark(&table, tt);
  printf("*** Garbage Collection (marked tau!%"PRId32") ***\n", tt);
  type_table_gc(&table);
  print_type_table(stdout, &table);
  printf("\n");

  delete_type_table(&table);


  printf("\n*** New Table ***\n");
  init_type_table(&table, 20);
  print_type_table(stdout, &table);
  printf("\n");

  printf("*** Creating bv10 and bv32 ***\n");
  bv10 = bv_type(&table, 10);
  i = bv_type(&table, 10);
  printf("---> bv10: %"PRId32", i: %"PRId32"\n", bv10, i);
  assert(i == bv10);
  bv32 = bv_type(&table, 32);
  set_type_name(&table, bv32, clone_string("bv32"));
  set_type_name(&table, bv32, clone_string("int32"));
  i = bv_type(&table, 32);
  printf("---> bv32: %"PRId32", i: %"PRId32"\n\n", bv32, i);
  print_type_table(stdout, &table);
  printf("\n");

  printf("*** Creating any (uninterpreted) ***\n");
  any = new_uninterpreted_type(&table);
  set_type_name(&table, any, clone_string("any"));
  printf("---> any: %"PRId32"\n\n", any);
  print_type_table(stdout, &table);
  printf("\n");

  printf("\n*** END ***\n");
  print_type_table(stdout, &table);
  printf("\n");
  print_symbol_table(stdout, &table.stbl, 10);
  printf("\n");
  print_int_hash_table(stdout, &table.htbl, 10);
  printf("\n\n");

  delete_type_table(&table);


  return 0;
}
