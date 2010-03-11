#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>

#include "types.h"
#include "memalloc.h"
#include "refcount_strings.h"


/*
 * Short cuts
 */
static type_t binary_function_type(type_table_t *tbl, type_t range, type_t dom1, type_t dom2) {
  type_t a[2];

  a[0] = dom1;
  a[1] = dom2;
  return function_type(tbl, range, 2, a);
}

extern type_t tuple_type_pair(type_table_t *tbl, type_t t1, type_t t2) {
  type_t a[2];

  a[0] = t1;
  a[1] = t2;
  return tuple_type(tbl, 2, a);
}

extern type_t tuple_type_triple(type_table_t *tbl, type_t t1, type_t t2, type_t t3) {
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



/*
 * Print type i
 */
static void print_type_aux(FILE *f, type_table_t *table, type_t i, uint32_t level) {
  int32_t k;
  switch (type_kind(table, i)) {
  case UNUSED_TYPE:
    fprintf(f, "deleted");
    break;
  case BOOL_TYPE:
    fprintf(f, "bool");
    break;
  case INT_TYPE:
    fprintf(f, "int");
    break;
  case REAL_TYPE:
    fprintf(f, "real");
    break;
  case BITVECTOR_TYPE:
    fprintf(f, "(bitvector %"PRId32")", bv_type_size(table, i));
    break;
  case SCALAR_TYPE:
    fprintf(f, "(scalar %"PRId32" %s)", scalar_type_cardinal(table, i), type_name(table, i));
    break;
  case UNINTERPRETED_TYPE:
    fprintf(f, "(uninterpreted %s)", type_name(table, i));
    break;
  case TUPLE_TYPE:
    fprintf(f, "(tuple-type");
    for (k=0; k<tuple_type_arity(table, i); k++) {
      fprintf(f, " %"PRId32, tuple_type_component(table, i, k));
    }
    fprintf(f, ")");
    break;
  case FUNCTION_TYPE:
    fprintf(f, "(fun-type:");
    for (k=0; k<function_type_arity(table, i); k++) {
      fprintf(f, " %"PRId32, function_type_domain(table, i, k));
    }
    fprintf(f, " -> %"PRId32")", function_type_range(table, i));
    break;
  default:
    fprintf(f, "(unknown kind %u)", type_kind(table, i));
    break;
  }

  if (level >= 1) {
    fprintf(f, ", card = %"PRIu32", flags = 0x%02x, ", 
	    type_card(table, i), (unsigned)type_flags(table, i));
    if (type_name(table, i) != NULL) {
      fprintf(f, "name = %s", type_name(table, i));
    } else {
      fprintf(f, "anonymous");
    }
  }
}

static void print_type_table(FILE *f, type_table_t *table, uint32_t level) {
  uint32_t i;
  int32_t k, l;

  fprintf(f, "type table %p\n", table);
  fprintf(f, "  size = %"PRIu32"\n", table->size);
  fprintf(f, "  nelems = %"PRIu32"\n", table->nelems);
  for (i=0; i<table->nelems; i++) {
    fprintf(f, "  type %"PRId32": ", i);
    print_type_aux(f, table, i, level);
    fprintf(f, "\n");
  }

  if (level >= 1) {
    k = table->free_idx;
    if (k < 0) {
      fprintf(f, "  free list: empty\n");
    } else {
      fprintf(f, "  free list:");
      l = 8;
      do {
	l --;
	if (l == 0) {
	  l = 8;
	  fprintf(f, "\n      ");
	}
	fprintf(f, " %"PRId32, k);
	k = table->desc[k].integer;
      } while (k >= 0);
      fprintf(f, "\n");
    }
  }
}





int main() {
  type_t bv10, bv32, i, any, enumtype, ft, tt;

  init_type_table(&table, 0);

  set_type_name(&table, real_type(&table), clone_string("real"));

  print_type_table(stdout, &table, 10);
  bv10 = bv_type(&table, 10);
  print_type_table(stdout, &table, 10);
  i = bv_type(&table, 10);
  print_type_table(stdout, &table, 10);
  printf("\n---> bv10: %"PRId32", i: %"PRId32"\n\n", bv10, i);
  bv32 = bv_type(&table, 32);
  set_type_name(&table, bv32, clone_string("bv32"));
  set_type_name(&table, bv32, clone_string("int32"));
  print_type_table(stdout, &table, 10);
  i = bv_type(&table, 32);
  print_type_table(stdout, &table, 10);
  printf("\n---> bv32: %"PRId32", i: %"PRId32"\n\n", bv32, i);

  any = new_uninterpreted_type(&table);
  set_type_name(&table, any, clone_string("any"));
  print_type_table(stdout, &table, 10);
  printf("\n---> any: %"PRId32"\n\n", any);

  enumtype = new_scalar_type(&table, 5);
  set_type_name(&table, enumtype, clone_string("enum"));
  print_type_table(stdout, &table, 10);
  printf("\n---> enumtype: %"PRId32"\n\n", enumtype);

  ft = binary_function_type(&table, real_type(&table), enumtype, any);
  set_type_name(&table, ft, clone_string("ftype"));
  i = binary_function_type(&table, real_type(&table), enumtype, any);
  print_type_table(stdout, &table, 10);
  printf("\n---> ft: %"PRId32", i: %"PRId32"\n\n", ft, i);
  
  i = get_type_by_name(&table, "real");
  printf("\n---> type-by-name real: %"PRId32"\n", i);
  i = get_type_by_name(&table, "enum");
  printf("---> type-by-name enum: %"PRId32"\n", i);
  i = get_type_by_name(&table, "any");
  printf("---> type-by-name any: %"PRId32"\n", i);
  i = get_type_by_name(&table, "bv32");
  printf("---> type-by-name bv32: %"PRId32"\n", i);
  i = get_type_by_name(&table, "int32");
  printf("---> type-by-name int32: %"PRId32"\n", i);
  i = get_type_by_name(&table, "ftype");
  printf("---> type-by-name ftype: %"PRId32"\n", i);
  i = get_type_by_name(&table, "bvxxx2");
  printf("---> type-by-name bvxxx2: %"PRId32"\n", i);

  //  printf("\n--- Garbage Collection ---\n");
  //  type_table_garbage_collection(&table);
  //  print_type_table(stdout, &table, 10);

  printf("\n--- removing bv32 and int32 ---\n");
  remove_type_name(&table, "bv32");
  i = get_type_by_name(&table, "bv32");
  printf("---> type-by-name bv32: %"PRId32"\n", i);
  remove_type_name(&table, "int32");
  i = get_type_by_name(&table, "int32");
  printf("---> type-by-name int32: %"PRId32"\n", i);
  remove_type_name(&table, "int32");
  i = get_type_by_name(&table, "int32");
  printf("---> type-by-name int32: %"PRId32"\n", i);
  print_type_table(stdout, &table, 10);

  //  printf("\n--- Garbage Collection ---\n");
  //  type_table_garbage_collection(&table);
  //  print_type_table(stdout, &table, 10);

  tt = tuple_type_pair(&table, any, enumtype);
  i = tuple_type_pair(&table, any, enumtype);
  printf("\n---> tt: %"PRId32", i: %"PRId32"\n\n", tt, i);
  print_type_table(stdout, &table, 10);

  tt = tuple_type_triple(&table, any, int_type(&table), tt);
  i = tuple_type_triple(&table, bv_type(&table, 24), int_type(&table), tt);
  printf("\n---> tt: %"PRId32", i: %"PRId32"\n\n", tt, i);
  print_type_table(stdout, &table, 10);

  // Check hash consing
  i = tuple_type_triple(&table, bv_type(&table, 24), int_type(&table),
			tuple_type_triple(&table, any, int_type(&table), 
					  tuple_type_pair(&table, any, enumtype)));
  printf("\n---> (tuple (bv 24) int (tuple any int (tuple any enum))): %"PRId32"\n\n", i);
  print_type_table(stdout, &table, 10);
  

  // keep tt/delete i
  //  set_root_type_flag(&table, tt);
  //  printf("\n--- Garbage Collection ---\n");
  //  type_table_garbage_collection(&table);
  //  print_type_table(stdout, &table, 10);
  delete_type_table(&table);


  printf("\n*** New Table ***\n");
  init_type_table(&table, 20);
  print_type_table(stdout, &table, 10);
  bv10 = bv_type(&table, 10);
  print_type_table(stdout, &table, 10);
  i = bv_type(&table, 10);
  print_type_table(stdout, &table, 10);
  printf("\n---> bv10: %"PRId32", i: %"PRId32"\n", bv10, i);
  bv32 = bv_type(&table, 32);
  set_type_name(&table, bv32, clone_string("bv32"));
  set_type_name(&table, bv32, clone_string("int32"));
  print_type_table(stdout, &table, 10);
  i = bv_type(&table, 32);
  print_type_table(stdout, &table, 10);
  printf("\n---> bv32: %"PRId32", i: %"PRId32"\n\n", bv32, i);

  any = new_uninterpreted_type(&table);
  set_type_name(&table, any, clone_string("any"));
  print_type_table(stdout, &table, 10);
  printf("\n---> any: %"PRId32"\n\n", any);

  printf("\n*** END ***\n");
  print_type_table(stdout, &table, 10);
  printf("\n");
  print_symbol_table(stdout, &table.stbl, 10);
  printf("\n");
  print_int_hash_table(stdout, &table.htbl, 10);
  printf("\n\n");

  delete_type_table(&table);


  return 0;
}
