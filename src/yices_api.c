/*
 * YICES API
 */

/*
 * This module implements the API defined in yices.h.
 *
 * It also implements the functions defined in yices_extensions.h and
 * yices_iterators.h
 */


/*
 * Visibility control: all extern functions declared here are in libyices's API
 * Other extern functions should have visibility=hidden (cf. Makefile).
 */
#if defined(CYGWIN) || defined(MINGW)
#define EXPORTED __declspec(dllexport)
#define __YICES_DLLSPEC__ EXPORTED
#else
#define EXPORTED __attribute__((visibility("default")))
#endif

#include <assert.h>
#include <stddef.h>
#include <string.h>

#include "refcount_strings.h"
#include "string_utils.h"
#include "dl_lists.h"
#include "int_array_sort.h"

#include "bv64_constants.h"
#include "arith_buffer_terms.h"
#include "bvarith_buffer_terms.h"
#include "bvarith64_buffer_terms.h"

#include "types.h"
#include "term_manager.h"
#include "context.h"
#include "models.h"
#include "context_config.h"
#include "search_parameters.h"

#include "yices.h"
#include "yices_error.h"
#include "yices_extensions.h"
#include "yices_iterators.h"
#include "yices_globals.h"
#include "yices_parser.h"
#include "yices_pp.h"


/*
 * Global tables: 
 * - type table + a single term_manager
 */
// global tables
static type_table_t types;
static term_manager_t manager;

// error report
static error_report_t error;

// parser, lexer, term stack: all are allocated on demand
static parser_t *parser;
static lexer_t *lexer;
static tstack_t *tstack;


// rational for building terms
static rational_t r0;

// buffer for building bitvector constants
static bvconstant_t bv0;


/*
 * Initial sizes of the type and term tables.
 */
#define INIT_TYPE_SIZE  16
#define INIT_TERM_SIZE  64


/*
 * Global table. Initially all pointers are NULL
 */
yices_globals_t __yices_globals = {
  NULL, NULL, NULL, NULL, NULL,
};




/************************************
 *  DYNAMICALLY ALLOCATED OBJECTS   *
 ***********************************/

/*
 * All objects that can be allocated via the API 
 * are stored in doubly-linked lists. This will help
 * implement some form of garbage collection at some point.
 * For now, this  makes it possible to delete all
 * global objects when yices_exit is called.
 */

/*
 * Doubly-linked list of arithmetic buffers
 */
typedef struct {
  dl_list_t header;
  arith_buffer_t buffer;
} arith_buffer_elem_t;

static dl_list_t arith_buffer_list;


/*
 * Doubly-linked list of bitvector arithmetic buffers
 */
typedef struct {
  dl_list_t header;
  bvarith_buffer_t buffer;
} bvarith_buffer_elem_t;

static dl_list_t bvarith_buffer_list;


/*
 * Variant: 64bit buffers
 */
typedef struct {
  dl_list_t header;
  bvarith64_buffer_t buffer;
} bvarith64_buffer_elem_t;

static dl_list_t bvarith64_buffer_list;


/*
 * Doubly-linked list of bitvector buffers
 */
typedef struct {
  dl_list_t header;
  bvlogic_buffer_t buffer;
} bvlogic_buffer_elem_t;

static dl_list_t bvlogic_buffer_list;


/*
 * Doubly-linked list of contexts
 */
typedef struct {
  dl_list_t header;
  context_t context;
} context_elem_t;

static dl_list_t context_list;


/*
 * Models
 */
typedef struct {
  dl_list_t header;
  model_t model;
} model_elem_t;

static dl_list_t model_list;


/*
 * Context configuration and parameter descriptors
 * are stored in one list.
 */
typedef struct {
  dl_list_t header;
  ctx_config_t config;
} ctx_config_elem_t;

typedef struct {
  dl_list_t header;
  param_t param;
} param_structure_elem_t;

static dl_list_t generic_list;




/**********************************
 *  ARITHMETIC-BUFFER ALLOCATION  *
 *********************************/

/*
 * Get header of buffer b, assuming b is embedded into an arith_buffer_elem
 */
static inline dl_list_t *arith_buffer_header(arith_buffer_t *b) {
  return (dl_list_t *)(((char *)b) - offsetof(arith_buffer_elem_t, buffer));
}

/*
 * Get buffer of header l
 */
static inline arith_buffer_t *arith_buffer(dl_list_t *l) {
  return (arith_buffer_t *)(((char *) l) + offsetof(arith_buffer_elem_t, buffer));
}

/*
 * Allocate an arithmetic buffer and insert it into the list
 */
static inline arith_buffer_t *alloc_arith_buffer(void) {
  arith_buffer_elem_t *new_elem;

  new_elem = (arith_buffer_elem_t *) safe_malloc(sizeof(arith_buffer_elem_t));
  list_insert_next(&arith_buffer_list, &new_elem->header);
  return &new_elem->buffer;
}

/*
 * Remove b from the list and free b
 */
static inline void free_arith_buffer(arith_buffer_t *b) {
  dl_list_t *elem;

  elem = arith_buffer_header(b);
  list_remove(elem);
  safe_free(elem);
}

/*
 * Clean up the arith buffer list: free all elements and empty the list
 */
static void free_arith_buffer_list(void) {
  dl_list_t *elem, *aux;

  elem = arith_buffer_list.next;
  while (elem != &arith_buffer_list) {
    aux = elem->next;
    delete_arith_buffer(arith_buffer(elem));
    safe_free(elem);
    elem = aux;
  }

  clear_list(&arith_buffer_list);
}



/********************************************
 *  BITVECTOR ARITHMETIC BUFFER ALLOCATION  *
 *******************************************/

/*
 * Get header of buffer b, assuming b is embedded into an bvarith_buffer_elem
 */
static inline dl_list_t *bvarith_buffer_header(bvarith_buffer_t *b) {
  return (dl_list_t *)(((char *)b) - offsetof(bvarith_buffer_elem_t, buffer));
}

/*
 * Get buffer of header l
 */
static inline bvarith_buffer_t *bvarith_buffer(dl_list_t *l) {
  return (bvarith_buffer_t *)(((char *) l) + offsetof(bvarith_buffer_elem_t, buffer));
}

/*
 * Allocate a bv-arithmetic buffer and insert it into the list
 */
static inline bvarith_buffer_t *alloc_bvarith_buffer(void) {
  bvarith_buffer_elem_t *new_elem;

  new_elem = (bvarith_buffer_elem_t *) safe_malloc(sizeof(bvarith_buffer_elem_t));
  list_insert_next(&bvarith_buffer_list, &new_elem->header);
  return &new_elem->buffer;
}

/*
 * Remove b from the list and free b
 */
static inline void free_bvarith_buffer(bvarith_buffer_t *b) {
  dl_list_t *elem;

  elem = bvarith_buffer_header(b);
  list_remove(elem);
  safe_free(elem);
}

/*
 * Clean up the arith buffer list: free all elements and empty the list
 */
static void free_bvarith_buffer_list(void) {
  dl_list_t *elem, *aux;

  elem = bvarith_buffer_list.next;
  while (elem != &bvarith_buffer_list) {
    aux = elem->next;
    delete_bvarith_buffer(bvarith_buffer(elem));
    safe_free(elem);
    elem = aux;
  }

  clear_list(&bvarith_buffer_list);
}



/*********************************
 *  BVARITH64 BUFFER ALLOCATION  *
 ********************************/

/*
 * Get header of buffer b, assuming b is embedded into an bvarith64_buffer_elem
 */
static inline dl_list_t *bvarith64_buffer_header(bvarith64_buffer_t *b) {
  return (dl_list_t *)(((char *)b) - offsetof(bvarith64_buffer_elem_t, buffer));
}

/*
 * Get buffer of header l
 */
static inline bvarith64_buffer_t *bvarith64_buffer(dl_list_t *l) {
  return (bvarith64_buffer_t *)(((char *) l) + offsetof(bvarith64_buffer_elem_t, buffer));
}

/*
 * Allocate a bv-arithmetic buffer and insert it into the list
 */
static inline bvarith64_buffer_t *alloc_bvarith64_buffer(void) {
  bvarith64_buffer_elem_t *new_elem;

  new_elem = (bvarith64_buffer_elem_t *) safe_malloc(sizeof(bvarith64_buffer_elem_t));
  list_insert_next(&bvarith64_buffer_list, &new_elem->header);
  return &new_elem->buffer;
}

/*
 * Remove b from the list and free b
 */
static inline void free_bvarith64_buffer(bvarith64_buffer_t *b) {
  dl_list_t *elem;

  elem = bvarith64_buffer_header(b);
  list_remove(elem);
  safe_free(elem);
}

/*
 * Clean up the buffer list: free all elements and empty the list
 */
static void free_bvarith64_buffer_list(void) {
  dl_list_t *elem, *aux;

  elem = bvarith64_buffer_list.next;
  while (elem != &bvarith64_buffer_list) {
    aux = elem->next;
    delete_bvarith64_buffer(bvarith64_buffer(elem));
    safe_free(elem);
    elem = aux;
  }

  clear_list(&bvarith64_buffer_list);
}



/*****************************
 *  LOGIC BUFFER ALLOCATION  *
 ****************************/

/*
 * Get header of buffer b, assuming b is embedded into an bvlogic_buffer_elem
 */
static inline dl_list_t *bvlogic_buffer_header(bvlogic_buffer_t *b) {
  return (dl_list_t *)(((char *)b) - offsetof(bvlogic_buffer_elem_t, buffer));
}

/*
 * Get buffer of header l
 */
static inline bvlogic_buffer_t *bvlogic_buffer(dl_list_t *l) {
  return (bvlogic_buffer_t *)(((char *) l) + offsetof(bvlogic_buffer_elem_t, buffer));
}

/*
 * Allocate an arithmetic buffer and insert it into the list
 */
static inline bvlogic_buffer_t *alloc_bvlogic_buffer(void) {
  bvlogic_buffer_elem_t *new_elem;

  new_elem = (bvlogic_buffer_elem_t *) safe_malloc(sizeof(bvlogic_buffer_elem_t));
  list_insert_next(&bvlogic_buffer_list, &new_elem->header);
  return &new_elem->buffer;
}

/*
 * Remove b from the list and free b
 */
static inline void free_bvlogic_buffer(bvlogic_buffer_t *b) {
  dl_list_t *elem;

  elem = bvlogic_buffer_header(b);
  list_remove(elem);
  safe_free(elem);
}

/*
 * Clean up the arith buffer list: free all elements and empty the list
 */
static void free_bvlogic_buffer_list(void) {
  dl_list_t *elem, *aux;

  elem = bvlogic_buffer_list.next;
  while (elem != &bvlogic_buffer_list) {
    aux = elem->next;
    delete_bvlogic_buffer(bvlogic_buffer(elem));
    safe_free(elem);    
    elem = aux;
  }

  clear_list(&bvlogic_buffer_list);
}




/*************************
 *  CONTEXT ALLOCATION   *
 ************************/

/*
 * Get the header of a context c, assuming c is embedded in a context_elem
 */
static inline dl_list_t *header_of_context(context_t *c) {
  return (dl_list_t *)(((char *) c) - offsetof(context_elem_t, context));
}

/*
 * Get the context of header l
 */
static inline context_t *context_of_header(dl_list_t *l) {
  return (context_t *) (((char *) l) + offsetof(context_elem_t, context));
}

/*
 * Allocate a fresh context object and insert it in the context_list
 * - WARNING: the context is not initialized
 */
static inline context_t *alloc_context(void) {
  context_elem_t *new_elem;

  new_elem = (context_elem_t *) safe_malloc(sizeof(context_elem_t));
  list_insert_next(&context_list, &new_elem->header);
  return &new_elem->context;
}


/*
 * Remove c from the list and free c
 * - WARNING: make sure to call delete_context(c) before this 
 *   function
 */
static inline void free_context(context_t *c) {
  dl_list_t *elem;

  elem = header_of_context(c);
  list_remove(elem);
  safe_free(elem);
}


/*
 * Cleanup the context list
 */
static void free_context_list(void) {
  dl_list_t *elem, *aux;

  elem = context_list.next;
  while (elem != &context_list) {
    aux = elem->next;
    delete_context(context_of_header(elem));
    safe_free(elem);
    elem = aux;
  }

  clear_list(&context_list);
}



/***********************
 *  MODEL ALLOCATION   *
 **********************/

/*
 * Get the header of a context m, assuming m is embedded in a model_elem
 */
static inline dl_list_t *header_of_model(model_t *m) {
  return (dl_list_t *)(((char *) m) - offsetof(model_elem_t, model));
}

/*
 * Get the model of header l
 */
static inline model_t *model_of_header(dl_list_t *l) {
  return (model_t *) (((char *) l) + offsetof(model_elem_t, model));
}

/*
 * Allocate a fresh model object and insert it in the model_list
 * - WARNING: the model is not initialized
 */
static inline model_t *alloc_model(void) {
  model_elem_t *new_elem;

  new_elem = (model_elem_t *) safe_malloc(sizeof(model_elem_t));
  list_insert_next(&model_list, &new_elem->header);
  return &new_elem->model;
}


/*
 * Remove c from the list and free m
 * - WARNING: make sure to call delete_model(c) before this 
 *   function
 */
static inline void free_model(model_t *m) {
  dl_list_t *elem;

  elem = header_of_model(m);
  list_remove(elem);
  safe_free(elem);
}


/*
 * Cleanup the model list
 */
static void free_model_list(void) {
  dl_list_t *elem, *aux;

  elem = model_list.next;
  while (elem != &model_list) {
    aux = elem->next;
    delete_model(model_of_header(elem));
    safe_free(elem);
    elem = aux;
  }

  clear_list(&model_list);
}




/********************************************
 *  CONFIG AND SEARCH PARAMETER STRUCTURES  *
 *******************************************/

/*
 * Get the header
 */
static inline dl_list_t *header_of_config_structure(ctx_config_t *c) {
  return (dl_list_t *) (((char *) c) - offsetof(ctx_config_elem_t, config));
}

static inline dl_list_t *header_of_param_structure(param_t *p) {
  return (dl_list_t *) (((char *) p) - offsetof(param_structure_elem_t, param));
}

/*
 * Allocate a structure and insert it into the generict
 * WARNING: the record is not initialized
 */
static inline ctx_config_t *alloc_config_structure(void) {
  ctx_config_elem_t *new_elem;

  new_elem = (ctx_config_elem_t *) safe_malloc(sizeof(ctx_config_elem_t));
  list_insert_next(&generic_list, &new_elem->header);
  return &new_elem->config;
}

static inline param_t *alloc_param_structure(void) {
  param_structure_elem_t *new_elem;

  new_elem = (param_structure_elem_t *) safe_malloc(sizeof(param_structure_elem_t));
  list_insert_next(&generic_list, &new_elem->header);
  return &new_elem->param;
}

/*
 * Remove a strcuture form the generic list
 */
static inline void free_config_structure(ctx_config_t *c) {
  dl_list_t *elem;

  elem = header_of_config_structure(c);
  list_remove(elem);
  safe_free(elem);
}

static inline void free_param_structure(param_t *p) {
  dl_list_t *elem;

  elem = header_of_param_structure(p);
  list_remove(elem);
  safe_free(elem);
}


/*
 * Empty the generic list
 */
static void free_generic_list(void) {
  dl_list_t *elem, *aux;

  elem = generic_list.next;
  while (elem != &generic_list) {
    aux = elem->next;
    safe_free(elem);
    elem = aux;
  }

  clear_list(&generic_list);
}



/***********************************
 *  PARSER AND RELATED STRUCTURES  *
 **********************************/

/*
 * Return the internal parser 
 * - initialize it to read from the given string
 * - s must be non-NULL, terminated by '\0'
 */
static parser_t *get_parser(const char *s) {
  if (parser == NULL) {
    assert(lexer == NULL && tstack == NULL);
    tstack = (tstack_t *) safe_malloc(sizeof(tstack_t));
    init_tstack(tstack);

    lexer = (lexer_t *) safe_malloc(sizeof(lexer_t));
    init_string_lexer(lexer, s, "yices");
    
    parser = (parser_t *) safe_malloc(sizeof(parser_t));
    init_parser(parser, lexer, tstack);

    // copy tstack into the global objects
    assert(__yices_globals.tstack == NULL);
    __yices_globals.tstack = tstack;

  } else {
    // reset the input string
    assert(lexer != NULL && tstack != NULL);
    reset_string_lexer(lexer, s);
  }

  return parser;
}


/*
 * Delete the internal parser, lexer, term stack
 * (it they exist)
 */
static void delete_parsing_objects(void) {
  assert(__yices_globals.tstack == tstack);

  if (parser != NULL) {
    assert(lexer != NULL && tstack != NULL);
    delete_parser(parser);
    safe_free(parser);
    parser = NULL;

    close_lexer(lexer);
    safe_free(lexer);
    lexer = NULL;

    delete_tstack(tstack);
    safe_free(tstack);
    tstack = NULL;
    __yices_globals.tstack = NULL;
  }

  assert(lexer == NULL && tstack == NULL);
}




/***************************************
 *  GLOBAL INITIALIZATION AND CLEANUP  *
 **************************************/

/*
 * Initialize the table of global objects
 */
static void init_globals(yices_globals_t *glob) {
  glob->types = &types;
  glob->terms = term_manager_get_terms(&manager);
  glob->manager = &manager;
  glob->tstack = NULL;
  glob->error = &error;
}


/*
 * Reset all to NULL
 */
static void clear_globals(yices_globals_t *glob) {
  glob->types = NULL;
  glob->terms = NULL;
  glob->manager = NULL;
  glob->tstack = NULL;
  glob->error = NULL;
}


/*
 * Initialize all global objects
 */
EXPORTED void yices_init(void) {
  error.code = NO_ERROR;

  init_yices_pp_tables();
  init_bvconstants();
  init_rationals();

  q_init(&r0);
  init_bvconstant(&bv0);

  // tables
  init_type_table(&types, INIT_TYPE_SIZE);
  init_term_manager(&manager, &types, INIT_TERM_SIZE);

  // buffer lists
  clear_list(&arith_buffer_list);
  clear_list(&bvarith_buffer_list);
  clear_list(&bvarith64_buffer_list);
  clear_list(&bvlogic_buffer_list);

  // other dynamic object lists
  clear_list(&context_list);
  clear_list(&model_list);
  clear_list(&generic_list);

  // parser etc.
  parser = NULL;
  lexer = NULL;
  tstack = NULL;

  // prepare the global table
  init_globals(&__yices_globals);
}


/*
 * Cleanup: delete all tables and internal data structures
 */
EXPORTED void yices_exit(void) {
  // parser etc.
  delete_parsing_objects();

  clear_globals(&__yices_globals);

  free_bvlogic_buffer_list();
  free_bvarith_buffer_list();
  free_bvarith64_buffer_list();
  free_arith_buffer_list();

  free_context_list();
  free_model_list();
  free_generic_list();

  delete_term_manager(&manager);
  delete_type_table(&types);

  q_clear(&r0);
  delete_bvconstant(&bv0);

  cleanup_rationals();
  cleanup_bvconstants();
}



/*
 * Get the last error report
 */
EXPORTED error_report_t *yices_error_report(void) {
  return &error;
}


/*
 * Get the last error code
 */
EXPORTED error_code_t yices_error_code(void) {
  return error.code;
}


/*
 * Clear the last error report
 */
EXPORTED void yices_clear_error(void) {
  error.code = NO_ERROR;
}


/*
 * Print an error message on f
 */
EXPORTED void yices_print_error(FILE *f) {
  print_error(f);
}




/***********************
 *  BUFFER ALLOCATION  *
 **********************/

/*
 * These functions are not part of the API.
 * They are exported to be used by other yices modules.
 */


/*
 * Short cuts: extract manager components
 */
static inline term_table_t *get_terms(void) {
  return term_manager_get_terms(&manager);
}

static inline pprod_table_t *get_pprods(void) {
  return term_manager_get_pprods(&manager);
}

static inline node_table_t *get_nodes(void) {
  return term_manager_get_nodes(&manager);
}

static inline object_store_t *get_arith_store(void) {
  return term_manager_get_arith_store(&manager);
}

static inline object_store_t *get_bvarith_store(void) {
  return term_manager_get_bvarith_store(&manager);
}

static inline object_store_t *get_bvarith64_store(void) {
  return term_manager_get_bvarith64_store(&manager);
}


static inline arith_buffer_t *get_arith_buffer(void) {
  return term_manager_get_arith_buffer(&manager);
}

static inline bvarith_buffer_t *get_bvarith_buffer(void) {
  return term_manager_get_bvarith_buffer(&manager);
}

static inline bvarith64_buffer_t *get_bvarith64_buffer(void) {
  return term_manager_get_bvarith64_buffer(&manager);
}

static inline bvlogic_buffer_t *get_bvlogic_buffer(void) {
  return term_manager_get_bvlogic_buffer(&manager);
}




/*
 * Allocate an arithmetic buffer, initialized to the zero polynomial.
 * Add it to the buffer list
 */
arith_buffer_t *yices_new_arith_buffer(void) {
  arith_buffer_t *b;
  
  b = alloc_arith_buffer();
  init_arith_buffer(b, get_pprods(), get_arith_store());
  return b;
}


/*
 * Free an allocated buffer
 */
void yices_free_arith_buffer(arith_buffer_t *b) {
  delete_arith_buffer(b);
  free_arith_buffer(b);
}


/*
 * Allocate and initialize a bvarith_buffer
 * - the buffer is initialized to 0b0...0 (with n bits)
 * - n must be positive and no more than YICES_MAX_BVSIZE
 */
bvarith_buffer_t *yices_new_bvarith_buffer(uint32_t n) {
  bvarith_buffer_t *b;

  b = alloc_bvarith_buffer();
  init_bvarith_buffer(b, get_pprods(), get_bvarith_store());
  bvarith_buffer_prepare(b, n);

  return b;
}


/*
 * Free an allocated bvarith_buffer
 */
void yices_free_bvarith_buffer(bvarith_buffer_t *b) {
  delete_bvarith_buffer(b);
  free_bvarith_buffer(b);
}


/*
 * Allocate and initialize a bvarith64_buffer
 * - the buffer is initialized to 0b0000..0 (with n bits)
 * - n must be between 1 and 64
 */
bvarith64_buffer_t *yices_new_bvarith64_buffer(uint32_t n) {
  bvarith64_buffer_t *b;

  b = alloc_bvarith64_buffer();
  init_bvarith64_buffer(b, get_pprods(), get_bvarith64_store());
  bvarith64_buffer_prepare(b, n);

  return b;
}


/*
 * Free an allocated bvarith64_buffer
 */
void yices_free_bvarith64_buffer(bvarith64_buffer_t *b) {
  delete_bvarith64_buffer(b);
  free_bvarith64_buffer(b);
}


/*
 * Allocate and initialize a bvlogic buffer
 * - the buffer is empty (bitsize = 0)
 */
bvlogic_buffer_t *yices_new_bvlogic_buffer(void) {
  bvlogic_buffer_t *b;

  b = alloc_bvlogic_buffer();
  init_bvlogic_buffer(b, get_nodes());

  return b;
}


/*
 * Free buffer b allocated by the previous function
 */
void yices_free_bvlogic_buffer(bvlogic_buffer_t *b) {
  bvlogic_buffer_clear(b);
  delete_bvlogic_buffer(b);
  free_bvlogic_buffer(b);
}



/***************
 *  ITERATORS  *
 **************/

void arith_buffer_iterate(void *aux, void (*f)(void *, arith_buffer_t *)) {
  dl_list_t *elem;

  for (elem = arith_buffer_list.next;
       elem != &arith_buffer_list;
       elem = elem->next) {
    f(aux, arith_buffer(elem));
  }
}

void bvarith_buffer_iterate(void *aux, void (*f)(void *, bvarith_buffer_t *)) {
  dl_list_t *elem;

  for (elem = bvarith_buffer_list.next;
       elem != &bvarith_buffer_list;
       elem = elem->next) {
    f(aux, bvarith_buffer(elem));
  }
}

void bvarith64_buffer_iterate(void *aux, void (*f)(void *, bvarith64_buffer_t *)) {
  dl_list_t *elem;

  for (elem = bvarith64_buffer_list.next;
       elem != &bvarith64_buffer_list;
       elem = elem->next) {
    f(aux, bvarith64_buffer(elem));
  }
}

void bvlogic_buffer_iterate(void *aux, void (*f)(void *, bvlogic_buffer_t *)) {
  dl_list_t *elem;

  for (elem = bvlogic_buffer_list.next;
       elem != &bvlogic_buffer_list;
       elem = elem->next) {
    f(aux, bvlogic_buffer(elem));
  }
}

void context_iterate(void *aux, void (*f)(void *, context_t *)) {
  dl_list_t *elem;

  for (elem = context_list.next;
       elem != &context_list;
       elem = elem->next) {
    f(aux, context_of_header(elem));
  }
}

void model_iterate(void *aux, void (*f)(void *, model_t *)) {
  dl_list_t *elem;

  for (elem = context_list.next;
       elem != &context_list;
       elem = elem->next) {
    f(aux, model_of_header(elem));
  }
}



/******************
 *  TYPECHECKING  *
 *****************/

/*
 * All check_ functions return true if the check succeeds.
 * Otherwise they return false and set the error code and diagnostic data.
 */

// Check whether n is positive
static bool check_positive(uint32_t n) {
  if (n == 0) {
    error.code = POS_INT_REQUIRED;
    error.badval = n;
    return false;
  }
  return true;
}

// Check whether n is less than YICES_MAX_ARITY
static bool check_arity(uint32_t n) {
  if (n > YICES_MAX_ARITY) {
    error.code = TOO_MANY_ARGUMENTS;
    error.badval = n;
    return false;
  }
  return true;
}

// Check whether n is less than YICES_MAX_VARS
static bool check_maxvars(uint32_t n) {
  if (n > YICES_MAX_VARS) {
    error.code = TOO_MANY_VARS;
    error.badval = n;
    return false;
  }
  return true;
}

// Check whether n is less than YICES_MAX_BVSIZE
static bool check_maxbvsize(uint32_t n) {
  if (n > YICES_MAX_BVSIZE) {
    error.code = MAX_BVSIZE_EXCEEDED;
    error.badval = n;
    return false;
  }
  return true;
}

// Check whether d is no more than YICES_MAX_DEGREE
static bool check_maxdegree(uint32_t d) {
  if (d > YICES_MAX_DEGREE) {
    error.code = DEGREE_OVERFLOW;
    error.badval = d;
    return false;
  }
  return true;
}

// Check whether tau is a valid type
static bool check_good_type(type_table_t *tbl, type_t tau) {
  if (bad_type(tbl, tau)) { 
    error.code = INVALID_TYPE;
    error.type1 = tau;
    return false;
  }
  return true;
}

// Check whether all types in a[0 ... n-1] are valid
static bool check_good_types(type_table_t *tbl, uint32_t n, type_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (bad_type(tbl, a[i])) {
      error.code = INVALID_TYPE;
      error.type1 = a[i];
      return false;
    }
  }
  return true;
}

// Check whether tau is uninterpreted or scalar, and whether 
// i a valid constant index for type tau.
static bool check_good_constant(type_table_t *tbl, type_t tau, int32_t i) {
  type_kind_t kind;

  if (bad_type(tbl, tau)) {
    error.code = INVALID_TYPE;
    error.type1 = tau;
    return false;
  }
  kind = type_kind(tbl, tau);
  if (kind != UNINTERPRETED_TYPE && kind != SCALAR_TYPE) {
    error.code = SCALAR_OR_UTYPE_REQUIRED;
    error.type1 = tau;
    return false;
  }
  if (i < 0 || 
      (kind == SCALAR_TYPE && i >= scalar_type_cardinal(tbl, tau))) {
    error.code = INVALID_CONSTANT_INDEX;
    error.type1 = tau;
    error.badval = i;
    return false;
  }
  return true;
}

// Check whether t is a valid term
static bool check_good_term(term_manager_t *mngr, term_t t) {
  term_table_t *tbl;

  tbl = term_manager_get_terms(mngr);
  if (bad_term(tbl, t)) {
    error.code = INVALID_TERM;
    error.term1 = t;
    return false;
  }
  return true;
}

// Check that terms in a[0 ... n-1] are valid
static bool check_good_terms(term_manager_t *mngr, uint32_t n, term_t *a) {
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    if (bad_term(tbl, a[i])) {
      error.code = INVALID_TERM;
      error.term1 = a[i];
      return false;
    }
  }
  return true;
}

// check that terms a[0 ... n-1] have types that match tau[0 ... n-1].
static bool check_arg_types(term_manager_t *mngr, uint32_t n, term_t *a, type_t *tau) {
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    if (! is_subtype(tbl->types, term_type(tbl, a[i]), tau[i])) {
      error.code = TYPE_MISMATCH;
      error.term1 = a[i];
      error.type1 = tau[i];
      return false;
    }
  }

  return true;
}

// check whether (f a[0] ... a[n-1]) is typecorrect
static bool check_good_application(term_manager_t *mngr, term_t f, uint32_t n, term_t *a) {
  term_table_t *tbl;
  function_type_t *ft;

  if (! check_positive(n) || 
      ! check_good_term(mngr, f) || 
      ! check_good_terms(mngr, n, a)) {
    return false;
  }

  tbl = term_manager_get_terms(mngr);

  if (! is_function_term(tbl, f)) {
    error.code = FUNCTION_REQUIRED;
    error.term1 = f;
    return false;
  }  

  ft = function_type_desc(tbl->types, term_type(tbl, f));
  if (n != ft->ndom) {
    error.code = WRONG_NUMBER_OF_ARGUMENTS;
    error.type1 = term_type(tbl, f);
    error.badval = n;
    return false;
  }

  return check_arg_types(mngr, n, a, ft->domain);
}

// Check whether t is a boolean term. t must be a valid term
static bool check_boolean_term(term_manager_t *mngr, term_t t) {
  term_table_t *tbl;

  tbl = term_manager_get_terms(mngr);

  if (! is_boolean_term(tbl, t)) {
    error.code = TYPE_MISMATCH;
    error.term1 = t;
    error.type1 = bool_type(tbl->types);
    return false;
  }
  return true;
}

// Check whether t is an arithmetic term, t must be valid.
static bool check_arith_term(term_manager_t *mngr, term_t t) {
  term_table_t *tbl;

  tbl = term_manager_get_terms(mngr);

  if (! is_arithmetic_term(tbl, t)) {
    error.code = ARITHTERM_REQUIRED;
    error.term1 = t;
    return false;
  }
  return true;
}

// Check whether t is a bitvector term, t must be valid
static bool check_bitvector_term(term_manager_t *mngr, term_t t) {
  term_table_t *tbl;

  tbl = term_manager_get_terms(mngr);

  if (! is_bitvector_term(tbl, t)) {
    error.code = BITVECTOR_REQUIRED;
    error.term1 = t;
    return false;
  }
  return true;
}

// Check whether t1 and t2 have compatible types (i.e., (= t1 t2) is well-typed)
// t1 and t2 must both be valid
static bool check_compatible_terms(term_manager_t *mngr, term_t t1, term_t t2) {
  term_table_t *tbl;
  type_t tau1, tau2;

  tbl = term_manager_get_terms(mngr);

  tau1 = term_type(tbl, t1);
  tau2 = term_type(tbl, t2);
  if (! compatible_types(tbl->types, tau1, tau2)) {
    error.code = INCOMPATIBLE_TYPES;
    error.term1 = t1;
    error.type1 = tau1;
    error.term2 = t2;
    error.type2 = tau2;
    return false;
  }

  return true;
}

// Check whether (= t1 t2) is type correct
static bool check_good_eq(term_manager_t *mngr, term_t t1, term_t t2) {
  return check_good_term(mngr, t1) && check_good_term(mngr, t2) &&
    check_compatible_terms(mngr, t1, t2);
}

// Check whether t1 and t2 are two valid arithmetic terms
static bool check_both_arith_terms(term_manager_t *mngr, term_t t1, term_t t2) {
  return check_good_term(mngr, t1) && check_good_term(mngr, t2) &&
    check_arith_term(mngr, t1) && check_arith_term(mngr, t2);
}


// Check that t1 and t2 are bitvectors of the same size
static bool check_compatible_bv_terms(term_manager_t *mngr, term_t t1, term_t t2) {
  return check_good_term(mngr, t1) && check_good_term(mngr, t2)
    && check_bitvector_term(mngr, t1) && check_bitvector_term(mngr, t2) 
    && check_compatible_terms(mngr, t1, t2);
}

// Check whether terms a[0 ... n-1] are all boolean
static bool check_boolean_args(term_manager_t *mngr, uint32_t n, term_t *a) {
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    if (! is_boolean_term(tbl, a[i])) {
      error.code = TYPE_MISMATCH;
      error.term1 = a[i];
      error.type1 = bool_type(tbl->types);
      return false;
    }
  }

  return true;
}

// Check whether terms a[0 ... n-1] are all arithmetic terms
static bool check_arithmetic_args(term_manager_t *mngr, uint32_t n, term_t *a) {
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    if (! is_arithmetic_term(tbl, a[i])) {
      error.code = ARITHTERM_REQUIRED;
      error.term1 = a[i];
      return false;
    }
  }

  return true;
}


// Check wether all numbers den[0 ... n-1] are positive
static bool check_denominators32(uint32_t n, uint32_t *den) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (den[i] == 0) {
      error.code = DIVISION_BY_ZERO;
      return false;
    }
  }

  return true;
}


static bool check_denominators64(uint32_t n, uint64_t *den) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (den[i] == 0) {
      error.code = DIVISION_BY_ZERO;
      return false;
    }
  }

  return true;
}


// Check whether (tuple-select i t) is well-typed
static bool check_good_select(term_manager_t *mngr, uint32_t i, term_t t) {
  term_table_t *tbl;
  type_t tau;

  if (! check_good_term(mngr, t)) {
    return false;
  }

  tbl = term_manager_get_terms(mngr);

  tau = term_type(tbl, t);
  if (type_kind(tbl->types, tau) != TUPLE_TYPE) {
    error.code = TUPLE_REQUIRED;
    error.term1 = t;
    return false;
  }

  if (i >= tuple_type_arity(tbl->types, tau)) {
    error.code = INVALID_TUPLE_INDEX;
    error.type1 = tau;
    error.badval = i;
    return false;
  }
  
  return true;
}

// Check that (update f (a_1 ... a_n) v) is well typed
static bool check_good_update(term_manager_t *mngr, term_t f, uint32_t n, term_t *a, term_t v) {
  term_table_t *tbl;
  function_type_t *ft;

  if (! check_positive(n) || 
      ! check_good_term(mngr, f) ||
      ! check_good_term(mngr, v) ||
      ! check_good_terms(mngr, n, a)) {
    return false;
  }

  tbl = term_manager_get_terms(mngr);

  if (! is_function_term(tbl, f)) {
    error.code = FUNCTION_REQUIRED;
    error.term1 = f;
    return false;
  }  

  ft = function_type_desc(tbl->types, term_type(tbl, f));
  if (n != ft->ndom) {
    error.code = WRONG_NUMBER_OF_ARGUMENTS;
    error.type1 = term_type(tbl, f);
    error.badval = n;
    return false;
  }

  if (! is_subtype(tbl->types, term_type(tbl, v), ft->range)) {
    error.code = TYPE_MISMATCH;
    error.term1 = v;
    error.type1 = ft->range;
    return false;
  }

  return check_arg_types(mngr, n, a, ft->domain);
}

// Check (distinct t_1 ... t_n)
static bool check_good_distinct_term(term_manager_t *mngr, uint32_t n, term_t *a) {
  term_table_t *tbl;
  uint32_t i;
  type_t tau;

  if (! check_positive(n) ||
      ! check_arity(n) ||
      ! check_good_terms(mngr, n, a)) {
    return false;
  }

  tbl = term_manager_get_terms(mngr);

  tau = term_type(tbl, a[0]); 
  for (i=1; i<n; i++) {
    tau = super_type(tbl->types, tau, term_type(tbl, a[i]));
    if (tau == NULL_TYPE) {
      error.code = INCOMPATIBLE_TYPES;
      error.term1 = a[0];
      error.type1 = term_type(tbl, a[0]);
      error.term2 = a[i];
      error.type2 = term_type(tbl, a[i]);
      return false;
    }
  }

  return true;
}

// Check quantified formula (FORALL/EXISTS (v_1 ... v_n) body)
// v must be sorted.
static bool check_good_quantified_term(term_manager_t *mngr, uint32_t n, term_t *v, term_t body) {
  term_table_t *tbl;
  int32_t i;

  if (! check_positive(n) ||
      ! check_maxvars(n) ||
      ! check_good_term(mngr, body) ||
      ! check_good_terms(mngr, n, v) ||
      ! check_boolean_term(mngr, body)) {
    return false;
  }

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    if (term_kind(tbl, v[i]) != VARIABLE) {      
      error.code = VARIABLE_REQUIRED;
      error.term1 = v[i];
      return false;
    }
  }

  for (i=1; i<n; i++) {
    if (v[i-1] == v[i]) {
      error.code = DUPLICATE_VARIABLE;
      error.term1 = v[i];
      return false;
    }
  }

  return true;
}

// Check whether (tuple-select i t v) is well-typed
static bool check_good_tuple_update(term_manager_t *mngr, uint32_t i, term_t t, term_t v) {
  term_table_t *tbl;
  type_t tau;
  tuple_type_t *desc;

  if (! check_good_term(mngr, t) ||
      ! check_good_term(mngr, v)) {
    return false;
  }

  tbl = term_manager_get_terms(mngr);

  tau = term_type(tbl, t);
  if (type_kind(tbl->types, tau) != TUPLE_TYPE) {
    error.code = TUPLE_REQUIRED;
    error.term1 = t;
    return false;
  }

  desc = tuple_type_desc(tbl->types, tau);
  if (i >= desc->nelem) {
    error.code = INVALID_TUPLE_INDEX;
    error.type1 = tau;
    error.badval = i;
    return false;
  }

  if (! is_subtype(tbl->types, term_type(tbl, v), desc->elem[i])) {
    error.code = TYPE_MISMATCH;
    error.term1 = v;
    error.type1 = desc->elem[i];
    return false;
  }
  
  return true;
}

// Check that the degree of t1 * t2 is at most MAX_DEGREE
static bool check_product_degree(term_manager_t *mngr, term_t t1, term_t t2) {
  term_table_t *tbl;
  uint32_t d1, d2;

  tbl = term_manager_get_terms(mngr);

  d1 = term_degree(tbl, t1);
  d2 = term_degree(tbl, t2);
  assert(d1 <= YICES_MAX_DEGREE && d2 <= YICES_MAX_DEGREE);

  return check_maxdegree(d1 + d2);
}


// Check that the degree of t^2 does not overflow
static bool check_square_degree(term_manager_t *mngr, term_t t) {
  term_table_t *tbl;
  uint32_t d;

  tbl = term_manager_get_terms(mngr);
  d = term_degree(tbl, t);
  assert(d <= YICES_MAX_DEGREE);

  return check_maxdegree(d + d);
}

// Check that the degree of t^n does not overflow
static bool check_power_degree(term_manager_t *mngr, term_t t, uint32_t n) {
  term_table_t *tbl;
  uint64_t d;

  tbl = term_manager_get_terms(mngr);

  d = term_degree(tbl, t) * n;
  if (d > ((uint64_t) UINT32_MAX)) {
    error.code = DEGREE_OVERFLOW;
    error.badval = UINT32_MAX;
    return false;
  }

  return check_maxdegree((uint32_t) d);
}


// Check whether i is a valid shift for bitvectors of size n
static bool check_bitshift(uint32_t i, uint32_t n) {
  if (i > n) {
    error.code = INVALID_BITSHIFT;
    error.badval = i;
    return false;
  }

  return true;
}

// Check whether [i, j] is a valid segment for bitvectors of size n
static bool check_bitextract(uint32_t i, uint32_t j, uint32_t n) {
  if (i > j || j >= n) {
    error.code = INVALID_BVEXTRACT;
    return false;
  }
  return true;
}



/***********************
 *  TYPE CONSTRUCTORS  *
 **********************/

EXPORTED type_t yices_bool_type(void) {
  return bool_type(&types);
}

EXPORTED type_t yices_int_type(void) {
  return int_type(&types);
}

EXPORTED type_t yices_real_type(void) {
  return real_type(&types);
}

EXPORTED type_t yices_bv_type(uint32_t size) {
  if (! check_positive(size) || ! check_maxbvsize(size)) {
    return NULL_TYPE;
  }
  return bv_type(&types, size);
}

EXPORTED type_t yices_new_uninterpreted_type(void) {
  return new_uninterpreted_type(&types);
}

EXPORTED type_t yices_new_scalar_type(uint32_t card) {
  if (! check_positive(card)) {
    return NULL_TYPE;
  }
  return new_scalar_type(&types, card);
}

EXPORTED type_t yices_tuple_type(uint32_t n, type_t elem[]) {
  if (! check_positive(n) || 
      ! check_arity(n) ||
      ! check_good_types(&types, n, elem)) {
    return NULL_TYPE;
  }
  return tuple_type(&types, n, elem);
}

EXPORTED type_t yices_function_type(uint32_t n, type_t dom[], type_t range) {
  if (! check_positive(n) || 
      ! check_arity(n) ||
      ! check_good_type(&types, range) || 
      ! check_good_types(&types, n, dom)) {
    return NULL_TYPE;
  }
  return function_type(&types, range, n, dom);
}






/***********************
 *  TERM CONSTRUCTORS  *
 **********************/

/*
 * When constructing a term to singleton type tau, we always
 * return the representative for tau (except for variables).
 */
EXPORTED term_t yices_true(void) {
  return true_term;
}

EXPORTED term_t yices_false(void) {
  return false_term;
}

EXPORTED term_t yices_constant(type_t tau, int32_t index) {
  if (! check_good_constant(&types, tau, index)) {
    return NULL_TERM;
  }

  return mk_constant(&manager, tau, index);
}

EXPORTED term_t yices_new_uninterpreted_term(type_t tau) {
  if (! check_good_type(&types, tau)) {
    return NULL_TERM;
  }

  return mk_uterm(&manager, tau);
}

EXPORTED term_t yices_new_variable(type_t tau) {
  if (! check_good_type(&types, tau)) {
    return NULL_TERM;
  }

  return mk_variable(&manager, tau);
}

EXPORTED term_t yices_application(term_t fun, uint32_t n, term_t arg[]) {
  if (! check_good_application(&manager, fun, n, arg)) {
    return NULL_TERM;
  }

  return mk_application(&manager, fun, n, arg);
}

EXPORTED term_t yices_ite(term_t cond, term_t then_term, term_t else_term) {
  term_table_t *tbl;
  type_t tau;

  // Check type correctness: first steps
  if (! check_good_term(&manager, cond) || 
      ! check_good_term(&manager, then_term) ||
      ! check_good_term(&manager, else_term) || 
      ! check_boolean_term(&manager, cond)) {
    return NULL_TERM;
  }

  // Check whether then/else are compatible and get the supertype
  tbl = get_terms();
  tau = super_type(&types, term_type(tbl, then_term), term_type(tbl, else_term));

  if (tau == NULL_TYPE) {
    // type error
    error.code = INCOMPATIBLE_TYPES;
    error.term1 = then_term;
    error.type1 = term_type(tbl, then_term);
    error.term2 = else_term;
    error.type2 = term_type(tbl, else_term);
    return NULL_TERM;
  }

  return mk_ite(&manager, cond, then_term, else_term, tau);
}


EXPORTED term_t yices_eq(term_t left, term_t right) {
  if (! check_good_eq(&manager, left, right)) {
    return NULL_TERM;
  }

  return mk_eq(&manager, left, right);
}

EXPORTED term_t yices_neq(term_t left, term_t right) {
  if (! check_good_eq(&manager, left, right)) {
    return NULL_TERM;
  }

  return mk_neq(&manager, left, right);
}

/*
 * BOOLEAN NEGATION
 */
EXPORTED term_t yices_not(term_t arg) {
  if (! check_good_term(&manager, arg) || 
      ! check_boolean_term(&manager, arg)) {
    return NULL_TERM;
  }

  return opposite_term(arg);
}


/*
 * OR, AND, and XOR may modify arg
 */
EXPORTED term_t yices_or(uint32_t n, term_t arg[]) {
  if (! check_arity(n) ||
      ! check_good_terms(&manager, n, arg) || 
      ! check_boolean_args(&manager, n, arg)) {
    return NULL_TERM;
  }

  switch (n) {
  case 0:
    return false_term;
  case 1:
    return arg[0];
  case 2:
    return mk_binary_or(&manager, arg[0], arg[1]);
  default:
    return mk_or(&manager, n, arg);
  }
}

EXPORTED term_t yices_and(uint32_t n, term_t arg[]) {
  if (! check_arity(n) ||
      ! check_good_terms(&manager, n, arg) || 
      ! check_boolean_args(&manager, n, arg)) {
    return NULL_TERM;
  }

  switch (n) {
  case 0:
    return true_term;
  case 1:
    return arg[0];
  case 2:
    return mk_binary_and(&manager, arg[0], arg[1]);
  default:
    return mk_and(&manager, n, arg);
  }
}

EXPORTED term_t yices_xor(uint32_t n, term_t arg[]) {
  if (! check_arity(n) ||
      ! check_good_terms(&manager, n, arg) || 
      ! check_boolean_args(&manager, n, arg)) {
    return NULL_TERM;
  }

  switch (n) {
  case 0:
    return false_term;
  case 1:
    return arg[0];
  case 2:
    return mk_binary_xor(&manager, arg[0], arg[1]);
  default:
    return mk_xor(&manager, n, arg);
  }
}


/*
 * BINARY VERSIONS OF OR/AND/XOR
 */
EXPORTED term_t yices_or2(term_t left, term_t right) {
  if (! check_good_term(&manager, left) ||
      ! check_good_term(&manager, right) || 
      ! check_boolean_term(&manager, left) || 
      ! check_boolean_term(&manager, right)) {
    return NULL_TERM;
  }

  return mk_binary_or(&manager, left, right);
}

EXPORTED term_t yices_and2(term_t left, term_t right) {
  if (! check_good_term(&manager, left) ||
      ! check_good_term(&manager, right) || 
      ! check_boolean_term(&manager, left) || 
      ! check_boolean_term(&manager, right)) {
    return NULL_TERM;
  }

  return mk_binary_and(&manager, left, right);
}

EXPORTED term_t yices_xor2(term_t left, term_t right) {
  if (! check_good_term(&manager, left) ||
      ! check_good_term(&manager, right) || 
      ! check_boolean_term(&manager, left) || 
      ! check_boolean_term(&manager, right)) {
    return NULL_TERM;
  }

  return mk_binary_xor(&manager, left, right);
}

EXPORTED term_t yices_iff(term_t left, term_t right) {
  if (! check_good_term(&manager, left) ||
      ! check_good_term(&manager, right) || 
      ! check_boolean_term(&manager, left) || 
      ! check_boolean_term(&manager, right)) {
    return NULL_TERM;
  }

  return mk_iff(&manager, left, right);
}

EXPORTED term_t yices_implies(term_t left, term_t right) {
  if (! check_good_term(&manager, left) ||
      ! check_good_term(&manager, right) || 
      ! check_boolean_term(&manager, left) || 
      ! check_boolean_term(&manager, right)) {
    return NULL_TERM;
  }

  return mk_implies(&manager, left, right);
}


EXPORTED term_t yices_tuple(uint32_t n, term_t arg[]) {
  if (! check_positive(n) || 
      ! check_arity(n) ||
      ! check_good_terms(&manager, n, arg)) {
    return NULL_TERM;
  }

  return mk_tuple(&manager, n, arg);
}

EXPORTED term_t yices_select(uint32_t index, term_t tuple) {
  if (! check_good_select(&manager, index, tuple)) {
    return NULL_TERM;
  }

  return mk_select(&manager, index, tuple);
}

EXPORTED term_t yices_update(term_t fun, uint32_t n, term_t arg[], term_t new_v) {
  if (! check_good_update(&manager, fun, n, arg, new_v)) {
    return NULL_TERM;
  }

  return mk_update(&manager, fun, n, arg, new_v);
}

EXPORTED term_t yices_distinct(uint32_t n, term_t arg[]) {
  if (! check_positive(n) ||
      ! check_arity(n) ||
      ! check_good_distinct_term(&manager, n, arg)) {
    return NULL_TERM;
  }
  
  return mk_distinct(&manager, n, arg);
}

EXPORTED term_t yices_tuple_update(term_t tuple, uint32_t index, term_t new_v) {
  if (! check_good_tuple_update(&manager, index, tuple, new_v)) {
    return NULL_TERM;
  }

  return mk_tuple_update(&manager, tuple, index, new_v);
}

EXPORTED term_t yices_forall(uint32_t n, term_t var[], term_t body) {
  if (n > 1) {
    int_array_sort(var, n);    
  }

  if (! check_good_quantified_term(&manager, n, var, body)) {
    return NULL_TERM;
  }

  return mk_forall(&manager, n, var, body);
}

EXPORTED term_t yices_exists(uint32_t n, term_t var[], term_t body) {
  if (n > 1) { 
    int_array_sort(var, n);    
  }

  if (! check_good_quantified_term(&manager, n, var, body)) {
    return NULL_TERM;
  }

  return mk_exists(&manager, n, var, body);
}




/*************************
 *  RATIONAL CONSTANTS   *
 ************************/

/*
 * Integer constants
 */
EXPORTED term_t yices_zero(void) {
  return zero_term;
}

EXPORTED term_t yices_int32(int32_t val) {
  q_set32(&r0, val);
  return  mk_arith_constant(&manager, &r0);
}

EXPORTED term_t yices_int64(int64_t val) {
  q_set64(&r0, val);
  return mk_arith_constant(&manager, &r0);
}


/*
 * Rational constants
 */
EXPORTED term_t yices_rational32(int32_t num, uint32_t den) {
  if (den == 0) {
    error.code = DIVISION_BY_ZERO;
    return NULL_TERM;
  }

  q_set_int32(&r0, num, den);
  return mk_arith_constant(&manager, &r0);
}

EXPORTED term_t yices_rational64(int64_t num, uint64_t den) {
  if (den == 0) {
    error.code = DIVISION_BY_ZERO;
    return NULL_TERM;
  }

  q_set_int64(&r0, num, den);
  return mk_arith_constant(&manager, &r0);
}


/*
 * Constant from GMP integers or rationals
 */
EXPORTED term_t yices_mpz(mpz_t z) {
  term_t t;

  q_set_mpz(&r0, z);
  t = mk_arith_constant(&manager, &r0);
  q_clear(&r0);

  return t;
}

EXPORTED term_t yices_mpq(mpq_t q) {
  term_t t;

  q_set_mpq(&r0, q);
  t = mk_arith_constant(&manager, &r0);
  q_clear(&r0);

  return t;
}


/*
 * Convert a string to a rational or integer term. 
 * The string format is
 *     <optional_sign> <numerator>/<denominator>
 *  or <optional_sign> <numerator>
 *
 * where <optional_sign> is + or - or nothing
 * <numerator> and <denominator> are sequences of 
 * decimal digits.
 *
 * Error report:
 *    code = INVALID_RATIONAL_FORMAT
 * or code = DIVISION_BY_ZERO
 */
EXPORTED term_t yices_parse_rational(const char *s) {
  int32_t code;
  term_t t;

  code = q_set_from_string(&r0, s);
  if (code < 0) {
    if (code == -1) {
      // wrong format
      error.code = INVALID_RATIONAL_FORMAT;
    } else {
      // denominator is 0
      error.code = DIVISION_BY_ZERO;
    }
    return NULL_TERM;
  }

  t = mk_arith_constant(&manager, &r0);
  q_clear(&r0);

  return t;
}


/*
 * Convert a string in floating point format to a rational
 * The string must be in one of the following formats:
 *   <optional sign> <integer part> . <fractional part>
 *   <optional sign> <integer part> <exp> <optional sign> <integer>
 *   <optional sign> <integer part> . <fractional part> <exp> <optional sign> <integer>
 * 
 * where <optional sign> is + or - or nothing
 *       <exp> is either 'e' or 'E'
 *
 * Error report:
 * code = INVALID_FLOAT_FORMAT
 */
EXPORTED term_t yices_parse_float(const char *s) {
  term_t t;

  if (q_set_from_float_string(&r0, s) < 0) {
    // wrong format
    error.code = INVALID_FLOAT_FORMAT;
    return NULL_TERM;
  }

  t = mk_arith_constant(&manager, &r0);
  q_clear(&r0);

  return t;
}



/***************************
 *  ARITHMETIC OPERATIONS  *
 **************************/

/*
 * Add t1 and t2
 */
EXPORTED term_t yices_add(term_t t1, term_t t2) {
  arith_buffer_t *b;
  term_table_t *tbl;

  if (! check_both_arith_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = get_terms();
  arith_buffer_reset(b);
  arith_buffer_add_term(b, tbl, t1);
  arith_buffer_add_term(b, tbl, t2);

  return mk_arith_term(&manager, b);
}


/*
 * Subtract t2 from t1
 */
EXPORTED term_t yices_sub(term_t t1, term_t t2) {
  arith_buffer_t *b;
  term_table_t *tbl;

  if (! check_both_arith_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = get_terms();
  arith_buffer_reset(b);
  arith_buffer_add_term(b, tbl, t1);
  arith_buffer_sub_term(b, tbl, t2);

  return mk_arith_term(&manager, b);
}


/*
 * Negate t1
 */
EXPORTED term_t yices_neg(term_t t1) {
  arith_buffer_t *b;
  term_table_t *tbl;

  if (! check_good_term(&manager, t1) || 
      ! check_arith_term(&manager, t1)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = get_terms();
  arith_buffer_reset(b);
  arith_buffer_sub_term(b, tbl, t1);

  return mk_arith_term(&manager, b);
}


/*
 * Multiply t1 and t2
 */
EXPORTED term_t yices_mul(term_t t1, term_t t2) {
  arith_buffer_t *b;
  term_table_t *tbl;

  if (! check_both_arith_terms(&manager, t1, t2) ||
      ! check_product_degree(&manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = get_terms();
  arith_buffer_reset(b);
  arith_buffer_add_term(b, tbl, t1);
  arith_buffer_mul_term(b, tbl, t2);

  return mk_arith_term(&manager, b);
}


/*
 * Compute the square of t1
 */
EXPORTED term_t yices_square(term_t t1) {
  arith_buffer_t *b;
  term_table_t *tbl;

  if (! check_good_term(&manager, t1) || 
      ! check_arith_term(&manager, t1) ||
      ! check_square_degree(&manager, t1)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = get_terms();
  arith_buffer_reset(b);
  arith_buffer_add_term(b, tbl, t1);
  arith_buffer_mul_term(b, tbl, t1);

  return mk_arith_term(&manager, b);
}


/*
 * Compute t1 ^ d
 */
EXPORTED term_t yices_power(term_t t1, uint32_t d) {
  arith_buffer_t *b;
  term_table_t *tbl;

  if (! check_good_term(&manager, t1) || 
      ! check_arith_term(&manager, t1) ||
      ! check_power_degree(&manager, t1, d)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = get_terms();
  arith_buffer_set_one(b);
  arith_buffer_mul_term_power(b, tbl, t1, d);

  return mk_arith_term(&manager, b);
}


/*******************
 *   POLYNOMIALS   *
 ******************/

/*
 * integer coefficients
 */
EXPORTED term_t yices_poly_int32(uint32_t n, int32_t a[], term_t t[]) {
  arith_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(&manager, n, t) ||
      ! check_arithmetic_args(&manager, n, t)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = get_terms();
  arith_buffer_reset(b);
  for (i=0; i<n; i++) {
    q_set32(&r0, a[i]);
    arith_buffer_add_const_times_term(b, tbl, &r0, t[i]);
  }

  return mk_arith_term(&manager, b);  
}

EXPORTED term_t yices_poly_int64(uint32_t n, int64_t a[], term_t t[]) {
  arith_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(&manager, n, t) ||
      ! check_arithmetic_args(&manager, n, t)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = get_terms();
  arith_buffer_reset(b);
  for (i=0; i<n; i++) {
    q_set64(&r0, a[i]);
    arith_buffer_add_const_times_term(b, tbl, &r0, t[i]);
  }

  return mk_arith_term(&manager, b);  
}


/*
 * Polynomial with rational coefficients
 * - den, num, and t must be arrays of size n
 * - the coefficient a_i is den[i]/num[i]
 * 
 * Error report:
 * if num[i] is 0
 *   code = DIVISION_BY_ZERO
 */
EXPORTED term_t yices_poly_rational32(uint32_t n, int32_t num[], uint32_t den[], term_t t[]) {
  arith_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(&manager, n, t) ||
      ! check_arithmetic_args(&manager, n, t) || 
      ! check_denominators32(n, den)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = get_terms();
  arith_buffer_reset(b);
  for (i=0; i<n; i++) {
    q_set_int32(&r0, num[i], den[i]);
    arith_buffer_add_const_times_term(b, tbl, &r0, t[i]);
  }

  return mk_arith_term(&manager, b);  
}

EXPORTED term_t yices_poly_rational64(uint32_t n, int64_t num[], uint64_t den[], term_t t[]) {
  arith_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(&manager, n, t) ||
      ! check_arithmetic_args(&manager, n, t) ||
      ! check_denominators64(n, den)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = get_terms();
  arith_buffer_reset(b);
  for (i=0; i<n; i++) {
    q_set_int64(&r0, num[i], den[i]);
    arith_buffer_add_const_times_term(b, tbl, &r0, t[i]);
  }

  return mk_arith_term(&manager, b);  
}


/*
 * GMP integers and rationals
 */
EXPORTED term_t yices_poly_mpz(uint32_t n, mpz_t z[], term_t t[]) {
  arith_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(&manager, n, t) ||
      ! check_arithmetic_args(&manager, n, t)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = get_terms();
  arith_buffer_reset(b);
  for (i=0; i<n; i++) {
    q_set_mpz(&r0, z[i]);
    arith_buffer_add_const_times_term(b, tbl, &r0, t[i]);
  }

  q_clear(&r0);

  return mk_arith_term(&manager, b);  
}


EXPORTED term_t yices_poly_mpq(uint32_t n, mpq_t q[], term_t t[]) {
  arith_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(&manager, n, t) ||
      ! check_arithmetic_args(&manager, n, t)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = get_terms();
  arith_buffer_reset(b);
  for (i=0; i<n; i++) {
    q_set_mpq(&r0, q[i]);
    arith_buffer_add_const_times_term(b, tbl, &r0, t[i]);
  }

  q_clear(&r0);

  return mk_arith_term(&manager, b);  
}






/**********************
 *  ARITHMETIC ATOMS  *
 *********************/

EXPORTED term_t yices_arith_eq_atom(term_t t1, term_t t2) {
  if (! check_both_arith_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_arith_eq(&manager, t1, t2);
}

EXPORTED term_t yices_arith_neq_atom(term_t t1, term_t t2) {
  if (! check_both_arith_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_arith_neq(&manager, t1, t2);
}

EXPORTED term_t yices_arith_geq_atom(term_t t1, term_t t2) {
  if (! check_both_arith_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_arith_geq(&manager, t1, t2);
}

EXPORTED term_t yices_arith_lt_atom(term_t t1, term_t t2) {
  if (! check_both_arith_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_arith_lt(&manager, t1, t2);
}

EXPORTED term_t yices_arith_gt_atom(term_t t1, term_t t2) {
  if (! check_both_arith_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_arith_gt(&manager, t1, t2);
}

EXPORTED term_t yices_arith_leq_atom(term_t t1, term_t t2) {
  if (! check_both_arith_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_arith_leq(&manager, t1, t2);
}


/*
 * Comparison with zero
 */
EXPORTED term_t yices_arith_eq0_atom(term_t t) {
  if (! check_good_term(&manager, t) || 
      ! check_arith_term(&manager, t)) {
    return NULL_TERM;
  }
  return mk_arith_term_eq0(&manager, t);
}

EXPORTED term_t yices_arith_neq0_atom(term_t t) {
  if (! check_good_term(&manager, t) || 
      ! check_arith_term(&manager, t)) {
    return NULL_TERM;
  }
  return mk_arith_term_neq0(&manager, t);
}

EXPORTED term_t yices_arith_geq0_atom(term_t t) {
  if (! check_good_term(&manager, t) || 
      ! check_arith_term(&manager, t)) {
    return NULL_TERM;
  }
  return mk_arith_term_geq0(&manager, t);
}

EXPORTED term_t yices_arith_leq0_atom(term_t t) {
  if (! check_good_term(&manager, t) || 
      ! check_arith_term(&manager, t)) {
    return NULL_TERM;
  }
  return mk_arith_term_leq0(&manager, t);
}

EXPORTED term_t yices_arith_gt0_atom(term_t t) {
  if (! check_good_term(&manager, t) || 
      ! check_arith_term(&manager, t)) {
    return NULL_TERM;
  }
  return mk_arith_term_gt0(&manager, t);
}

EXPORTED term_t yices_arith_lt0_atom(term_t t) {
  if (! check_good_term(&manager, t) || 
      ! check_arith_term(&manager, t)) {
    return NULL_TERM;
  }
  return mk_arith_term_lt0(&manager, t);
}



/**************************
 *  BITVECTOR CONSTANTS   *
 *************************/

EXPORTED term_t yices_bvconst_uint32(uint32_t n, uint32_t x) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set32(bv0.data, bv0.width, x);

  return mk_bv_constant(&manager, &bv0);
}

EXPORTED term_t yices_bvconst_uint64(uint32_t n, uint64_t x) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set64(bv0.data, bv0.width, x);

  return mk_bv_constant(&manager, &bv0);
}

EXPORTED term_t yices_bvconst_mpz(uint32_t n, mpz_t x) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set_mpz(bv0.data, bv0.width, x);

  return mk_bv_constant(&manager, &bv0);
}


/*
 * bvconst_zero: set all bits to 0
 * bvconst_one: set low-order bit to 1, all the others to 0
 * bvconst_minus_one: set all bits to 1
 */
EXPORTED term_t yices_bvconst_zero(uint32_t n) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_all_zero(&bv0, n);

  return mk_bv_constant(&manager, &bv0);
}

EXPORTED term_t yices_bvconst_one(uint32_t n) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }
  
  bvconstant_set_bitsize(&bv0, n);
  bvconst_set_one(bv0.data, bv0.width);

  return mk_bv_constant(&manager, &bv0);
}

EXPORTED term_t yices_bvconst_minus_one(uint32_t n) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_all_one(&bv0, n);

  return mk_bv_constant(&manager, &bv0);
}


/*
 * Convert an integer array to a bit constant
 * - a[i] =  0 --> bit i = 0
 * - a[i] != 0 --> bit i = 1
 */
EXPORTED term_t yices_bvconst_from_array(uint32_t n, int32_t a[]) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set_array(bv0.data, a, n);

  return mk_bv_constant(&manager, &bv0);
}



/*
 * Parse a string of '0' and '1' and convert to a bit constant
 * - the number of bits is the length of s
 * - the string is in read in big-endian format: the first character
 *   is the high-order bit.
 */
EXPORTED term_t yices_parse_bvbin(const char *s) {
  uint32_t n;
  int32_t code;

  n = strlen(s);
  if (n == 0) {
    error.code = INVALID_BVBIN_FORMAT;
    return NULL_TERM;
  }

  if (! check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_bitsize(&bv0, n);
  code = bvconst_set_from_string(bv0.data, n, s);
  if (code < 0) {
    error.code = INVALID_BVBIN_FORMAT;
    return NULL_TERM;    
  }

  return mk_bv_constant(&manager, &bv0);
}


/*
 * Parse a string of hexa decimal digits and convert it to a bit constant
 * - return NULL_TERM if there's a format error 
 * - the number of bits is four times the length of s
 * - the string is read in big-endian format (the first character defines
 *   the four high-order bits).
 */
EXPORTED term_t yices_parse_bvhex(const char *s) {
  uint32_t n;
  int32_t code;

  n = strlen(s);
  if (n == 0) {
    error.code = INVALID_BVHEX_FORMAT;
    return NULL_TERM;
  }

  if (n > YICES_MAX_BVSIZE/4) {
    error.code = MAX_BVSIZE_EXCEEDED;
    error.badval = ((uint64_t) n) * 4; // badval is 64bits
    return NULL_TERM;
  }

  bvconstant_set_bitsize(&bv0, 4 * n);
  code = bvconst_set_from_hexa_string(bv0.data, n, s);
  if (code < 0) {
    error.code = INVALID_BVHEX_FORMAT;
    return NULL_TERM;    
  }  

  return mk_bv_constant(&manager, &bv0);
}







/***************************
 *  BIT-VECTOR ARITHMETIC  *
 ***************************/

/*
 * Every operation: add/sub/neg/mul/square has two variants
 * - one for bitvectors of small size (1 to 64 bits)
 * - one for bitvectors of more than 64 bits
 */
static term_t mk_bvadd64(term_t t1, term_t t2) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith64_buffer();
  tbl = get_terms();
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_add_term(b, tbl, t2);

  return mk_bvarith64_term(&manager, b);
}

static term_t mk_bvadd(term_t t1, term_t t2) {
  bvarith_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith_buffer();
  tbl = get_terms();
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_add_term(b, tbl, t2);

  return mk_bvarith_term(&manager, b);
}

EXPORTED term_t yices_bvadd(term_t t1, term_t t2) {  
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  if (term_bitsize(get_terms(), t1) <= 64) {
    return mk_bvadd64(t1, t2);
  } else {
    return mk_bvadd(t1, t2);
  }
}


static term_t mk_bvsub64(term_t t1, term_t t2) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith64_buffer();
  tbl = get_terms();
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_sub_term(b, tbl, t2);

  return mk_bvarith64_term(&manager, b);
}

static term_t mk_bvsub(term_t t1, term_t t2) {
  bvarith_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith_buffer();
  tbl = get_terms();
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_sub_term(b, tbl, t2);

  return mk_bvarith_term(&manager, b);
}

EXPORTED term_t yices_bvsub(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  if (term_bitsize(get_terms(), t1) <= 64) {
    return mk_bvsub64(t1, t2);
  } else {
    return mk_bvsub(t1, t2);
  }
}


static term_t mk_bvneg64(term_t t1) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith64_buffer();
  tbl = get_terms();
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_negate(b);

  return mk_bvarith64_term(&manager, b);
}

static term_t mk_bvneg(term_t t1) {
  bvarith_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith_buffer();
  tbl = get_terms();
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_negate(b);

  return mk_bvarith_term(&manager, b);
}

EXPORTED term_t yices_bvneg(term_t t1) {
  if (! check_good_term(&manager, t1) ||
      ! check_bitvector_term(&manager, t1)) {
    return NULL_TERM;
  }

  if (term_bitsize(get_terms(), t1) <= 64) {
    return mk_bvneg64(t1);
  } else {
    return mk_bvneg(t1);
  }
}


static term_t mk_bvmul64(term_t t1, term_t t2) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith64_buffer();
  tbl = get_terms();
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_mul_term(b, tbl, t2);

  return mk_bvarith64_term(&manager, b);
}

static term_t mk_bvmul(term_t t1, term_t t2) {
  bvarith_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith_buffer();
  tbl = get_terms();
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_mul_term(b, tbl, t2);

  return mk_bvarith_term(&manager, b);
}

EXPORTED term_t yices_bvmul(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2) || 
      ! check_product_degree(&manager, t1, t2)) {
    return NULL_TERM;
  }

  if (term_bitsize(get_terms(), t1) <= 64) {
    return mk_bvmul64(t1, t2);
  } else {
    return mk_bvmul(t1, t2);
  }
}


static term_t mk_bvsquare64(term_t t1) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith64_buffer();
  tbl = get_terms();
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_square(b);

  return mk_bvarith64_term(&manager, b);
}

static term_t mk_bvsquare(term_t t1) {
  bvarith_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith_buffer();
  tbl = get_terms();
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_square(b);

  return mk_bvarith_term(&manager, b);
}

EXPORTED term_t yices_bvsquare(term_t t1) {
  if (! check_good_term(&manager, t1) ||
      ! check_bitvector_term(&manager, t1) || 
      ! check_square_degree(&manager, t1)) {
    return NULL_TERM;
  }

  if (term_bitsize(get_terms(), t1) <= 64) {
    return mk_bvsquare64(t1);
  } else {
    return mk_bvsquare(t1);
  }
}




static term_t mk_bvpower64(term_t t1, uint32_t d) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;
  uint32_t n;

  b = get_bvarith64_buffer();
  tbl = get_terms();
  n = term_bitsize(tbl, t1);
  bvarith64_buffer_prepare(b, n);
  bvarith64_buffer_set_one(b);
  bvarith64_buffer_mul_term_power(b, tbl, t1, d);

  return mk_bvarith64_term(&manager, b);
}

static term_t mk_bvpower(term_t t1, uint32_t d) {
  bvarith_buffer_t *b;
  term_table_t *tbl;
  uint32_t n;

  b = get_bvarith_buffer();
  tbl = get_terms();
  n = term_bitsize(tbl, t1);
  bvarith_buffer_prepare(b, n);
  bvarith_buffer_set_one(b);
  bvarith_buffer_mul_term_power(b, tbl, t1, d);

  return mk_bvarith_term(&manager, b);
}

EXPORTED term_t yices_bvpower(term_t t1, uint32_t d) {
  if (! check_good_term(&manager, t1) ||
      ! check_bitvector_term(&manager, t1) || 
      ! check_power_degree(&manager, t1, d)) {
    return NULL_TERM;
  }

  if (term_bitsize(get_terms(), t1) <= 64) {
    return mk_bvpower64(t1, d);
  } else {
    return mk_bvpower(t1, d);
  }
}



/***********************************
 *  BITWISE BIT-VECTOR OPERATIONS  *
 **********************************/

EXPORTED term_t yices_bvnot(term_t t1) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_good_term(&manager, t1) ||
      ! check_bitvector_term(&manager, t1)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = get_terms();
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_not(b);

  return mk_bvlogic_term(&manager, b);
}


EXPORTED term_t yices_bvand(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = get_terms();
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_and_term(b, tbl, t2);

  return mk_bvlogic_term(&manager, b);
}

EXPORTED term_t yices_bvor(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = get_terms();
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_or_term(b, tbl, t2);

  return mk_bvlogic_term(&manager, b);
}

EXPORTED term_t yices_bvxor(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;
  
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = get_terms();
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_xor_term(b, tbl, t2);

  return mk_bvlogic_term(&manager, b);
}


EXPORTED term_t yices_bvnand(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = get_terms();
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_and_term(b, tbl, t2);
  bvlogic_buffer_not(b);

  return mk_bvlogic_term(&manager, b);
}

EXPORTED term_t yices_bvnor(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = get_terms();
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_or_term(b, tbl, t2);
  bvlogic_buffer_not(b);

  return mk_bvlogic_term(&manager, b);
}

EXPORTED term_t yices_bvxnor(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = get_terms();
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_xor_term(b, tbl, t2);
  bvlogic_buffer_not(b);

  return mk_bvlogic_term(&manager, b);
}




/*********************************************
 *   BITVECTOR SHIFT/ROTATION BY A CONSTANT  *
 ********************************************/

/*
 * Shift or rotation by an integer constant n
 * - shift_left0 sets the low-order bits to zero
 * - shift_left1 sets the low-order bits to one
 * - shift_rigth0 sets the high-order bits to zero
 * - shift_right1 sets the high-order bits to one
 * - ashift_right is arithmetic shift, it copies the sign bit &
 * - rotate_left: circular rotation
 * - rotate_right: circular rotation 
 *
 * If t is a vector of m bits, then n must satisfy 0 <= n <= m.
 *
 * The functions return NULL_TERM (-1) if there's an error.
 *
 * Error reports:
 * if t is not valid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 * if n > size of t
 *   code = INVALID_BITSHIFT
 *   badval = n
 */
EXPORTED term_t yices_shift_left0(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = get_terms();

  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t) || 
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }
  
  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_shift_left0(b, n);

  return mk_bvlogic_term(&manager, b);
}

EXPORTED term_t yices_shift_left1(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = get_terms();

  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t) || 
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }
  
  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_shift_left1(b, n);

  return mk_bvlogic_term(&manager, b);
}

EXPORTED term_t yices_shift_right0(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = get_terms();

  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t) || 
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }
  
  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_shift_right0(b, n);

  return mk_bvlogic_term(&manager, b);
}

EXPORTED term_t yices_shift_right1(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = get_terms();

  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t) || 
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }
  
  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_shift_right1(b, n);

  return mk_bvlogic_term(&manager, b);
}

EXPORTED term_t yices_ashift_right(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = get_terms();

  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t) || 
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }
  
  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_ashift_right(b, n);

  return mk_bvlogic_term(&manager, b);
}

EXPORTED term_t yices_rotate_left(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = get_terms();

  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t) || 
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }
  
  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  if (n < b->bitsize) {
    bvlogic_buffer_rotate_left(b, n);
  }

  return mk_bvlogic_term(&manager, b);
}

EXPORTED term_t yices_rotate_right(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = get_terms();

  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t) || 
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }
  
  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  if (n < b->bitsize) {
    bvlogic_buffer_rotate_right(b, n);
  }

  return mk_bvlogic_term(&manager, b);
}



/****************************************
 *  BITVECTOR EXTRACTION/CONCATENATION  *
 ***************************************/

/*
 * Extract a subvector of t
 * - t must be a bitvector term of size m
 * - i and j must satisfy 0 <= i <= j <= m-1
 * The result is the bits i to j of t.
 *
 * Return NULL_TERM (-1) if there's an error.
 *
 * Error reports:
 * if t is not valid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 * if 0 <= i <= j <= m-1 does not hold
 *   code = INVALID_BVEXTRACT
 */
EXPORTED term_t yices_bvextract(term_t t, uint32_t i, uint32_t j) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;
  uint32_t n;

  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t)) {
    return NULL_TERM;
  }

  tbl = get_terms();
  n = term_bitsize(tbl, t);
  if (! check_bitextract(i, j, n)) {
    return NULL_TERM;
  }

  if (i == 0 && j == n-1) {
    return t;
  } else {
    b = get_bvlogic_buffer();
    bvlogic_buffer_set_slice_term(b, tbl, i, j, t);
    return mk_bvlogic_term(&manager, b);
  }
}


/*
 * Concatenation
 * - t1 and t2 must be bitvector terms
 *
 * Return NULL_TERM (-1) if there's an error.
 *
 * Error reports
 * if t1 or t2 is not a valid term
 *   code = INVALID_TERM
 *   term1 = t1 or t2
 * if t1 or t2 is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t1 or t2
 * if the size of the result would be larger than MAX_BVSIZE
 *   code = MAX_BVSIZE_EXCEEDED
 *   badval = n1 + n2 (n1 = size of t1, n2 = size of t2)
 */
EXPORTED term_t yices_bvconcat(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = get_terms();

  if (! check_good_term(&manager, t1) ||
      ! check_good_term(&manager, t2) ||
      ! check_bitvector_term(&manager, t1) ||
      ! check_bitvector_term(&manager, t2) || 
      ! check_maxbvsize(term_bitsize(tbl, t1) + term_bitsize(tbl, t2))) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t2);
  bvlogic_buffer_concat_left_term(b, tbl, t1);

  return mk_bvlogic_term(&manager, b);
}


/*
 * Repeated concatenation:
 * - make n copies of t and concatenate them
 * - n must be positive
 *
 * Return NULL_TERM (-1) if there's an error
 *
 * Error report:
 * if t is not valid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 * if n <= 0
 *   code = POSINT_REQUIRED
 *   badval = n
 * if size of the result would be more than MAX_BVSIZE
 *   code = MAX_BVSIZE_EXCEEDED
 *   badval = n * bitsize of t
 */
EXPORTED term_t yices_bvrepeat(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;
  uint64_t m;

  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t) ||
      ! check_positive(n)) {
    return NULL_TERM;
  }

  // check size
  tbl = get_terms();
  m = ((uint64_t) n) * term_bitsize(tbl, t);
  if (m > (uint64_t) YICES_MAX_BVSIZE) {
    error.code = MAX_BVSIZE_EXCEEDED;
    error.badval = m;
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_repeat_concat(b, n);

  return mk_bvlogic_term(&manager, b);
}


/*
 * Sign extension
 * - add n copies of t's sign bit
 * - n must be non-negative
 *
 * Return NULL_TERM if there's an error.
 *
 * Error reports:
 * if t is invalid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not a bitvector
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 * if n + bitsize of t is too large:
 *   code = MAX_BVSIZE_EXCEEDED
 *   badval = n + bitsize of t
 */
EXPORTED term_t yices_sign_extend(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;
  uint64_t m;

  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t)) {
    return NULL_TERM;
  }


  // check size
  tbl = get_terms();
  m = ((uint64_t) n) + term_bitsize(tbl, t);
  if (m > (uint64_t) YICES_MAX_BVSIZE) {
    error.code = MAX_BVSIZE_EXCEEDED;
    error.badval = m;
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_sign_extend(b, b->bitsize + n);

  return mk_bvlogic_term(&manager, b);
}


/*
 * Zero extension
 * - add n zeros to t
 * - n must be non-negative
 *
 * Return NULL_TERM if there's an error.
 *
 * Error reports:
 * if t is invalid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not a bitvector
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 * if n + bitsize of t is too large:
 *   code = MAX_BVSIZE_EXCEEDED
 *   badval = n + bitsize of t
 */
EXPORTED term_t yices_zero_extend(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;
  uint64_t m;

  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t)) {
    return NULL_TERM;
  }

  // check size
  tbl = get_terms();
  m = ((uint64_t) n) + term_bitsize(tbl, t);
  if (m > (uint64_t) YICES_MAX_BVSIZE) {
    error.code = MAX_BVSIZE_EXCEEDED;
    error.badval = m;
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_zero_extend(b, b->bitsize + n);

  return mk_bvlogic_term(&manager, b);
}



/*
 * AND-reduction: 
 * if t is b[m-1] ... b[0], then the result is a bit-vector of 1 bit
 * equal to the conjunction of all bits of t (i.e., (and b[0] ... b[m-1])
 *
 * OR-reduction: compute (or b[0] ... b[m-1])
 *
 * Return NULL_TERM if there's an error
 *
 * Error reports:
 * if t is invalid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not a bitvector
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 */
EXPORTED term_t yices_redand(term_t t) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = get_terms();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_redand(b);

  return mk_bvlogic_term(&manager, b);
}

EXPORTED term_t yices_redor(term_t t) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = get_terms();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_redor(b);

  return mk_bvlogic_term(&manager, b);
}


/*
 * Bitwise equality comparison: if t1 and t2 are bitvectors of size n,
 * construct (bvand (bvxnor t1 t2))
 *
 * Return NULL_TERM if there's an error
 *
 * Error reports:
 * if t1 or t2 is not valid
 *   code = INVALID_TERM
 *   term1 = t1 or t2
 *   index = -1
 * if t1 or t2 is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t1 or t2
 * if t1 and t2 do not have the same bitvector type
 *   code = INCOMPATIBLE_TYPES
 *   term1 = t1
 *   type1 = type of t1
 *   term2 = t2
 *   type2 = type of t2
 */
EXPORTED term_t yices_redcomp(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = get_terms();
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_comp_term(b, tbl, t2);

  return mk_bvlogic_term(&manager, b);
}




/*******************************
 *  GENERIC BIT-VECTOR SHIFTS  *
 *****************************/


EXPORTED term_t yices_bvshl(term_t t1, term_t t2) {  
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  return mk_bvshl(&manager, t1, t2);
}



EXPORTED term_t yices_bvlshr(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  return mk_bvlshr(&manager, t1, t2);
}



EXPORTED term_t yices_bvashr(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }

  return mk_bvashr(&manager, t1, t2);
}





/**********************************
 *  BITVECTOR DIVISION OPERATORS  *
 *********************************/

EXPORTED term_t yices_bvdiv(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvdiv(&manager, t1, t2);
}


EXPORTED term_t yices_bvrem(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvrem(&manager, t1, t2);
}


EXPORTED term_t yices_bvsdiv(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsdiv(&manager, t1, t2);
}


EXPORTED term_t yices_bvsrem(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsrem(&manager, t1, t2);
}


EXPORTED term_t yices_bvsmod(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsmod(&manager, t1, t2);
}



/*
 * Convert an array of boolean terms arg[0 ... n-1] into
 * a bitvector term.
 *
 * Error report:
 * if n == 0
 *    code = POSINT_REQUIRED
 *    badval = n
 * if n > YICES_MAX_BVSIZE
 *    code = MAX_BVSIZE_EXCEEDED
 *    badval = size
 * if arg[i] is invalid
 *    code = INVALID_TERM
 *    term1 = arg[i]
 *    index = i
 * if arg[i] is not a boolean
 *    code = TYPE_MISMATCH
 *    term1 = arg[i]
 *    type1 = bool
 *    index = i
 */
EXPORTED term_t yices_bvarray(uint32_t n, term_t arg[]) {
  if (! check_positive(n) ||
      ! check_maxbvsize(n) ||
      ! check_good_terms(&manager, n, arg) ||
      ! check_boolean_args(&manager, n, arg)) {
    return NULL_TERM;
  }
  return mk_bvarray(&manager, n, arg);
}



/*
 * Extract bit i of vector v (as a boolean)
 *
 * Error report:
 * if v is invalid
 *    code = INVALID_TERM
 *    term1 = v
 *    index = -1
 * if v is not a bitvector term
 *    code = BITVECTOR_REQUIRES
 *    term1 = t
 * if i >= v's bitsize
 *    code = INVALID_BVEXTRACT
 */
EXPORTED term_t yices_bitextract(term_t t, uint32_t i) {
  if (! check_good_term(&manager, t) ||
      ! check_bitvector_term(&manager, t) ||
      ! check_bitextract(i, i, term_bitsize(get_terms(), t))) {
    return NULL_TERM;
  }
  return mk_bitextract(&manager, t, i);
}




/*********************
 *  BITVECTOR ATOMS  *
 ********************/

EXPORTED term_t yices_bveq_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bveq(&manager, t1, t2);
}


EXPORTED term_t yices_bvneq_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvneq(&manager, t1, t2);
}


EXPORTED term_t yices_bvge_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvge(&manager, t1, t2);
}


EXPORTED term_t yices_bvgt_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvgt(&manager, t1, t2);
}


EXPORTED term_t yices_bvle_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvle(&manager, t1, t2);
}


EXPORTED term_t yices_bvlt_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvlt(&manager, t1, t2);
}


EXPORTED term_t yices_bvsge_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsge(&manager, t1, t2);
}

EXPORTED term_t yices_bvsgt_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsgt(&manager, t1, t2);
}


EXPORTED term_t yices_bvsle_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsle(&manager, t1, t2);
}


EXPORTED term_t yices_bvslt_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(&manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvslt(&manager, t1, t2);
}






/**************************
 *  SOME CHECKS ON TERMS  *
 *************************/

/*
 * Get the type of term t
 * return NULL_TYPE if t is not a valid term
 * and set the error report:
 *   code = INVALID_TERM
 *   term1 = t
 *   index = -1
 */
EXPORTED type_t yices_type_of_term(term_t t) {
  if (! check_good_term(&manager, t)) {
    return NULL_TYPE;
  }
  return term_type(get_terms(), t);
}


/*
 * Check the type of a term t:
 * - term_is_arithmetic check whether t's type is either int or real
 * - term_is_real check whether t's type is real (return false if t's type is int)
 * - term_is_int check whether t's type is int 
 * If t is not a valid term, the check functions return false
 * and set the error report as above.
 */
EXPORTED int32_t yices_term_is_bool(term_t t) {
  return check_good_term(&manager, t) && is_boolean_term(get_terms(), t);
}

EXPORTED int32_t yices_term_is_int(term_t t) {
  return check_good_term(&manager, t) && is_integer_term(get_terms(), t);
}

EXPORTED int32_t yices_term_is_real(term_t t) {
  return check_good_term(&manager, t) && is_real_term(get_terms(), t);
}

EXPORTED int32_t yices_term_is_arithmetic(term_t t) {
  return check_good_term(&manager, t) && is_arithmetic_term(get_terms(), t);
}

EXPORTED int32_t yices_term_is_bitvector(term_t t) {
  return check_good_term(&manager, t) && is_bitvector_term(get_terms(), t);
}

EXPORTED int32_t yices_term_is_tuple(term_t t) {
  return check_good_term(&manager, t) && is_tuple_term(get_terms(), t);
}

EXPORTED int32_t yices_term_is_function(term_t t) {
  return check_good_term(&manager, t) && is_function_term(get_terms(), t);
}

EXPORTED int32_t yices_term_is_scalar(term_t t) {
  term_table_t *tbl;

  tbl = get_terms();
  return check_good_term(&manager, t) && (is_scalar_term(tbl, t) || is_utype_term(tbl, t));
}


/*
 * Size of bitvector term t. 
 * return 0 if t is not a bitvector
 */
EXPORTED uint32_t yices_term_bitsize(term_t t) {
  if (! check_bitvector_term(&manager, t)) {
    return 0;
  }
  return term_bitsize(get_terms(), t);
}




/***********************************
 *  EXTENSIONS: TERM CONSTRUCTORS  *
 **********************************/

/*
 * These term constructors are used in term_stack
 */
term_t arith_buffer_get_term(arith_buffer_t *b) {
  return mk_arith_term(&manager, b);
}

term_t arith_buffer_get_eq0_atom(arith_buffer_t *b) {
  return mk_arith_eq0(&manager, b);
}

term_t arith_buffer_get_geq0_atom(arith_buffer_t *b) {
  return mk_arith_geq0(&manager, b);
}

term_t arith_buffer_get_leq0_atom(arith_buffer_t *b) {
  return mk_arith_leq0(&manager, b);
}

term_t arith_buffer_get_gt0_atom(arith_buffer_t *b) {
  return mk_arith_gt0(&manager, b);
}

term_t arith_buffer_get_lt0_atom(arith_buffer_t *b) {
  return mk_arith_lt0(&manager, b);
}

term_t bvlogic_buffer_get_term(bvlogic_buffer_t *b) {
  return mk_bvlogic_term(&manager, b);
}

term_t bvarith_buffer_get_term(bvarith_buffer_t *b) {
  return mk_bvarith_term(&manager, b);
}

term_t bvarith64_buffer_get_term(bvarith64_buffer_t *b) {
  return mk_bvarith64_term(&manager, b);
}

term_t yices_bvconst_term(uint32_t n, uint32_t *v) {
  assert(64 < n && n <= YICES_MAX_BVSIZE);
  return bvconst_term(get_terms(), n, v);
}

term_t yices_bvconst64_term(uint32_t n, uint64_t c) {
  assert(1 <= n && n <= 64 && c == norm64(c, n));
  return bv64_constant(get_terms(), n, c);
}

term_t yices_rational_term(rational_t *q) {
  return arith_constant(get_terms(), q);
}


/*******************************************
 *  EXTENSIONS: SUPPORT FOR TYPE CHECKING  *
 ******************************************/

/*
 * Check whether t is a valid arithmetic term
 * - if not set the internal error report:
 *
 * If t is not a valid term:
 *   code = INVALID_TERM 
 *   term1 = t
 *   index = -1
 * If t is not an arithmetic term; 
 *   code = ARITHTERM_REQUIRED
 *   term1 = t
 */
bool yices_check_arith_term(term_t t) {
  return check_good_term(&manager, t) && check_arith_term(&manager, t);
}


/*
 * Check for degree overflow in the product (b * t) 
 * - b must be a buffer obtained via yices_new_arith_buffer().
 * - t must be a valid arithmetic term.
 *
 * Return true if there's no overflow.
 *
 * Return false otherwise and set the error report:
 *   code = DEGREE_OVERFLOW
 *   badval = degree of b + degree of t
 */
bool yices_check_mul_term(arith_buffer_t *b, term_t t) {
  term_table_t *tbl;
  uint32_t d1, d2;

  tbl = get_terms();

  assert(good_term(tbl, t) && is_arithmetic_term(tbl, t));

  d1 = arith_buffer_degree(b);
  d2 = term_degree(tbl, t);
  assert(d1 <= YICES_MAX_DEGREE && d2 <= YICES_MAX_DEGREE);

  return check_maxdegree(d1 + d2);
}


/*
 * Same thing for the product of two buffers b1 and b2.
 * - both must be buffers allocated using yices_new_arith_buffer().
 */
bool yices_check_mul_buffer(arith_buffer_t *b1, arith_buffer_t *b2) {
  uint32_t d1, d2;

  d1 = arith_buffer_degree(b1);
  d2 = arith_buffer_degree(b2);
  assert(d1 <= YICES_MAX_DEGREE && d2 <= YICES_MAX_DEGREE);

  return check_maxdegree(d1 + d2);  
}



/*
 * Check whether n <= YICES_MAX_BVSIZE and if not set the error report.
 */
bool yices_check_bvsize(uint32_t n) {
  return check_maxbvsize(n);
}


/*
 * Check whether t is a valid bitvector term
 * - if not set the internal error report:
 *
 * If t is not a valid term:
 *   code = INVALID_TERM 
 *   term1 = t
 *   index = -1
 * If t is not an arithmetic term; 
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 */
bool yices_check_bv_term(term_t t) {
  return check_good_term(&manager, t) && check_bitvector_term(&manager, t);
}


/*
 * Check whether b is non empty
 * Error report:
 *   code = EMPTY_BITVECTOR
 */
bool yices_check_bvlogic_buffer(bvlogic_buffer_t *b) {
  if (bvlogic_buffer_is_empty(b)) {
    error.code = EMPTY_BITVECTOR;
    return false;
  }
  return true;
}


/*
 * Check whether s is a valid shift amount for buffer b:
 * - return true if 0 <= s <= b->bitsize
 * - otherwise set the error report and return false.
 */
bool yices_check_bitshift(bvlogic_buffer_t *b, int32_t s) {
  if (s < 0 || s > bvlogic_buffer_bitsize(b)) {
    error.code = INVALID_BITSHIFT;
    error.badval = s;
    return false;
  }

  return true;
}


/*
 * Check whether [i, j] is a valid segment for a vector of n bits
 * - return true if 0 <= i <= j <= n
 * - otherwise set the error report and return false.
 */
bool yices_check_bvextract(uint32_t n, int32_t i, int32_t j) {
  if (i < 0 || i > j || j >= n) {
    error.code = INVALID_BVEXTRACT;
    return false;
  }

  return true;
}


/*
 * Check whether repeat_concat(b, n) is valid
 * - return true if it is
 * - returm false and set errort report if it's not.
 *
 * Error report:
 * if n <= 0
 *   code = POSINT_REQUIRED
 *   badval = n
 * if size of the result would be more than MAX_BVSIZE
 *   code = MAX_BVSIZE_EXCEEDED
 *   badval = n * bitsize of t
 */
bool yices_check_bvrepeat(bvlogic_buffer_t *b, int32_t n) {
  uint64_t m;

  if (n <= 0) {
    error.code = POS_INT_REQUIRED;
    error.badval = n;
    return false;
  }

  m = ((uint64_t) n) * bvlogic_buffer_bitsize(b);
  if (m > ((uint64_t) YICES_MAX_BVSIZE)) {
    error.code = MAX_BVSIZE_EXCEEDED;
    error.badval = m;
    return false;
  }

  return true;
}



/*
 * Check whether zero_extend(b, n) and sign_extend(b, n) are valid;
 * - n is the number of bits to add
 * - return true if 0 <= n, b->bitsize != 0, and (n + b->bitsize) <= MAX_BVSIZE
 * - return false and set an error report otherwise.
 *
 * Error reports:
 * - if b is empty: EMPTY_BITVECTOR
 * - if n < 0: NONNEG_INT_REQUIRED
 * - if n + b->bitsize > MAX_BVSIZE: MAX_BVSIZE_EXCEEDED
 */
bool yices_check_bvextend(bvlogic_buffer_t *b, int32_t n) {
  uint64_t m;

  if (n < 0) {
    error.code = NONNEG_INT_REQUIRED;
    error.badval = n;
    return false;
  }

  m = bvlogic_buffer_bitsize(b);
  if (m == 0) {
    error.code = EMPTY_BITVECTOR;
    return false;
  }
  
  m += n;
  if (m >= ((uint64_t) YICES_MAX_BVSIZE)) {
    error.code = MAX_BVSIZE_EXCEEDED;
    error.badval = m;
    return false;
  }

  return true;
}


/*
 * Checks for degree overflow in bitvector multiplication:
 * - four variants depending on the type of buffer used
 *   and on whether the argument is a term or a buffer
 *
 * In all cases, the function set the error report and
 * return false if there's an overflow:
 *   code = DEGREE_OVEFLOW
 *   badval = degree of the product
 *
 * All return true if there's no overflow.
 */
bool yices_check_bvmul64_term(bvarith64_buffer_t *b, term_t t) {
  term_table_t *tbl;
  uint32_t d1, d2;

  tbl = get_terms();

  assert(good_term(tbl, t) && is_bitvector_term(tbl, t));

  d1 = bvarith64_buffer_degree(b);
  d2 = term_degree(tbl, t);

  assert(d1 <= YICES_MAX_DEGREE && d2 <= YICES_MAX_DEGREE);

  return check_maxdegree(d1 + d2);
}

bool yices_check_bvmul64_buffer(bvarith64_buffer_t *b1, bvarith64_buffer_t *b2) {
  uint32_t d1, d2;

  d1 = bvarith64_buffer_degree(b1);
  d2 = bvarith64_buffer_degree(b2);

  assert(d1 <= YICES_MAX_DEGREE && d2 <= YICES_MAX_DEGREE);

  return check_maxdegree(d1 + d2);
}

bool yices_check_bvmul_term(bvarith_buffer_t *b, term_t t) {
  term_table_t *tbl;
  uint32_t d1, d2;

  tbl = get_terms();

  assert(good_term(tbl, t) && is_bitvector_term(tbl, t));

  d1 = bvarith_buffer_degree(b);
  d2 = term_degree(tbl, t);

  assert(d1 <= YICES_MAX_DEGREE && d2 <= YICES_MAX_DEGREE);

  return check_maxdegree(d1 + d2);
}

bool yices_check_bvmul_buffer(bvarith_buffer_t *b1, bvarith_buffer_t *b2) {
  uint32_t d1, d2;

  d1 = bvarith_buffer_degree(b1);
  d2 = bvarith_buffer_degree(b2);

  assert(d1 <= YICES_MAX_DEGREE && d2 <= YICES_MAX_DEGREE);

  return check_maxdegree(d1 + d2);
}






/************************
 *  TERM SUBSTITUTION   *
 ***********************/

// TO BE DONE



/**************
 *  PARSING   *
 *************/

/*
 * Parse s as a type expression in the Yices language.
 * Return NULL_TYPE if there's an error.
 */
EXPORTED type_t yices_parse_type(const char *s) {
  parser_t *p;

  p = get_parser(s);
  return parse_yices_type(p, NULL);
}


/*
 * Parse s as a term in the Yices language.
 * Return NULL_TERM if there's an error.
 */
EXPORTED term_t yices_parse_term(const char *s) {
  parser_t *p;

  p = get_parser(s);
  return parse_yices_term(p, NULL);
}



/************
 *  NAMES   *
 ***********/

/*
 * Create mapping (name -> tau) in the type table.
 * If a previous mapping (name -> tau') is in the table, then 
 * it is hidden. 
 *
 * return -1 if tau is invalid and set error report
 * return 0 otherwise.
 */
EXPORTED int32_t yices_set_type_name(type_t tau, const char *name) {
  char *clone;

  if (! check_good_type(&types, tau)) {
    return -1;
  }

  // make a copy of name
  clone = clone_string(name);
  set_type_name(&types, tau, clone);

  return 0;
}


/*
 * Create mapping (name -> t) in the term table.
 * If a previous mapping (name -> t') is in the table, then 
 * it is hidden. 
 *
 * return -1 if  is invalid and set error report
 * return 0 otherwise.
 */
EXPORTED int32_t yices_set_term_name(term_t t, const char *name) {
  char *clone;

  if (! check_good_term(&manager, t)) {
    return -1;
  }

  // make a copy of name
  clone = clone_string(name);
  set_term_name(get_terms(), t, clone);

  return 0;
}


/*
 * Get name of type tau
 * - return NULL if tau has no name (or if tau is not a valid type)
 */
EXPORTED const char *yices_get_type_name(type_t tau) {
  if (! check_good_type(&types, tau)) {
    return NULL;
  }
  return type_name(&types, tau);
}


/*
 * Get name of term t
 * - return NULL is t has no name (or if t is not a valid term)
 */
EXPORTED const char *yices_get_term_name(term_t t) {
  if (! check_good_term(&manager, t)) {
    return NULL;
  }
  return term_name(get_terms(), t);
}



/*
 * Remove name from the type table.
 */
EXPORTED void yices_remove_type_name(const char *name) {
  remove_type_name(&types, name);
}


/*
 * Remove name from the term table.
 */
EXPORTED void yices_remove_term_name(const char *name) {
  remove_term_name(get_terms(), name);
}


/*
 * Get type of the given name or return NULL_TYPE (-1)
 */
EXPORTED type_t yices_get_type_by_name(const char *name) {
  return get_type_by_name(&types, name);
}


/*
 * Get term of the given name or return NULL_TERM
 */
EXPORTED term_t yices_get_term_by_name(const char *name) {
  return get_term_by_name(get_terms(), name);
}


/*
 * Remove the name of type tau (if any)
 * Return -1 if tau is not a valid type and set the error code.
 * Return 0 otherwise.
 */
EXPORTED int32_t yices_clear_type_name(type_t tau) {
  if (! check_good_type(&types, tau)) {
    return -1;
  }

  clear_type_name(&types, tau);
  return 0;
}


/*
 * Remove the name of term t (if any)
 *
 * Return -1 if t is not a valid term (and set the error code)
 * Return 0 otherwise.
 */
EXPORTED int32_t yices_clear_term_name(term_t t) {
  if (! check_good_term(&manager, t)) {
    return -1;
  }

  clear_term_name(get_terms(), t);
  return 0;
}



/****************************
 *  CONTEXT CONFIGURATIONS  *
 ***************************/

/*
 * Allocate a new configuration descriptor
 * - initialize it do defaults
 */
EXPORTED ctx_config_t *yices_new_config(void) {
  ctx_config_t *tmp;

  tmp = alloc_config_structure();
  init_config_to_defaults(tmp);

  return tmp;
}


/*
 * Delete
 */
EXPORTED void yices_free_config(ctx_config_t *config) {
  free_config_structure(config);
}


/*
 * Set a configuration parameter
 */
EXPORTED int32_t yices_set_config(ctx_config_t *config, const char *name, const char *value) {
  int32_t k;

  k = config_set_field(config, name, value);
  if (k < 0) {
    if (k == -1) {
      // invalid name
      error.code = CTX_UNKNOWN_PARAMETER;
    } else {
      error.code = CTX_INVALID_PARAMETER_VALUE;
    }
    return -1;
  }

  return 0;
}


/*
 * Set config to a default solver combination for the given logic
 * - return -1 if there's an error
 * - return 0 otherwise
 */
EXPORTED int32_t yices_default_config_for_logic(ctx_config_t *config, const char *logic) {
  int32_t k;

  k = config_set_logic(config, logic);
  if (k < 0) {
    if (k == -1) {
      error.code = CTX_UNKNOWN_LOGIC;
    } else {
      error.code = CTX_LOGIC_NOT_SUPPORTED;
    }
    return -1;
  }

  return 0;
}



/*******************************************
 *  SIMPLIFICATION/PREPROCESSING OPTIONS   *
 ******************************************/

/*
 * Parameters are identified by an integer in the following range
 */
typedef enum ctx_option {
  CTX_OPTION_VAR_ELIM,
  CTX_OPTION_ARITH_ELIM,
  CTX_OPTION_BVARITH_ELIM,
  CTX_OPTION_FLATTEN,
  CTX_OPTION_LEARN_EQ,
  CTX_OPTION_KEEP_ITE,
  CTX_OPTION_EAGER_ARITH_LEMMAS,
} ctx_option_t;

#define NUM_CTX_OPTIONS (CTX_OPTION_EAGER_ARITH_LEMMAS+1)


/*
 * Option names in lexicographic order
 */
static const char * const ctx_option_names[NUM_CTX_OPTIONS] = {
  "arith-elim",
  "bvarith-elim",
  "eager-arith-lemmas",
  "flatten",
  "keep-ite",
  "learn-eq",
  "var-elim",
};


/*
 * Corresponding index (cf. string_utils.h for parse_as_keyword)
 */
static const int32_t ctx_option_key[NUM_CTX_OPTIONS] = {
  CTX_OPTION_ARITH_ELIM,
  CTX_OPTION_BVARITH_ELIM,
  CTX_OPTION_EAGER_ARITH_LEMMAS,
  CTX_OPTION_FLATTEN,
  CTX_OPTION_KEEP_ITE,
  CTX_OPTION_LEARN_EQ,
  CTX_OPTION_VAR_ELIM,
};


/*
 * Enable a specific option
 */
EXPORTED int32_t yices_context_enable_option(context_t *ctx, const char *option) {
  int32_t k, r;

  r = 0; // default return code: no error
  k = parse_as_keyword(option, ctx_option_names, ctx_option_key, NUM_CTX_OPTIONS);
  switch (k) {
  case CTX_OPTION_VAR_ELIM:
    enable_variable_elimination(ctx);
    break;

  case CTX_OPTION_ARITH_ELIM:
    enable_arith_elimination(ctx);
    break;

  case CTX_OPTION_BVARITH_ELIM:
    enable_bvarith_elimination(ctx);
    break;

  case CTX_OPTION_FLATTEN:
    enable_diseq_and_or_flattening(ctx);
    break;

  case CTX_OPTION_LEARN_EQ:
    enable_eq_abstraction(ctx);
    break;

  case CTX_OPTION_KEEP_ITE:
    enable_keep_ite(ctx);
    break;

  case CTX_OPTION_EAGER_ARITH_LEMMAS:
    enable_splx_eager_lemmas(ctx);
    break;

  default:
    assert(k == -1);
    // not recognized
    error.code = CTX_UNKNOWN_PARAMETER;
    r = -1;
    break;
  }

  return r;
}


/*
 * Disable a specific option
 */
EXPORTED int32_t yices_context_disable_option(context_t *ctx, const char *option) {
  int32_t k, r;

  r = 0; // default return code: no error
  k = parse_as_keyword(option, ctx_option_names, ctx_option_key, NUM_CTX_OPTIONS);
  switch (k) {
  case CTX_OPTION_VAR_ELIM:
    disable_variable_elimination(ctx);
    break;

  case CTX_OPTION_ARITH_ELIM:
    disable_arith_elimination(ctx);
    break;

  case CTX_OPTION_BVARITH_ELIM:
    enable_bvarith_elimination(ctx);
    break;

  case CTX_OPTION_FLATTEN:
    disable_diseq_and_or_flattening(ctx);
    break;

  case CTX_OPTION_LEARN_EQ:
    disable_eq_abstraction(ctx);
    break;

  case CTX_OPTION_KEEP_ITE:
    disable_keep_ite(ctx);
    break;

  case CTX_OPTION_EAGER_ARITH_LEMMAS:
    enable_splx_eager_lemmas(ctx);
    break;

  default:
    assert(k == -1);
    // not recognized
    error.code = CTX_UNKNOWN_PARAMETER;
    r = -1;
    break;
  }

  return r;
}


/*************************************
 *  SEARCH PARAMETER CONFIGURATIONS  *
 ************************************/

/*
 * Allocate a new configuration descriptor
 * - initialize it do defaults
 */
EXPORTED param_t *yices_new_param_record(void) {
  param_t *tmp;

  tmp = alloc_param_structure();
  init_params_to_defaults(tmp);
  return tmp;
}

/*
 * Delete
 */
EXPORTED void yices_free_param_record(param_t *param) {
  free_param_structure(param);
}

/*
 * Set a search parameter
 */
EXPORTED int32_t yices_set_param(param_t *param, const char *name, const char *value) {
  int32_t k;

  k = params_set_field(param, name, value);
  if (k < 0) {
    if (k == -1) {
      error.code = CTX_UNKNOWN_PARAMETER;
    } else {
      error.code = CTX_INVALID_PARAMETER_VALUE;
    }
    return -1;
  }

  return 0;
}



/*************************
 *  CONTEXT OPERATIONS   *
 ************************/

/*
 * Allocate and initalize a new context.
 * The configuration is specified by arch/mode/iflag/qflag.
 * - arch = architecture to use
 * - mode = which optional features are supported
 * - iflag = true to active the integer solver
 * - qflag = true to support quantifiers
 */
context_t *yices_create_context(context_arch_t arch, context_mode_t mode, bool iflag, bool qflag) {
  context_t *ctx;

  ctx = alloc_context();
  init_context(ctx, get_terms(), mode, arch, qflag);

  enable_variable_elimination(ctx);
  enable_eq_abstraction(ctx);
  enable_diseq_and_or_flattening(ctx);
  enable_arith_elimination(ctx);
  enable_bvarith_elimination(ctx);
  if (iflag) {
    enable_splx_periodic_icheck(ctx);
  }  

  return ctx;
}


/*
 * Allocate and initialize and new context
 * - the configuration is defined by config.
 * - if config is NULL, the default is used.
 * - otherwise, if the configuration is not supported, the function returns NULL.
 */
EXPORTED context_t *yices_new_context(const ctx_config_t *config) {
  context_arch_t arch;
  context_mode_t mode;
  bool iflag;
  bool qflag;
  int32_t k;

  if (config == NULL) {
    // Default configuration: all solvers, mode = push/pop
    arch = CTX_ARCH_EGFUNSPLXBV;
    mode = CTX_MODE_PUSHPOP;
    iflag = true;
    qflag = false;
  } else {
    // read the config
    k = decode_config(config, &arch, &mode, &iflag, &qflag);
    if (k < 0) {
      // invalid configuration
      error.code = CTX_INVALID_CONFIG;
      return NULL;
    }
  }

  return yices_create_context(arch, mode, iflag, qflag);
}


/*
 * Delete ctx
 */
EXPORTED void yices_free_context(context_t *ctx) {
  delete_context(ctx);
  free_context(ctx);
}




/*
 * Get status: return the context's status flag
 * - return one of the codes defined in yices_types.h
 */
EXPORTED smt_status_t yices_context_status(context_t *ctx) {
  return context_status(ctx);
}


/*
 * Reset: remove all assertions and restore ctx's status to IDLE
 */
EXPORTED void yices_reset_context(context_t *ctx) {
  reset_context(ctx);
}


/*
 * Push: mark a backtrack point
 * - return 0 if this operation is supported by the context
 *         -1 otherwise
 *
 * Error report:
 * - if the context is not configured to support push/pop
 *   code = CTX_OPERATION_NOT_SUPPORTED
 * - if the context status is UNSAT or SEARCHING or INTERRUPTED
 *   code = CTX_INVALID_OPERATION
 */
EXPORTED int32_t yices_push(context_t *ctx) {
  if (! context_supports_pushpop(ctx)) {
    error.code = CTX_OPERATION_NOT_SUPPORTED;
    return -1;
  }

  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    context_clear(ctx);
    assert(context_status(ctx) == STATUS_IDLE);
    // fall-through intended
  case STATUS_IDLE:
    break;

  case STATUS_UNSAT:
  case STATUS_INTERRUPTED:
  case STATUS_SEARCHING:
    error.code = CTX_INVALID_OPERATION;
    return -1;

  case STATUS_ERROR:
  default:
    error.code = INTERNAL_EXCEPTION;
    return -1;
  }

  context_push(ctx);
  return 0;
}



/*
 * Pop: backtrack to the previous backtrack point (i.e., the matching
 * call to yices_push).
 * - return 0 if the operation succeeds, -1 otherwise.
 *
 * Error report:
 * - if the context is not configured to support push/pop
 *   code = CTX_OPERATION_NOT_SUPPORTED
 * - if there's no matching push (i.e., the context stack is empty)
 *   or if the context's status is SEARCHING or INTERRUPTED
 *   code = CTX_INVALID_OPERATION
 */
EXPORTED int32_t yices_pop(context_t *ctx) {
  if (! context_supports_pushpop(ctx)) {
    error.code = CTX_OPERATION_NOT_SUPPORTED;
    return -1;
  }

  if (context_base_level(ctx) == 0) {
    error.code = CTX_INVALID_OPERATION;
    return -1;
  }

  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
  case STATUS_INTERRUPTED: // TODO: check this?
    context_clear(ctx);
    assert(context_status(ctx) == STATUS_IDLE);
    // fall-through intended
  case STATUS_IDLE:
    break;

  case STATUS_UNSAT:
    context_clear_unsat(ctx);
    break;

  case STATUS_SEARCHING:
    error.code = CTX_INVALID_OPERATION;
    return -1;

  case STATUS_ERROR:
  default:
    error.code = INTERNAL_EXCEPTION;
    return -1;
  }

  context_pop(ctx);
  return 0;
}



/*
 * Convert an error code reported by assert_formula
 * into the corresponding yces_error value.
 */
static const error_code_t intern_code2error[NUM_INTERNALIZATION_ERRORS] = {
  NO_ERROR,                  // CTX_NO_ERROR
  INTERNAL_EXCEPTION,        // INTERNAL_ERROR 
  INTERNAL_EXCEPTION,        // TYPE_ERROR. Should not happen if the assertions are type correct
  CTX_FREE_VAR_IN_FORMULA,
  CTX_LOGIC_NOT_SUPPORTED,
  CTX_UF_NOT_SUPPORTED,
  CTX_ARITH_NOT_SUPPORTED,
  CTX_BV_NOT_SUPPORTED,
  CTX_ARRAYS_NOT_SUPPORTED,
  CTX_QUANTIFIERS_NOT_SUPPORTED,
  CTX_FORMULA_NOT_IDL,
  CTX_FORMULA_NOT_RDL,
  CTX_NONLINEAR_ARITH_NOT_SUPPORTED,
  CTX_TOO_MANY_ARITH_VARS,
  CTX_TOO_MANY_ARITH_ATOMS,
  CTX_ARITH_SOLVER_EXCEPTION,
  CTX_BV_SOLVER_EXCEPTION,
};

static inline void convert_internalization_error(int32_t code) {
  assert(-NUM_INTERNALIZATION_ERRORS < code && code < 0);
  error.code = intern_code2error[-code];  
}


/*
 * Assert formula t in ctx
 * - ctx status must be IDLE or UNSAT or SAT or UNKNOWN
 * - t must be a boolean term
 *
 * If ctx's status is UNSAT, nothing is done.
 * 
 * If cts's status is IDLE, SAT, or UNKNONW, then the formula is
 * simplified and asserted in the context. The context status is
 * changed to UNSAT if the formula is simplified to 'false' or
 * to IDLE if it does not simplify to false.
 * 
 * This returns 0 if there's no error or -1 if there's an error.
 * 
 * Error report:
 * if t is invalid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not boolean
 *   code = TYPE_MISMATCH
 *   term1 = t
 *   type1 = bool (expected type)
 * if ctx's status is not IDLE or UNSAT or SAT or UNKNOWN
 *   code = CTX_INVALID_OPERATION
 * if ctx's status is neither IDLE nor UNSAT, and the context is 
 * not configured for multiple checks
 *   code = CTX_OPERATION_NOT_SUPPORTED
 *
 * Other error codes are defined in yices_types.h to report that t is
 * outside the logic supported by ctx.
 */
EXPORTED int32_t yices_assert_formula(context_t *ctx, term_t t) {
  int32_t code;

  if (! check_good_term(&manager, t) || 
      ! check_boolean_term(&manager, t)) {
    return -1;
  }

  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    if (! context_supports_multichecks(ctx)) {
      error.code = CTX_OPERATION_NOT_SUPPORTED;
      return -1;
    }
    context_clear(ctx);
    assert(context_status(ctx) == STATUS_IDLE);
    // fall-through intended
  case STATUS_IDLE:
    code = assert_formula(ctx, t);
    if (code < 0) {
      // error during internalization
      convert_internalization_error(code);
      return -1;
    }
    assert(code == TRIVIALLY_UNSAT || code == CTX_NO_ERROR);
  case STATUS_UNSAT:
    // nothing to do
    break;

    
  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
    error.code = CTX_INVALID_OPERATION;
    return -1;

  case STATUS_ERROR:
  default:
    error.code = INTERNAL_EXCEPTION;
    return -1;
  }

  return 0;
}



/*
 * Same thing for an array of n formulas t[0 ... n-1]
 */
EXPORTED int32_t yices_assert_formulas(context_t *ctx, uint32_t n, term_t t[]) {
  int32_t code;

  if (! check_good_terms(&manager, n, t) ||
      ! check_boolean_args(&manager, n, t)) {
    return -1;
  }

  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    if (! context_supports_multichecks(ctx)) {
      error.code = CTX_OPERATION_NOT_SUPPORTED;
      return -1;
    }
    context_clear(ctx);
    assert(context_status(ctx) == STATUS_IDLE);
    // fall-through intended
  case STATUS_IDLE:
    code = assert_formulas(ctx, n, t);
    if (code < 0) {
      // error during internalization
      convert_internalization_error(code);
      return -1;
    }
    assert(code == TRIVIALLY_UNSAT || code == CTX_NO_ERROR);

  case STATUS_UNSAT:
    // fall-through intended
    // nothing to do
    break;

    
  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
    error.code = CTX_INVALID_OPERATION;
    return -1;

  case STATUS_ERROR:
  default:
    error.code = INTERNAL_EXCEPTION;
    return -1;
  }

  return 0;
}



/*
 * Add a blocking clause: this is intended to support all-sat and variants.
 * - if ctx's status is SAT or UNKNOWN, then a new clause is added to ctx
 *   to remove the current truth assignment from the search space.
 *   The status is then updated to IDLE (if the new clause is not empty) or 
 *   to UNSAT (if the new clause is the empty clause).
 *
 * Return code: 0 if there's no error, -1 if there's an error.
 *
 * Error report:
 * if ctx's status is different from SAT or UNKNOWN
 *    code = CTX_INVALID_OPERATION
 * if ctx is not configured to support multiple checks
 *    code = CTX_OPERATION_NOT_SUPPORTED
 */
EXPORTED int32_t yices_assert_blocking_clause(context_t *ctx) {
  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    if (context_supports_multichecks(ctx)) {
      assert_blocking_clause(ctx);
      return 0;
    } else {
      error.code = CTX_OPERATION_NOT_SUPPORTED;
      return -1;
    }

  case STATUS_IDLE:
  case STATUS_UNSAT:
  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
    error.code = CTX_INVALID_OPERATION;
    return -1;

  case STATUS_ERROR:
  default:
    error.code = INTERNAL_EXCEPTION;
    return -1;
  }
}


/*
 * Check satisfiability: check whether the assertions stored in ctx
 * are satisfiable.  
 * - params is an optional structure that stores heurisitic parameters.
 * - if params is NULL, default parameter settings are used.
 *
 * It's better to keep params=NULL unless you encounter performance
 * problems.  Then you may want to play with the heuristics to see if
 * performance improves.
 *
 * The behavior and returned value depend on ctx's current status:
 *
 * 1) If ctx's status is SAT, UNSAT, or UNKNOWN, the function 
 *    does nothing and just return the status.
 *
 * 2) If ctx's status is IDLE, then the solver searches for a
 *    satisfying assignment. If param != NULL, the search parameters
 *    defined by params are used.
 * 
 *    The function returns one of the following codes:
 *    - SAT: the context is satisfiable
 *    - UNSAT: the context is not satisfiable
 *    - UNKNOWN: satisfiability can't be proved or disproved 
 *    - INTERRUPTED: the search was interrupted
 *
 *    The returned status is also stored as the new ctx's status flag.
 *
 * 3) Otherwise, the function does nothing and returns 'STATUS_ERROR', 
 *    it also sets the yices error report (code = CTX_INVALID_OPERATION).
 */
EXPORTED smt_status_t yices_check_context(context_t *ctx, const param_t *params) {
  smt_status_t stat;

  stat = context_status(ctx);
  switch (stat) {
  case STATUS_UNKNOWN:
  case STATUS_UNSAT:
  case STATUS_SAT:
    break;

  case STATUS_IDLE:
    stat = check_context(ctx, params, false); // TODO? add verbosity option
    if (stat == STATUS_INTERRUPTED && context_supports_cleaninterrupt(ctx)) {
      context_cleanup(ctx);
    }
    break;

  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
    error.code = CTX_INVALID_OPERATION;
    stat = STATUS_ERROR;
    break;

  case STATUS_ERROR:
  default:
    error.code = INTERNAL_EXCEPTION;
    stat = STATUS_ERROR;
    break;
  }

  return stat;
}


/*
 * Interrupt the search:
 * - this can be called from a signal handler to stop the search,
 *   after a call to yices_check_context to interrupt the solver.
 *
 * If ctx's status is SEARCHING, then the current search is
 * interrupted and ctx's status flag is updated to
 * INTERRUPTED. Otherwise, the function does nothing.
 */
EXPORTED void yices_stop_search(context_t *ctx) {
  if (context_status(ctx) == STATUS_SEARCHING) {
    context_stop_search(ctx);
  }
}


