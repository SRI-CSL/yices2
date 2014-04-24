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
#include <errno.h>

#include "refcount_strings.h"
#include "string_utils.h"
#include "dl_lists.h"
#include "int_array_sort.h"
#include "sparse_arrays.h"

#include "bv64_constants.h"
#include "bvarith_buffer_terms.h"
#include "bvarith64_buffer_terms.h"

#include "types.h"
#include "term_manager.h"
#include "term_substitution.h"
#include "context.h"
#include "models.h"
#include "model_eval.h"
#include "context_config.h"
#include "search_parameters.h"

#include "type_printer.h"
#include "term_printer.h"
#include "model_printer.h"

#include "yices.h"
#include "yices_error.h"
#include "yices_extensions.h"
#include "yices_lock_free.h"
#include "yices_iterators.h"
#include "yices_globals.h"
#include "yices_lexer.h"
#include "yices_locks.h"
#include "yices_parser.h"
#include "yices_pp.h"



#ifdef HAS_TLS
#define YICES_THREAD_LOCAL __thread
#else
#define YICES_THREAD_LOCAL 
#endif


/****************************
 *  GLOBAL DATA STRUCTURES  *
 ***************************/


/*
 * Initial sizes of the type and term tables.
 */
#define INIT_TYPE_SIZE  16
#define INIT_TERM_SIZE  64


/*
 * Global table.
 */
yices_globals_t __yices_globals;

/*
 * Thread Local Errors
 */


YICES_THREAD_LOCAL bool __yices_error_initialized = false;
YICES_THREAD_LOCAL error_report_t  __yices_error; 

void init_yices_error(void){
  if(!__yices_error_initialized){
    __yices_error_initialized = true;
    memset(&__yices_error, 0, sizeof(error_report_t));
  }
}

error_report_t* get_yices_error(){
  init_yices_error();
  return &__yices_error;
}

/*
 * Registry tables for root terms and types (for garbage collection).
 * - the two tables are statically allocated but initialized only
 *   when needed.
 * - we keep pointers to the tables:
 *   Initially, we set root_terms = NULL and root_types = NULL
 *   On the first call to register a term or type, we initialize the
 *   static tables and update root_terms/root_types to point to it
 */
static yices_lock_t root_lock;

static sparse_array_t *root_terms;
static sparse_array_t *root_types;

static sparse_array_t the_root_terms;
static sparse_array_t the_root_types;



/************************************
 *  DYNAMICALLY ALLOCATED OBJECTS   *
 ***********************************/

/*
 * All objects that can be allocated via the API are stored in
 * doubly-linked lists. This is used by the garbage collector to keep
 * track of live terms.  This also makes it possible to delete all
 * global objects when yices_exit is called.
 */

/*
 * Doubly-linked list of bitvector arithmetic buffers
 */
typedef struct {
  dl_list_t header;
  bvarith_buffer_t buffer;
} bvarith_buffer_elem_t;

static dl_list_t bvarith_buffer_list;
static yices_lock_t  bvarith_buffer_lock; 


/*
 * Variant: 64bit buffers
 */
typedef struct {
  dl_list_t header;
  bvarith64_buffer_t buffer;
} bvarith64_buffer_elem_t;

static dl_list_t bvarith64_buffer_list;
static yices_lock_t bvarith64_buffer_lock;

/*
 * Doubly-linked list of bitvector buffers
 */
typedef struct {
  dl_list_t header;
  bvlogic_buffer_t buffer;
} bvlogic_buffer_elem_t;

static dl_list_t bvlogic_buffer_list;
static yices_lock_t bvlogic_buffer_lock;

/*
 * Doubly-linked list of contexts
 */
typedef struct {
  dl_list_t header;
  context_t context;
} context_elem_t;

static dl_list_t context_list;
static yices_lock_t context_lock;

/*
 * Models
 */
typedef struct {
  dl_list_t header;
  model_t model;
} model_elem_t;

static dl_list_t model_list;
static yices_lock_t model_lock;


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
static yices_lock_t generic_lock;




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

  get_yices_lock(&bvarith_buffer_lock);

  list_insert_next(&bvarith_buffer_list, &new_elem->header);

  release_yices_lock(&bvarith_buffer_lock);


  return &new_elem->buffer;
}

/*
 * Remove b from the list and free b
 */
static inline void free_bvarith_buffer(bvarith_buffer_t *b) {
  dl_list_t *elem;

  elem = bvarith_buffer_header(b);

  get_yices_lock(&bvarith_buffer_lock);

  list_remove(elem);

  release_yices_lock(&bvarith_buffer_lock);


  safe_free(elem);
}

/*
 * Clean up the arith buffer list: free all elements and empty the list
 */
static void free_bvarith_buffer_list(void) {
  dl_list_t *elem, *aux;

  get_yices_lock(&bvarith_buffer_lock);

  elem = bvarith_buffer_list.next;
  while (elem != &bvarith_buffer_list) {
    aux = elem->next;
    delete_bvarith_buffer(bvarith_buffer(elem));
    safe_free(elem);
    elem = aux;
  }

  clear_list(&bvarith_buffer_list);

  release_yices_lock(&bvarith_buffer_lock);

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

  get_yices_lock(&bvarith64_buffer_lock);

  list_insert_next(&bvarith64_buffer_list, &new_elem->header);

  release_yices_lock(&bvarith64_buffer_lock);

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

  get_yices_lock(&bvarith64_buffer_lock);

  elem = bvarith64_buffer_list.next;
  while (elem != &bvarith64_buffer_list) {
    aux = elem->next;
    delete_bvarith64_buffer(bvarith64_buffer(elem));
    safe_free(elem);
    elem = aux;
  }

  clear_list(&bvarith64_buffer_list);

  release_yices_lock(&bvarith64_buffer_lock);

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

  get_yices_lock(&bvlogic_buffer_lock);

  list_insert_next(&bvlogic_buffer_list, &new_elem->header);

  release_yices_lock(&bvlogic_buffer_lock);

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

  get_yices_lock(&bvlogic_buffer_lock);

  elem = bvlogic_buffer_list.next;
  while (elem != &bvlogic_buffer_list) {
    aux = elem->next;
    delete_bvlogic_buffer(bvlogic_buffer(elem));
    safe_free(elem);
    elem = aux;
  }

  clear_list(&bvlogic_buffer_list);

  release_yices_lock(&bvlogic_buffer_lock);
  
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
static context_t *alloc_context(void) {
  context_elem_t *new_elem;
  context_t *retval;

  new_elem = (context_elem_t *) safe_malloc(sizeof(context_elem_t));

  get_yices_lock(&context_lock);

  list_insert_next(&context_list, &new_elem->header);

  release_yices_lock(&context_lock);

  retval = &new_elem->context;

  create_yices_lock(&(retval->lock));

  return retval;
}


/*
 * Remove c from the list and free c
 * - WARNING: make sure to call delete_context(c) before this
 *   function
 */
static void free_context(context_t *c) {
  dl_list_t *elem;
  
  destroy_yices_lock(&(c->lock));

  elem = header_of_context(c);

  get_yices_lock(&context_lock);

  list_remove(elem);
  safe_free(elem);

  release_yices_lock(&context_lock); 
 
}


/*
 * Cleanup the context list
 */
static void free_context_list(void) {
  dl_list_t *elem, *aux;

  get_yices_lock(&context_lock);

  elem = context_list.next;
  while (elem != &context_list) {
    aux = elem->next;
    delete_context(context_of_header(elem));
    safe_free(elem);
    elem = aux;
  }

  clear_list(&context_list);

  release_yices_lock(&context_lock);
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
static model_t *alloc_model(void) {
  model_elem_t *new_elem;
  model_t *retval;

  new_elem = (model_elem_t *) safe_malloc(sizeof(model_elem_t));

  get_yices_lock(&model_lock);

  list_insert_next(&model_list, &new_elem->header);

  release_yices_lock(&model_lock);

  retval = &new_elem->model;

  create_yices_lock(&(retval->lock));

  return retval;
}


/*
 * Remove c from the list and free m
 * - WARNING: make sure to call delete_model(c) before this
 *   function
 */
static void free_model(model_t *m) {
  dl_list_t *elem;

  elem = header_of_model(m);

  destroy_yices_lock(&(m->lock));

  get_yices_lock(&model_lock);

  list_remove(elem);
  safe_free(elem);

  release_yices_lock(&model_lock);

}


/*
 * Cleanup the model list
 */
static void free_model_list(void) {
  dl_list_t *elem, *aux;

  get_yices_lock(&model_lock);

  elem = model_list.next;
  while (elem != &model_list) {
    aux = elem->next;
    delete_model(model_of_header(elem));
    safe_free(elem);
    elem = aux;
  }

  clear_list(&model_list);

  release_yices_lock(&model_lock);

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
 * Allocate a structure and insert it into the generic
 * WARNING: the record is not initialized
 */
static ctx_config_t *alloc_config_structure(void) {
  ctx_config_elem_t *new_elem;
  ctx_config_t *retval;

  new_elem = (ctx_config_elem_t *) safe_malloc(sizeof(ctx_config_elem_t));

  /* add the new elem to the generic list */

  get_yices_lock(&generic_lock);

  list_insert_next(&generic_list, &new_elem->header);

  release_yices_lock(&generic_lock);

  create_yices_lock(&(new_elem->config.lock));

  retval = &new_elem->config;

  /* initialize the ctx_config_t lock */

  create_yices_lock(&(retval->lock));

  return retval;
}

static param_t *alloc_param_structure(void) {
  param_structure_elem_t *new_elem;
  param_t *retval;

  new_elem = (param_structure_elem_t *) safe_malloc(sizeof(param_structure_elem_t));

  get_yices_lock(&generic_lock);

  list_insert_next(&generic_list, &new_elem->header);

  release_yices_lock(&generic_lock);

  retval = &new_elem->param;

  /* initialize the param_t lock */

  create_yices_lock(&(retval->lock));

  return  retval;
}

/*
 * Remove a structure from the generic list
 */
static void free_config_structure(ctx_config_t *c) {
  dl_list_t *elem;

  elem = header_of_config_structure(c);

  /* reclaim the lock */
  destroy_yices_lock(&(c->lock));

  /* remove the ctx_config_t object from the generic list */

  get_yices_lock(&generic_lock);

  list_remove(elem);
  safe_free(elem);

  release_yices_lock(&generic_lock);
}

static void free_param_structure(param_t *p) {
  dl_list_t *elem;


  elem = header_of_param_structure(p);

  /* reclaim the lock */
  destroy_yices_lock(&(p->lock));

  /* remove the param_t object from the generic list */
  
  get_yices_lock(&generic_lock);
  
  list_remove(elem);
  safe_free(elem);
  
  release_yices_lock(&generic_lock);
}


/*
 * Empty the generic list
 */
static void free_generic_list(void) {
  dl_list_t *elem, *aux;

  get_yices_lock(&generic_lock);

  elem = generic_list.next;
  while (elem != &generic_list) {
    aux = elem->next;
    safe_free(elem);
    elem = aux;
  }

  clear_list(&generic_list);

  release_yices_lock(&generic_lock);
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
  
  if (__yices_globals.parser == NULL) {
    assert(__yices_globals.lexer == NULL && __yices_globals.tstack == NULL);
    __yices_globals.tstack = (tstack_t *) safe_malloc(sizeof(tstack_t));
    init_tstack(__yices_globals.tstack, NUM_BASE_OPCODES);

    __yices_globals.lexer = (lexer_t *) safe_malloc(sizeof(lexer_t));
    init_string_lexer(__yices_globals.lexer, s, "yices");

    __yices_globals.parser = (parser_t *) safe_malloc(sizeof(parser_t));
    init_parser(__yices_globals.parser, __yices_globals.lexer, __yices_globals.tstack);

  } else {
    // reset the input string
    assert(__yices_globals.lexer != NULL && __yices_globals.tstack != NULL);
    reset_string_lexer(__yices_globals.lexer, s);
  }

  return __yices_globals.parser;
}


/*
 * Delete the internal parser, lexer, term stack
 * (it they exist)
 */
static void delete_parsing_objects(void) {

  if (__yices_globals.parser != NULL) {
    assert(__yices_globals.lexer != NULL && __yices_globals.tstack != NULL);
    delete_parser(__yices_globals.parser);
    safe_free(__yices_globals.parser);
    __yices_globals.parser = NULL;

    close_lexer(__yices_globals.lexer);
    safe_free(__yices_globals.lexer);
    __yices_globals.lexer = NULL;

    delete_tstack(__yices_globals.tstack);
    safe_free(__yices_globals.tstack);
    __yices_globals.tstack = NULL;

  }

  assert(__yices_globals.lexer == NULL && __yices_globals.tstack == NULL);

}




/***************************************
 *  GLOBAL INITIALIZATION AND CLEANUP  *
 **************************************/

/*
 * Initialize the table of global objects
 */



static void init_globals(yices_globals_t *glob) {

  /* first the global object, then the miscellaneous globals */

  type_table_t *types = (type_table_t *)safe_malloc(sizeof(type_table_t));
  term_table_t *terms = (term_table_t *)safe_malloc(sizeof(term_table_t));
  term_manager_t *manager = (term_manager_t *)safe_malloc(sizeof(term_manager_t));
  //error_report_t *error = (error_report_t *)safe_malloc(sizeof(error_report_t));
  pprod_table_t *pprods = (pprod_table_t *)safe_malloc(sizeof(pprod_table_t));   

  memset(types, 0, sizeof(type_table_t));
  memset(terms, 0, sizeof(term_table_t));
  memset(manager, 0, sizeof(term_manager_t));
  //memset(error, 0, sizeof(error_report_t));
  memset(pprods, 0, sizeof(pprod_table_t));

  glob->types = types;
  glob->terms = terms;
  glob->manager = manager;
  //glob->error = error;
  glob->pprods = pprods;

  /* the parser state */
  glob->parser = NULL;
  glob->lexer = NULL;
  glob->tstack = NULL;

  create_yices_lock(&(glob->lock));

}


/*
 * Reset all to NULL (and free up the memory)
 */
static void clear_globals(yices_globals_t *glob) {

  free(glob->types);
  free(glob->terms);
  free(glob->manager);
  //free(glob->error);
  //free(glob->pprods);    //bruno?

  glob->types = NULL;
  glob->terms = NULL;
  glob->manager = NULL;
  //glob->error = NULL;
  //glob->pprods = NULL;    //bruno?

  
  destroy_yices_lock(&(glob->lock));


}

/*
 * Initialize all global objects
 */
EXPORTED void yices_init(void) {
  type_table_t *types;
  term_table_t *terms;
  term_manager_t *manager;
  //error_report_t *error;
  pprod_table_t *pprods;   

  // allocate the global table
  init_globals(&__yices_globals);

  types = __yices_globals.types;
  terms = __yices_globals.terms;
  manager = __yices_globals.manager;
  //error = __yices_globals.error;
  pprods = __yices_globals.pprods;   


  //error->code = NO_ERROR;

  init_yices_pp_tables();
  init_yices_lexer_table();
  init_bvconstants();
  init_rationals();

  // tables
  init_type_table(types, INIT_TYPE_SIZE);
  init_pprod_table(pprods, 0);
  init_term_table(terms, INIT_TERM_SIZE, types, pprods);
  init_term_manager(manager, types, terms);

  // buffer lists
  create_yices_lock(&(bvarith_buffer_lock));
  clear_list(&bvarith_buffer_list);

  create_yices_lock(&(bvarith64_buffer_lock));
  clear_list(&bvarith64_buffer_list);

  create_yices_lock(&(bvlogic_buffer_lock));
  clear_list(&bvlogic_buffer_list);

  // other dynamic object lists
  create_yices_lock(&(context_lock));
  clear_list(&context_list);

  create_yices_lock(&(model_lock));
  clear_list(&model_list);

  create_yices_lock(&(generic_lock));
  clear_list(&generic_list);


  // registries for garbage collection
  create_yices_lock(&(root_lock));
  root_terms = NULL;
  root_types = NULL;

}


/*
 * Cleanup: delete all tables and internal data structures
 */
EXPORTED void yices_exit(void) {
  type_table_t *types = __yices_globals.types;
  term_table_t *terms = __yices_globals.terms;
  term_manager_t *manager = __yices_globals.manager;
  pprod_table_t *pprods = __yices_globals.pprods;   

  // registries
  if (root_terms != NULL) {
    assert(root_terms == &the_root_terms);
    delete_sparse_array(&the_root_terms);
  }
  if (root_types != NULL) {
    assert(root_types == &the_root_types);
    delete_sparse_array(&the_root_types);
  }

  // parser etc.
  delete_parsing_objects();


  free_bvlogic_buffer_list();
  free_bvarith_buffer_list();
  free_bvarith64_buffer_list();

  free_context_list();
  free_model_list();
  free_generic_list();

  delete_term_manager(manager);
  delete_term_table(terms);
  delete_pprod_table(pprods);
  delete_type_table(types);

  clear_globals(&__yices_globals);

  /* ditch the global locks */
  destroy_yices_lock(&(bvarith_buffer_lock));
  destroy_yices_lock(&(bvarith64_buffer_lock));
  destroy_yices_lock(&(bvlogic_buffer_lock));
  destroy_yices_lock(&(context_lock));
  destroy_yices_lock(&(model_lock));
  destroy_yices_lock(&(generic_lock));
  destroy_yices_lock(&(root_lock));



  cleanup_rationals();
  cleanup_bvconstants();
}



/*
 * Full reset: delete everything
 */
EXPORTED void yices_reset(void) {
  yices_exit();
  yices_init();
}


/*
 * Get the last error report
 */
EXPORTED error_report_t *yices_error_report(void) {
  //  return __yices_globals.error;
  return get_yices_error();
}

EXPORTED error_report_t *yices_get_error_report(void) {
  //return __yices_globals.error;
  return get_yices_error();
}



/*
 * Get the last error code
 */
EXPORTED error_code_t yices_error_code(void) {
  error_report_t *error = get_yices_error();
  return error->code;
  // return __yices_globals.error->code;
}

EXPORTED error_code_t yices_get_error_code(void) {
  error_report_t *error = get_yices_error();
  return error->code;
  // return __yices_globals.error->code;
}


/*
 * Clear the last error report
 */
EXPORTED void yices_clear_error(void) {
  error_report_t *error = get_yices_error();
  error->code = NO_ERROR;

  //__yices_globals.error->code = NO_ERROR;
}


/*
 * Print an error message on f
 */
EXPORTED int32_t yices_print_error(FILE *f) {
  return print_error(f);
}




/***********************
 *  BUFFER ALLOCATION  *
 **********************/

/*
 * These functions are not part of the API.
 * They are exported to be used by other yices modules.
 */


/*
 * Allocate and initialize a bvarith_buffer
 * - the buffer is initialized to 0b0...0 (with n bits)
 * - n must be positive and no more than YICES_MAX_BVSIZE
 *
 * _o_yices_new_bvarith_buffer: non locking version
 *
 *  yices_new_bvarith_buffer: locking version (exported)
 *
 */
bvarith_buffer_t *_o_yices_new_bvarith_buffer(uint32_t n) {
  term_manager_t *manager = __yices_globals.manager;
  bvarith_buffer_t *b;

  b = alloc_bvarith_buffer();
  init_bvarith_buffer(b, __yices_globals.pprods, term_manager_get_bvarith_store(manager));
  bvarith_buffer_prepare(b, n);

  return b;
}


bvarith_buffer_t *yices_new_bvarith_buffer(uint32_t n) {
  bvarith_buffer_t *retval;

  get_yices_lock(&(__yices_globals.lock));
  
  retval = _o_yices_new_bvarith_buffer(n);
  
  release_yices_lock(&(__yices_globals.lock));
  
  return retval;
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
  term_manager_t *manager = __yices_globals.manager;
  bvarith64_buffer_t *b;

  b = alloc_bvarith64_buffer();
  init_bvarith64_buffer(b, __yices_globals.pprods, term_manager_get_bvarith64_store(manager));
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
  term_manager_t *manager = __yices_globals.manager;
  bvlogic_buffer_t *b;

  b = alloc_bvlogic_buffer();
  init_bvlogic_buffer(b, term_manager_get_nodes(manager));

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

void bvarith_buffer_iterate(void *aux, void (*f)(void *, bvarith_buffer_t *)) {  //bruno?  hope these f's don't use locks 
  dl_list_t *elem;

  get_yices_lock(&bvarith_buffer_lock);

  for (elem = bvarith_buffer_list.next;
       elem != &bvarith_buffer_list;
       elem = elem->next) {
    f(aux, bvarith_buffer(elem));
  }

  release_yices_lock(&bvarith_buffer_lock);

}

void bvarith64_buffer_iterate(void *aux, void (*f)(void *, bvarith64_buffer_t *)) { //bruno?  hope these f's don't use locks
  dl_list_t *elem;

  get_yices_lock(&bvarith64_buffer_lock);

  for (elem = bvarith64_buffer_list.next;
       elem != &bvarith64_buffer_list;
       elem = elem->next) {
    f(aux, bvarith64_buffer(elem));
  }

  release_yices_lock(&bvarith64_buffer_lock);

}

void bvlogic_buffer_iterate(void *aux, void (*f)(void *, bvlogic_buffer_t *)) { //bruno?  hope these f's don't use locks
  dl_list_t *elem;

  get_yices_lock(&bvlogic_buffer_lock);

  for (elem = bvlogic_buffer_list.next;
       elem != &bvlogic_buffer_list;
       elem = elem->next) {
    f(aux, bvlogic_buffer(elem));
  }

  release_yices_lock(&bvlogic_buffer_lock);

}

void context_iterate(void *aux, void (*f)(void *, context_t *)) {
  dl_list_t *elem;

  get_yices_lock(&context_lock);

  for (elem = context_list.next;
       elem != &context_list;
       elem = elem->next) {
    f(aux, context_of_header(elem));
  }

  release_yices_lock(&context_lock);

}

void model_iterate(void *aux, void (*f)(void *, model_t *)) {
  dl_list_t *elem;

  get_yices_lock(&context_lock);

  for (elem = context_list.next;
       elem != &context_list;
       elem = elem->next) {
    f(aux, model_of_header(elem));
  }

  release_yices_lock(&context_lock);

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
  error_report_t *error = get_yices_error();

  if (n == 0) {
    error->code = POS_INT_REQUIRED;
    error->badval = n;
    return false;
  }
  return true;
}

// Check whether n is less than YICES_MAX_ARITY
static bool check_arity(uint32_t n) {
  error_report_t *error = get_yices_error();

  if (n > YICES_MAX_ARITY) {
    error->code = TOO_MANY_ARGUMENTS;
    error->badval = n;
    return false;
  }
  return true;
}

// Check whether n is less than YICES_MAX_BVSIZE
static bool check_maxbvsize(uint32_t n) {
  error_report_t *error = get_yices_error();

  if (n > YICES_MAX_BVSIZE) {
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = n;
    return false;
  }
  return true;
}

// Check whether d is no more than YICES_MAX_DEGREE
static bool check_maxdegree(uint32_t d) {
  error_report_t *error = get_yices_error();
 
  if (d > YICES_MAX_DEGREE) {
    error->code = DEGREE_OVERFLOW;
    error->badval = d;
    return false;
  }
  return true;
}

// Check whether tau is a valid type
static bool check_good_type(type_table_t *tbl, type_t tau) {
  error_report_t *error = get_yices_error();

  if (bad_type(tbl, tau)) {
    error->code = INVALID_TYPE;
    error->type1 = tau;
    return false;
  }
  return true;
}

// Check whether tau is a bitvector type (tau is valid)
static bool check_bvtype(type_table_t *tbl, type_t tau) {
  error_report_t *error = get_yices_error();

  if (! is_bv_type(tbl, tau)) {
    error->code = BVTYPE_REQUIRED;
    error->type1 = tau;
    return false;
  }
  return true;
}

// Check whether t is a valid term
static bool check_good_term(term_manager_t *mngr, term_t t) {
  error_report_t *error = get_yices_error();
  term_table_t *tbl;

  tbl = term_manager_get_terms(mngr);
  if (bad_term(tbl, t)) {
    error->code = INVALID_TERM;
    error->term1 = t;
    return false;
  }
  return true;
}

// Check that terms in a[0 ... n-1] are valid
static bool check_good_terms(term_manager_t *mngr, uint32_t n, term_t *a) {
  error_report_t *error = get_yices_error();
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    if (bad_term(tbl, a[i])) {
      error->code = INVALID_TERM;
      error->term1 = a[i];
      return false;
    }
  }
  return true;
}


// Check whether t is a boolean term. t must be a valid term
static bool check_boolean_term(term_manager_t *mngr, term_t t) {
  error_report_t *error = get_yices_error();
  term_table_t *tbl;

  tbl = term_manager_get_terms(mngr);

  if (! is_boolean_term(tbl, t)) {
    error->code = TYPE_MISMATCH;
    error->term1 = t;
    error->type1 = bool_type(tbl->types);
    return false;
  }
  return true;
}


// Check whether t is a bitvector term, t must be valid
static bool check_bitvector_term(term_manager_t *mngr, term_t t) {
  error_report_t *error = get_yices_error();
  term_table_t *tbl;

  tbl = term_manager_get_terms(mngr);

  if (! is_bitvector_term(tbl, t)) {
    error->code = BITVECTOR_REQUIRED;
    error->term1 = t;
    return false;
  }
  return true;
}

// Check whether t1 and t2 have compatible types (i.e., (= t1 t2) is well-typed)
// t1 and t2 must both be valid
static bool check_compatible_terms(term_manager_t *mngr, term_t t1, term_t t2) {
  error_report_t *error = get_yices_error();
  term_table_t *tbl;
  type_t tau1, tau2;

  tbl = term_manager_get_terms(mngr);

  tau1 = term_type(tbl, t1);
  tau2 = term_type(tbl, t2);
  if (! compatible_types(tbl->types, tau1, tau2)) {
    error->code = INCOMPATIBLE_TYPES;
    error->term1 = t1;
    error->type1 = tau1;
    error->term2 = t2;
    error->type2 = tau2;
    return false;
  }

  return true;
}

// Check whether (= t1 t2) is type correct
static bool check_good_eq(term_manager_t *mngr, term_t t1, term_t t2) {
  return check_good_term(mngr, t1) && check_good_term(mngr, t2) &&
    check_compatible_terms(mngr, t1, t2);
}

// Check that t1 and t2 are bitvectors of the same size
static bool check_compatible_bv_terms(term_manager_t *mngr, term_t t1, term_t t2) {
  return check_good_term(mngr, t1) && check_good_term(mngr, t2)
    && check_bitvector_term(mngr, t1) && check_bitvector_term(mngr, t2)
    && check_compatible_terms(mngr, t1, t2);
}

// Check whether terms a[0 ... n-1] are all boolean
static bool check_boolean_args(term_manager_t *mngr, uint32_t n, term_t *a) {
  error_report_t *error = get_yices_error();
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    if (! is_boolean_term(tbl, a[i])) {
      error->code = TYPE_MISMATCH;
      error->term1 = a[i];
      error->type1 = bool_type(tbl->types);
      return false;
    }
  }

  return true;
}


// Check (distinct t_1 ... t_n)
static bool check_good_distinct_term(term_manager_t *mngr, uint32_t n, term_t *a) {
  error_report_t *error = get_yices_error();
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
      error->code = INCOMPATIBLE_TYPES;
      error->term1 = a[0];
      error->type1 = term_type(tbl, a[0]);
      error->term2 = a[i];
      error->type2 = term_type(tbl, a[i]);
      return false;
    }
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
  error_report_t *error = get_yices_error();
  term_table_t *tbl;
  uint64_t d;

  tbl = term_manager_get_terms(mngr);

  d = term_degree(tbl, t) * n;
  if (d > ((uint64_t) YICES_MAX_DEGREE)) {
    error->code = DEGREE_OVERFLOW;
    error->badval = UINT32_MAX;
    return false;
  }

  return check_maxdegree((uint32_t) d);
}



// Check whether i is a valid shift for bitvectors of size n
static bool check_bitshift(uint32_t i, uint32_t n) {
  error_report_t *error = get_yices_error();
  if (i > n) {
    error->code = INVALID_BITSHIFT;
    error->badval = i;
    return false;
  }

  return true;
}

// Check whether [i, j] is a valid segment for bitvectors of size n
static bool check_bitextract(uint32_t i, uint32_t j, uint32_t n) {
  if (i > j || j >= n) {
    error_report_t *error = get_yices_error();
    error->code = INVALID_BVEXTRACT;
    return false;
  }
  return true;
}


// Check that t is an uninterpreted term
static bool term_is_uninterpreted(term_table_t *tbl, term_t t) {
  assert(good_term(tbl, t) && is_pos_term(t));
  return term_kind(tbl, t) == UNINTERPRETED_TERM;
}

// Check that all terms of v are uninterpreted terms
// all elements of v must be good terms
static bool check_good_uninterpreted(term_manager_t *mngr, uint32_t n, term_t *v) {
  error_report_t *error = get_yices_error();
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);
  for (i=0; i<n; i++) {
    if (is_neg_term(v[i]) || !term_is_uninterpreted(tbl, v[i])) {
      error->code = VARIABLE_REQUIRED;
      error->term1 = v[i];
      return false;
    }
  }

  return true;
}

// Check whether arrays v and a define a valid substitution
// both must be arrays of n elements
static bool check_good_substitution(term_manager_t *mngr, uint32_t n, term_t *v, term_t *a) {
  error_report_t *error = get_yices_error();
  term_table_t *tbl;
  type_t tau;
  uint32_t i;

  if (! check_good_terms(mngr, n, v) ||
      ! check_good_terms(mngr, n, a) ||
      ! check_good_uninterpreted(mngr, n, v)) {
    return false;
  }

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    tau = term_type(tbl, v[i]);
    if (! is_subtype(tbl->types, term_type(tbl, a[i]), tau)) {
      error->code = TYPE_MISMATCH;
      error->term1 = a[i];
      error->type1 = tau;
      return false;
    }
  }

  return true;
}


/***********************
 *  TYPE CONSTRUCTORS  *
 **********************/

/* locking version */
EXPORTED type_t yices_bool_type(void) {
  yices_lock_t *lock = &__yices_globals.lock;
  type_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bool_type();

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
type_t _o_yices_bool_type(void) {
  return bool_type(__yices_globals.types);
}

/* locking version */
EXPORTED type_t yices_bv_type(uint32_t size) {
  yices_lock_t *lock = &__yices_globals.lock;
  type_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bv_type(size);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
type_t _o_yices_bv_type(uint32_t size) {
  if (! check_positive(size) || ! check_maxbvsize(size)) {
    return NULL_TYPE;
  }
  return bv_type(__yices_globals.types, size);
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

/* locking version */
EXPORTED term_t yices_new_uninterpreted_term(type_t tau) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_new_uninterpreted_term(tau);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_new_uninterpreted_term(type_t tau) {
  if (! check_good_type(__yices_globals.types, tau)) {
    return NULL_TERM;
  }

  return mk_uterm(__yices_globals.manager, tau);
}

/* locking version */
EXPORTED term_t yices_ite(term_t cond, term_t then_term, term_t else_term) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_ite(cond, then_term, else_term);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_ite(term_t cond, term_t then_term, term_t else_term) {
  term_table_t *tbl = __yices_globals.terms;
  term_manager_t *manager = __yices_globals.manager;
  error_report_t *error = get_yices_error();
  type_t tau;

  // Check type correctness: first steps
  if (! check_good_term(manager, cond) ||
      ! check_good_term(manager, then_term) ||
      ! check_good_term(manager, else_term) ||
      ! check_boolean_term(manager, cond)) {
    return NULL_TERM;
  }

  // Check whether then/else are compatible and get the supertype
  tau = super_type(__yices_globals.types, term_type(tbl, then_term), term_type(tbl, else_term));

  if (tau == NULL_TYPE) {
    // type error
    error->code = INCOMPATIBLE_TYPES;
    error->term1 = then_term;
    error->type1 = term_type(tbl, then_term);
    error->term2 = else_term;
    error->type2 = term_type(tbl, else_term);
    return NULL_TERM;
  }

  return mk_ite(manager, cond, then_term, else_term, tau);
}

/* locking version */
EXPORTED term_t yices_eq(term_t left, term_t right) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_eq(left, right);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_eq(term_t left, term_t right) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_good_eq(manager, left, right)) {
    return NULL_TERM;
  }

  return mk_eq(manager, left, right);
}

/* locking version */
EXPORTED term_t yices_neq(term_t left, term_t right) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_neq(left, right);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_neq(term_t left, term_t right) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_good_eq(manager, left, right)) {
    return NULL_TERM;
  }

  return mk_neq(manager, left, right);
}


/*
 * BOOLEAN NEGATION
 */

/* locking version */
EXPORTED term_t yices_not(term_t arg) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_not(arg);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_not(term_t arg) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_good_term(manager, arg) ||
      ! check_boolean_term(manager, arg)) {
    return NULL_TERM;
  }

  return opposite_term(arg);
}


/*
 * OR, AND, and XOR may modify arg
 */

/* locking version */
EXPORTED term_t yices_or(uint32_t n, term_t arg[]) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_or(n, arg);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_or(uint32_t n, term_t arg[]) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_arity(n) ||
      ! check_good_terms(manager, n, arg) ||
      ! check_boolean_args(manager, n, arg)) {
    return NULL_TERM;
  }

  switch (n) {
  case 0:
    return false_term;
  case 1:
    return arg[0];
  case 2:
    return mk_binary_or(manager, arg[0], arg[1]);
  default:
    return mk_or(manager, n, arg);
  }
}

/* locking version */
EXPORTED term_t yices_and(uint32_t n, term_t arg[]) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_and(n, arg);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_and(uint32_t n, term_t arg[]) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_arity(n) ||
      ! check_good_terms(manager, n, arg) ||
      ! check_boolean_args(manager, n, arg)) {
    return NULL_TERM;
  }

  switch (n) {
  case 0:
    return true_term;
  case 1:
    return arg[0];
  case 2:
    return mk_binary_and(manager, arg[0], arg[1]);
  default:
    return mk_and(manager, n, arg);
  }
}

/* locking version */
EXPORTED term_t yices_xor(uint32_t n, term_t arg[]) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_xor(n, arg);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_xor(uint32_t n, term_t arg[]) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_arity(n) ||
      ! check_good_terms(manager, n, arg) ||
      ! check_boolean_args(manager, n, arg)) {
    return NULL_TERM;
  }

  switch (n) {
  case 0:
    return false_term;
  case 1:
    return arg[0];
  case 2:
    return mk_binary_xor(manager, arg[0], arg[1]);
  default:
    return mk_xor(manager, n, arg);
  }
}



// Variant: 3 arguments
EXPORTED term_t yices_or3(term_t t1, term_t t2, term_t t3) {
  term_t aux[3];

  aux[0] = t1;
  aux[1] = t2;
  aux[2] = t3;

  return yices_or(3, aux);
}

EXPORTED term_t yices_and3(term_t t1, term_t t2, term_t t3) {
  term_t aux[3];

  aux[0] = t1;
  aux[1] = t2;
  aux[2] = t3;

  return yices_and(3, aux);
}

EXPORTED term_t yices_xor3(term_t t1, term_t t2, term_t t3) {
  term_t aux[3];

  aux[0] = t1;
  aux[1] = t2;
  aux[2] = t3;

  return yices_xor(3, aux);
}



/*
 * BINARY VERSIONS OF OR/AND/XOR
 */

/* locking version */
EXPORTED term_t yices_or2(term_t left, term_t right) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_or2(left, right);

  release_yices_lock(lock);

  return retval;
}


/* non-locking version */
term_t _o_yices_or2(term_t left, term_t right) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_good_term(manager, left) ||
      ! check_good_term(manager, right) ||
      ! check_boolean_term(manager, left) ||
      ! check_boolean_term(manager, right)) {
    return NULL_TERM;
  }

  return mk_binary_or(manager, left, right);
}

/* locking version */
EXPORTED term_t yices_and2(term_t left, term_t right) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_and2(left, right);

  release_yices_lock(lock);

  return retval;
}
/* non-locking version */
term_t _o_yices_and2(term_t left, term_t right) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_good_term(manager, left) ||
      ! check_good_term(manager, right) ||
      ! check_boolean_term(manager, left) ||
      ! check_boolean_term(manager, right)) {
    return NULL_TERM;
  }

  return mk_binary_and(manager, left, right);
}

/* locking version */
EXPORTED term_t yices_xor2(term_t left, term_t right) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_xor2(left, right);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_xor2(term_t left, term_t right) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_good_term(manager, left) ||
      ! check_good_term(manager, right) ||
      ! check_boolean_term(manager, left) ||
      ! check_boolean_term(manager, right)) {
    return NULL_TERM;
  }

  return mk_binary_xor(manager, left, right);
}


/* locking version */
EXPORTED term_t yices_iff(term_t left, term_t right) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_iff(left, right);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_iff(term_t left, term_t right) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_good_term(manager, left) ||
      ! check_good_term(manager, right) ||
      ! check_boolean_term(manager, left) ||
      ! check_boolean_term(manager, right)) {
    return NULL_TERM;
  }

  return mk_iff(manager, left, right);
}

/* locking version */
EXPORTED term_t yices_implies(term_t left, term_t right) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_implies(left, right);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_implies(term_t left, term_t right) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_good_term(manager, left) ||
      ! check_good_term(manager, right) ||
      ! check_boolean_term(manager, left) ||
      ! check_boolean_term(manager, right)) {
    return NULL_TERM;
  }

  return mk_implies(manager, left, right);
}


/* locking version */
EXPORTED term_t yices_distinct(uint32_t n, term_t arg[]) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_distinct(n, arg);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_distinct(uint32_t n, term_t arg[]) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_positive(n) ||
      ! check_arity(n) ||
      ! check_good_distinct_term(manager, n, arg)) {
    return NULL_TERM;
  }

  return mk_distinct(manager, n, arg);
}





/**************************
 *  BITVECTOR CONSTANTS   *
 *************************/

/* locking version */
EXPORTED term_t yices_bvconst_uint32(uint32_t n, uint32_t x) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvconst_uint32(n, x);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvconst_uint32(uint32_t n, uint32_t x) {
  term_t retval;
  bvconstant_t bv0;
 
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  init_bvconstant(&bv0);

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set32(bv0.data, bv0.width, x);

  retval = mk_bv_constant(__yices_globals.manager, &bv0);

  delete_bvconstant(&bv0);

  return retval;
}


/* locking version */
EXPORTED term_t yices_bvconst_uint64(uint32_t n, uint64_t x) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvconst_uint64(n, x);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvconst_uint64(uint32_t n, uint64_t x) {
  term_t retval;
  bvconstant_t bv0;

  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  init_bvconstant(&bv0);
  bvconstant_set_bitsize(&bv0, n);
  bvconst_set64(bv0.data, bv0.width, x);
  
  retval =  mk_bv_constant(__yices_globals.manager, &bv0);

  delete_bvconstant(&bv0);

  return retval;
}


/* locking version */
EXPORTED term_t yices_bvconst_mpz(uint32_t n, mpz_t x) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvconst_mpz(n, x);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvconst_mpz(uint32_t n, mpz_t x) {
  term_t retval;
  bvconstant_t bv0;

  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }


  init_bvconstant(&bv0);

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set_mpz(bv0.data, bv0.width, x);
  
  retval = mk_bv_constant(__yices_globals.manager, &bv0);
  
  delete_bvconstant(&bv0);

  return retval;
}


/*
 * bvconst_zero: set all bits to 0
 * bvconst_one: set low-order bit to 1, all the others to 0
 * bvconst_minus_one: set all bits to 1
 */

/* locking version */
EXPORTED term_t yices_bvconst_zero(uint32_t n) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvconst_zero(n);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvconst_zero(uint32_t n) {
  term_t retval;
  bvconstant_t bv0;

 if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

 init_bvconstant(&bv0);
 
 bvconstant_set_all_zero(&bv0, n);
 
 retval =  mk_bv_constant(__yices_globals.manager, &bv0);
 
 delete_bvconstant(&bv0);
 return retval;
}

/* locking version */
EXPORTED term_t yices_bvconst_one(uint32_t n) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvconst_one(n);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvconst_one(uint32_t n) {
  term_t retval;
  bvconstant_t bv0;
  
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  init_bvconstant(&bv0);

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set_one(bv0.data, bv0.width);

  retval = mk_bv_constant(__yices_globals.manager, &bv0);
  
  delete_bvconstant(&bv0);

  return retval;
}

/* locking version */
EXPORTED term_t yices_bvconst_minus_one(uint32_t n) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvconst_minus_one(n);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvconst_minus_one(uint32_t n) {
  term_t retval;
  bvconstant_t bv0;

  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  init_bvconstant(&bv0);

  bvconstant_set_all_one(&bv0, n);

  retval = mk_bv_constant(__yices_globals.manager, &bv0);

  delete_bvconstant(&bv0);

  return retval;
}


/*
 * Convert an integer array to a bit constant
 * - a[i] =  0 --> bit i = 0
 * - a[i] != 0 --> bit i = 1
 */

/* locking version */
EXPORTED term_t yices_bvconst_from_array(uint32_t n, int32_t a[]) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvconst_from_array(n, a);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvconst_from_array(uint32_t n, int32_t a[]) {
  term_t retval;
  bvconstant_t bv0;

  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  init_bvconstant(&bv0);

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set_array(bv0.data, a, n);

  retval = mk_bv_constant(__yices_globals.manager, &bv0);

  delete_bvconstant(&bv0);

  return retval;
}



/*
 * Parse a string of '0' and '1' and convert to a bit constant
 * - the number of bits is the length of s
 * - the string is read in big-endian format: the first character
 *   is the high-order bit.
 */

/* locking version */
EXPORTED term_t yices_parse_bvbin(const char *s) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_parse_bvbin(s);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_parse_bvbin(const char *s) {
  error_report_t *error = get_yices_error();
  term_t retval;
  bvconstant_t bv0;
  size_t len;
  uint32_t n;
  int32_t code;

  len = strlen(s);
  if (len == 0) {
    error->code = INVALID_BVBIN_FORMAT;
    return NULL_TERM;
  }

  if (len > YICES_MAX_BVSIZE) {
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = len; // slightly wrong: len is unsigned, badval is signed
    return NULL_TERM;
  }

  n = (uint32_t) len;

  init_bvconstant(&bv0);
  

  bvconstant_set_bitsize(&bv0, n);
  code = bvconst_set_from_string(bv0.data, n, s);

  if (code < 0) {
    error->code = INVALID_BVBIN_FORMAT;
    retval = NULL_TERM;
  } else {
    retval = mk_bv_constant(__yices_globals.manager, &bv0);
  }

  delete_bvconstant(&bv0);

  return retval;
}

// same function under a different name for backward compatibility
EXPORTED term_t yices_bvconst_from_string(const char *s) {
  return yices_parse_bvbin(s);
}



/*
 * Parse a string of hexa decimal digits and convert it to a bit constant
 * - return NULL_TERM if there's a format error
 * - the number of bits is four times the length of s
 * - the string is read in big-endian format (the first character defines
 *   the four high-order bits).
 */

/* locking version */
EXPORTED term_t yices_parse_bvhex(const char *s) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_parse_bvhex(s);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_parse_bvhex(const char *s) {
  error_report_t *error = get_yices_error();
  term_t retval;
  bvconstant_t bv0;
  size_t len;
  uint32_t n;
  int32_t code;

  len = strlen(s);
  if (len == 0) {
    error->code = INVALID_BVHEX_FORMAT;
    return NULL_TERM;
  }

  if (len > YICES_MAX_BVSIZE/4) {
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = ((uint64_t) len) * 4; // could overflow here
    return NULL_TERM;
  }

  n = (uint32_t) len;

  init_bvconstant(&bv0);


  bvconstant_set_bitsize(&bv0, 4 * n);
  code = bvconst_set_from_hexa_string(bv0.data, n, s);
  if (code < 0) {
    error->code = INVALID_BVHEX_FORMAT;
    retval = NULL_TERM;
  } else {

    retval = mk_bv_constant(__yices_globals.manager, &bv0);
  }

  
  delete_bvconstant(&bv0);

  return retval;
}


// same function under a different name for backward compatibility
EXPORTED term_t yices_bvconst_from_hexa_string(const char *s) {
  return yices_parse_bvhex(s);
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
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvarith64_buffer_t *b;

  b = term_manager_get_bvarith64_buffer(manager);
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_add_term(b, tbl, t2);

  return mk_bvarith64_term(manager, b);
}

static term_t mk_bvadd(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvarith_buffer_t *b;

  b = term_manager_get_bvarith_buffer(manager);
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_add_term(b, tbl, t2);

  return mk_bvarith_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_bvadd(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvadd(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvadd(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  if (term_bitsize(__yices_globals.terms, t1) <= 64) {
    return mk_bvadd64(t1, t2);
  } else {
    return mk_bvadd(t1, t2);
  }
}


static term_t mk_bvsub64(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvarith64_buffer_t *b;


  b = term_manager_get_bvarith64_buffer(manager);
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_sub_term(b, tbl, t2);

  return mk_bvarith64_term(manager, b);
}

static term_t mk_bvsub(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvarith_buffer_t *b;

  b = term_manager_get_bvarith_buffer(manager);

  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_sub_term(b, tbl, t2);

  return mk_bvarith_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_bvsub(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvsub(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvsub(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  if (term_bitsize(__yices_globals.terms, t1) <= 64) {
    return mk_bvsub64(t1, t2);
  } else {
    return mk_bvsub(t1, t2);
  }
}


static term_t mk_bvneg64(term_t t1) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvarith64_buffer_t *b;


  b = term_manager_get_bvarith64_buffer(manager);
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_negate(b);

  return mk_bvarith64_term(manager, b);
}

static term_t mk_bvneg(term_t t1) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvarith_buffer_t *b;


  b = term_manager_get_bvarith_buffer(manager);
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_negate(b);

  return mk_bvarith_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_bvneg(term_t t1) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvneg(t1);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvneg(term_t t1) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_good_term(manager, t1) ||
      ! check_bitvector_term(manager, t1)) {
    return NULL_TERM;
  }

  if (term_bitsize(__yices_globals.terms, t1) <= 64) {
    return mk_bvneg64(t1);
  } else {
    return mk_bvneg(t1);
  }
}


static term_t mk_bvmul64(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvarith64_buffer_t *b;

  b = term_manager_get_bvarith64_buffer(manager);
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_mul_term(b, tbl, t2);

  return mk_bvarith64_term(manager, b);
}

static term_t mk_bvmul(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvarith_buffer_t *b;

  b = term_manager_get_bvarith_buffer(manager);
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_mul_term(b, tbl, t2);

  return mk_bvarith_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_bvmul(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvmul(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvmul(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2) ||
      ! check_product_degree(manager, t1, t2)) {
    return NULL_TERM;
  }

  if (term_bitsize(__yices_globals.terms, t1) <= 64) {
    return mk_bvmul64(t1, t2);
  } else {
    return mk_bvmul(t1, t2);
  }
}


static term_t mk_bvsquare64(term_t t1) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvarith64_buffer_t *b;


  b = term_manager_get_bvarith64_buffer(manager);
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_square(b);

  return mk_bvarith64_term(manager, b);
}

static term_t mk_bvsquare(term_t t1) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvarith_buffer_t *b;


  b = term_manager_get_bvarith_buffer(manager);
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_square(b);

  return mk_bvarith_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_bvsquare(term_t t1) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvsquare(t1);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvsquare(term_t t1) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_good_term(manager, t1) ||
      ! check_bitvector_term(manager, t1) ||
      ! check_square_degree(manager, t1)) {
    return NULL_TERM;
  }

  if (term_bitsize(__yices_globals.terms, t1) <= 64) {
    return mk_bvsquare64(t1);
  } else {
    return mk_bvsquare(t1);
  }
}




static term_t mk_bvpower64(term_t t1, uint32_t d) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvarith64_buffer_t *b;
  uint32_t n;

  b = term_manager_get_bvarith64_buffer(manager);
  n = term_bitsize(tbl, t1);
  bvarith64_buffer_prepare(b, n);
  bvarith64_buffer_set_one(b);
  bvarith64_buffer_mul_term_power(b, tbl, t1, d);

  return mk_bvarith64_term(manager, b);
}

static term_t mk_bvpower(term_t t1, uint32_t d) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvarith_buffer_t *b;
  uint32_t n;

  b = term_manager_get_bvarith_buffer(manager);
  n = term_bitsize(tbl, t1);
  bvarith_buffer_prepare(b, n);
  bvarith_buffer_set_one(b);
  bvarith_buffer_mul_term_power(b, tbl, t1, d);

  return mk_bvarith_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_bvpower(term_t t1, uint32_t d) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvpower(t1, d);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvpower(term_t t1, uint32_t d) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_good_term(manager, t1) ||
      ! check_bitvector_term(manager, t1) ||
      ! check_power_degree(manager, t1, d)) {
    return NULL_TERM;
  }

  if (term_bitsize(__yices_globals.terms, t1) <= 64) {
    return mk_bvpower64(t1, d);
  } else {
    return mk_bvpower(t1, d);
  }
}



/***********************************
 *  BITWISE BIT-VECTOR OPERATIONS  *
 **********************************/

/* locking version */
EXPORTED term_t yices_bvnot(term_t t1) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvnot(t1);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvnot(term_t t1) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;  
  bvlogic_buffer_t *b;

  if (! check_good_term(manager, t1) ||
      ! check_bitvector_term(manager, t1)) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_not(b);

  return mk_bvlogic_term(manager, b);
}


/* locking version */
EXPORTED term_t yices_bvand(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvand(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvand(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_and_term(b, tbl, t2);

  return mk_bvlogic_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_bvor(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvor(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvor(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;


  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_or_term(b, tbl, t2);

  return mk_bvlogic_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_bvxor(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvxor(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvxor(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_xor_term(b, tbl, t2);

  return mk_bvlogic_term(manager, b);
}


/* locking version */
EXPORTED term_t yices_bvnand(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvnand(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvnand(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_and_term(b, tbl, t2);
  bvlogic_buffer_not(b);

  return mk_bvlogic_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_bvnor(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvnor(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvnor(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_or_term(b, tbl, t2);
  bvlogic_buffer_not(b);

  return mk_bvlogic_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_bvxnor(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvxnor(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvxnor(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_xor_term(b, tbl, t2);
  bvlogic_buffer_not(b);

  return mk_bvlogic_term(manager, b);
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

/* locking version */
EXPORTED term_t yices_shift_left0(term_t t, uint32_t n) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_shift_left0(t, n);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_shift_left0(term_t t, uint32_t n) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;


  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_shift_left0(b, n);

  return mk_bvlogic_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_shift_left1(term_t t, uint32_t n) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_shift_left1(t, n);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_shift_left1(term_t t, uint32_t n) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_shift_left1(b, n);

  return mk_bvlogic_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_shift_right0(term_t t, uint32_t n) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_shift_right0(t, n);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_shift_right0(term_t t, uint32_t n) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;
 
  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_shift_right0(b, n);

  return mk_bvlogic_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_shift_right1(term_t t, uint32_t n) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_shift_right1(t, n);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_shift_right1(term_t t, uint32_t n) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_shift_right1(b, n);

  return mk_bvlogic_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_ashift_right(term_t t, uint32_t n) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_ashift_right(t, n);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_ashift_right(term_t t, uint32_t n) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_ashift_right(b, n);

  return mk_bvlogic_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_rotate_left(term_t t, uint32_t n) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_rotate_left(t, n);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_rotate_left(term_t t, uint32_t n) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t);
  if (n < b->bitsize) {
    bvlogic_buffer_rotate_left(b, n);
  }

  return mk_bvlogic_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_rotate_right(term_t t, uint32_t n) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_rotate_right(t, n);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_rotate_right(term_t t, uint32_t n) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t);
  if (n < b->bitsize) {
    bvlogic_buffer_rotate_right(b, n);
  }

  return mk_bvlogic_term(manager, b);
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
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvextract(t, i, j) ;

  release_yices_lock(lock);

  return retval;
}

term_t _o_yices_bvextract(term_t t, uint32_t i, uint32_t j) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;
  uint32_t n;

  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t)) {
    return NULL_TERM;
  }

  n = term_bitsize(tbl, t);
  if (! check_bitextract(i, j, n)) {
    return NULL_TERM;
  }

  if (i == 0 && j == n-1) {
    return t;
  } else {
    b =  term_manager_get_bvlogic_buffer(manager);
    bvlogic_buffer_set_slice_term(b, tbl, i, j, t);
    return mk_bvlogic_term(manager, b);
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

/* locking version */
EXPORTED term_t yices_bvconcat(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvconcat(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvconcat(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_good_term(manager, t1) ||
      ! check_good_term(manager, t2) ||
      ! check_bitvector_term(manager, t1) ||
      ! check_bitvector_term(manager, t2) ||
      ! check_maxbvsize(term_bitsize(tbl, t1) + term_bitsize(tbl, t2))) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t2);
  bvlogic_buffer_concat_left_term(b, tbl, t1);

  return mk_bvlogic_term(manager, b);
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

/* locking version */
EXPORTED term_t yices_bvrepeat(term_t t, uint32_t n) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvrepeat(t, n);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvrepeat(term_t t, uint32_t n) {
  error_report_t *error = get_yices_error();
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  uint64_t m;

  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t) ||
      ! check_positive(n)) {
    return NULL_TERM;
  }

  // check size
  m = ((uint64_t) n) * term_bitsize(tbl, t);
  if (m > (uint64_t) YICES_MAX_BVSIZE) {
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = m;
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_repeat_concat(b, n);

  return mk_bvlogic_term(manager, b);
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

/* locking version */
EXPORTED term_t yices_sign_extend(term_t t, uint32_t n) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_sign_extend(t, n);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_sign_extend(term_t t, uint32_t n) {
  error_report_t *error = get_yices_error();
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;
  uint64_t m;

  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t)) {
    return NULL_TERM;
  }


  // check size
  m = ((uint64_t) n) + term_bitsize(tbl, t);
  if (m > (uint64_t) YICES_MAX_BVSIZE) {
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = m;
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_sign_extend(b, b->bitsize + n);

  return mk_bvlogic_term(manager, b);
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

/* locking version */
EXPORTED term_t yices_zero_extend(term_t t, uint32_t n) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_zero_extend(t, n);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_zero_extend(term_t t, uint32_t n) {
  error_report_t *error = get_yices_error();
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;
  uint64_t m;

  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t)) {
    return NULL_TERM;
  }

  // check size
  m = ((uint64_t) n) + term_bitsize(tbl, t);
  if (m > (uint64_t) YICES_MAX_BVSIZE) {
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = m;
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_zero_extend(b, b->bitsize + n);

  return mk_bvlogic_term(manager, b);
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

/* locking version */
EXPORTED term_t yices_redand(term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_redand(t);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_redand(term_t t) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t)) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_redand(b);

  return mk_bvlogic_term(manager, b);
}

/* locking version */
EXPORTED term_t yices_redor(term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_redor(t);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_redor(term_t t) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t)) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_redor(b);

  return mk_bvlogic_term(manager, b);
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

/* locking version */
EXPORTED term_t yices_redcomp(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_redcomp(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_redcomp(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  term_table_t *tbl = __yices_globals.terms;
  bvlogic_buffer_t *b;

  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_comp_term(b, tbl, t2);

  return mk_bvlogic_term(manager, b);
}




/*******************************
 *  GENERIC BIT-VECTOR SHIFTS  *
 *****************************/

/* locking version */
EXPORTED term_t yices_bvshl(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvshl(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvshl(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }

  return mk_bvshl(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvlshr(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvlshr(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvlshr(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }

  return mk_bvlshr(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvashr(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvashr(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvashr(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }

  return mk_bvashr(manager, t1, t2);
}





/**********************************
 *  BITVECTOR DIVISION OPERATORS  *
 *********************************/

/* locking version */
EXPORTED term_t yices_bvdiv(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvdiv(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvdiv(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvdiv(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvrem(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvrem(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvrem(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvrem(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvsdiv(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvsdiv(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvsdiv(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsdiv(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvsrem(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvsrem(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvsrem(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsrem(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvsmod(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvsmod(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvsmod(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsmod(manager, t1, t2);
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

/* locking version */
EXPORTED term_t yices_bvarray(uint32_t n, term_t arg[]) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvarray(n, arg);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvarray(uint32_t n, term_t arg[]) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_positive(n) ||
      ! check_maxbvsize(n) ||
      ! check_good_terms(manager, n, arg) ||
      ! check_boolean_args(manager, n, arg)) {
    return NULL_TERM;
  }
  return mk_bvarray(manager, n, arg);
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

/* locking version */
EXPORTED term_t yices_bitextract(term_t t, uint32_t i) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bitextract(t, i);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bitextract(term_t t, uint32_t i) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t) ||
      ! check_bitextract(i, i, term_bitsize(__yices_globals.terms, t))) {
    return NULL_TERM;
  }
  return mk_bitextract(manager, t, i);
}




/*********************
 *  BITVECTOR ATOMS  *
 ********************/

/* locking version */
EXPORTED term_t yices_bveq_atom(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bveq_atom(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bveq_atom(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bveq(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvneq_atom(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvneq_atom(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvneq_atom(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvneq(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvge_atom(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvge_atom(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvge_atom(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvge(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvgt_atom(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvgt_atom(t1, t2) ;

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvgt_atom(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvgt(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvle_atom(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvle_atom(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvle_atom(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvle(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvlt_atom(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvlt_atom(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvlt_atom(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvlt(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvsge_atom(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvsge_atom(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t  _o_yices_bvsge_atom(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsge(manager, t1, t2);
}

/* locking version */
EXPORTED term_t yices_bvsgt_atom(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvsgt_atom(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvsgt_atom(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsgt(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvsle_atom(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvsle_atom(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvsle_atom(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsle(manager, t1, t2);
}


/* locking version */
EXPORTED term_t yices_bvslt_atom(term_t t1, term_t t2) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvslt_atom(t1, t2);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_bvslt_atom(term_t t1, term_t t2) {
  term_manager_t *manager = __yices_globals.manager;
  if (! check_compatible_bv_terms(manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvslt(manager, t1, t2);
}



/*********************
 *  PRETTY PRINTING  *
 ********************/

/*
 * Pretty print type tau
 * - f = output file to use
 * - width, height, offset = print area
 */

/* locking version */
EXPORTED int32_t yices_pp_type(FILE *f, type_t tau, uint32_t width, uint32_t height, uint32_t offset) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_pp_type(f, tau, width, height, offset);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_pp_type(FILE *f, type_t tau, uint32_t width, uint32_t height, uint32_t offset) {
  error_report_t *error = get_yices_error();
  yices_pp_t printer;
  pp_area_t area;
  int32_t code;

  if (! check_good_type(__yices_globals.types, tau)) {
    return -1;
  }

  if (width < 4) width = 4;
  if (height == 0) height = 1;

  area.width = width;
  area.height = height;
  area.offset = offset;
  area.stretch = false;
  area.truncate = true;

  init_default_yices_pp(&printer, f, &area);
  pp_type_exp(&printer, __yices_globals.types, tau);
  flush_yices_pp(&printer);

  // check for error
  code = 0;
  if (yices_pp_print_failed(&printer)) {
    code = -1;
    errno = yices_pp_errno(&printer);
    error->code = OUTPUT_ERROR;
  }
  delete_yices_pp(&printer, false);

  return code;
}


/*
 * Pretty print term t
 * - f = output file to use
 * - width, height, offset = print area
 */

/* locking version */
EXPORTED int32_t yices_pp_term(FILE *f, term_t t, uint32_t width, uint32_t height, uint32_t offset) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_pp_term(f, t, width, height, offset);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_pp_term(FILE *f, term_t t, uint32_t width, uint32_t height, uint32_t offset) {
  error_report_t *error = get_yices_error();
  yices_pp_t printer;
  pp_area_t area;
  int32_t code;

  if (! check_good_term(__yices_globals.manager, t)) {
    return -1;
  }

  if (width < 4) width = 4;
  if (height == 0) height = 1;

  area.width = width;
  area.height = height;
  area.offset = offset;
  area.stretch = false;
  area.truncate = true;

  init_default_yices_pp(&printer, f, &area);
  pp_term_full(&printer, __yices_globals.terms, t);
  flush_yices_pp(&printer);

  // check for error
  code = 0;
  if (yices_pp_print_failed(&printer)) {
    code = -1;
    errno = yices_pp_errno(&printer);
    error->code = OUTPUT_ERROR;
  }
  delete_yices_pp(&printer, false);

  return code;
}



/*********************
 *  CHECKS ON TYPES  *
 ********************/

/*
 * Checks on a type tau:
 * - all functions return 0 for false, 1 for true
 *
 * yices_type_is_arithmetic(tau) returns true if tau is either int or real.
 *
 * if tau not a valid type, the functions return false
 * and set the error report:
 *   code = INVALID_TYPE
 *   type1 = tau
 */

/* locking version */
EXPORTED int32_t yices_type_is_bool(type_t tau) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_type_is_bool(tau);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_type_is_bool(type_t tau) {
  return check_good_type(__yices_globals.types, tau) && is_boolean_type(tau);
}

/* locking version */
EXPORTED int32_t yices_type_is_bitvector(type_t tau) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_type_is_bitvector(tau);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_type_is_bitvector(type_t tau) {
  return check_good_type(__yices_globals.types, tau) && is_bv_type(__yices_globals.types, tau);
}



/*
 * Check whether tau is a subtype of sigma
 * - return 0 for false, 1 for true
 *
 * If tau or sigma is not a valid type, the function returns false
 * and set the error report:
 *   code = INVALID_TYPE
 *   type1 = tau or sigma
 */

/* locking version */
EXPORTED int32_t yices_test_subtype(type_t tau, type_t sigma) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_test_subtype(tau, sigma);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_test_subtype(type_t tau, type_t sigma) {
  return check_good_type(__yices_globals.types, tau) && check_good_type(__yices_globals.types, sigma) && is_subtype(__yices_globals.types, tau, sigma);
}

/*
 * Number of bits for type tau
 * - return 0 if there's an error
 *
 * Error report:
 * if tau is not a valid type
 *    code = INVALID_TYPE
 *    type1 = tau
 * if tau is not a bitvector type
 *    code = BVTYPE_REQUIRED
 *    type1 = tau
 */

/* locking version */
EXPORTED uint32_t yices_bvtype_size(type_t tau) {
  yices_lock_t *lock = &__yices_globals.lock;
  uint32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_bvtype_size(tau);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
uint32_t _o_yices_bvtype_size(type_t tau) {
  if (! check_good_type(__yices_globals.types, tau) ||
      ! check_bvtype(__yices_globals.types, tau)) {
    return 0;
  }
  return bv_type_size(__yices_globals.types, tau);
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

/* locking version */
EXPORTED type_t yices_type_of_term(term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;
  type_t retval;

  get_yices_lock(lock);

  retval = _o_yices_type_of_term(t);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
type_t _o_yices_type_of_term(term_t t) {
  if (! check_good_term(__yices_globals.manager, t)) {
    return NULL_TYPE;
  }
  return term_type(__yices_globals.terms, t);
}


/*
 * Check the type of a term t:
 * - term_is_arithmetic check whether t's type is either int or real
 * - term_is_real check whether t's type is real (return false if t's type is int)
 * - term_is_int check whether t's type is int
 * If t is not a valid term, the check functions return false
 * and set the error report as above.
 */

/* locking version */
EXPORTED int32_t yices_term_is_bool(term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_term_is_bool(t);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_term_is_bool(term_t t) {
  return check_good_term(__yices_globals.manager, t) && is_boolean_term(__yices_globals.terms, t);
}

/* locking version */
EXPORTED int32_t yices_term_is_bitvector(term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_term_is_bitvector(t);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_term_is_bitvector(term_t t) {
  return check_good_term(__yices_globals.manager, t) && is_bitvector_term(__yices_globals.terms, t);
}

/*
 * Size of bitvector term t.
 * return 0 if t is not a bitvector
 */

/* locking version */
EXPORTED uint32_t yices_term_bitsize(term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;
  uint32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_term_bitsize(t);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
uint32_t _o_yices_term_bitsize(term_t t) {
  if (! check_bitvector_term(__yices_globals.manager, t)) {
    return 0;
  }
  return term_bitsize(__yices_globals.terms, t);
}




/***********************************
 *  EXTENSIONS: TERM CONSTRUCTORS  *
 **********************************/

/*
 * These term constructors are used in term_stack. Ian says: MAYBE NOT THESE THEN (essentially they are mk_xxxxx routines)
 */

term_t bvlogic_buffer_get_term(bvlogic_buffer_t *b) {
  return mk_bvlogic_term(__yices_globals.manager, b);
}

term_t bvarith_buffer_get_term(bvarith_buffer_t *b) {
  return mk_bvarith_term(__yices_globals.manager, b);
}

term_t bvarith64_buffer_get_term(bvarith64_buffer_t *b) {
  return mk_bvarith64_term(__yices_globals.manager, b);
}

term_t yices_bvconst_term(uint32_t n, uint32_t *v) {
  assert(64 < n && n <= YICES_MAX_BVSIZE);
  return bvconst_term(__yices_globals.terms, n, v);
}

term_t yices_bvconst64_term(uint32_t n, uint64_t c) {
  assert(1 <= n && n <= 64 && c == norm64(c, n));
  return bv64_constant(__yices_globals.terms, n, c);
}



/*******************************************
 *  EXTENSIONS: SUPPORT FOR TYPE CHECKING  *
 ******************************************/

/*
 * Check whether t is a valid boolean term
 * - if not set the internal error report
 *
 * If t is not a valid term:
 *   code = INVALID_TERM
 *   term1 = t
 *   index = -1
 * If t is not Boolean
 *   code = TYPE_MISMATCH
 *   term1 = t
 *   type = bool
 */
bool yices_check_boolean_term(term_t t) {
  term_manager_t *manager = __yices_globals.manager;
  return check_good_term(manager, t) && check_boolean_term(manager, t);
}

/*
 * Check whether t's type is a subtype of tau
 */
bool yices_check_term_type(term_t t, type_t tau) {
  error_report_t *error = get_yices_error();
  term_table_t *tbl = __yices_globals.terms;
  if (! is_subtype(tbl->types, term_type(tbl, t), tau)) {
    error->code = TYPE_MISMATCH;
    error->term1 = t;
    error->type1 = tau;
    return false;
  }

  return true;
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
  term_manager_t *manager = __yices_globals.manager;
  return check_good_term(manager, t) && check_bitvector_term(manager, t);
}


/*
 * Check whether b is non empty
 * Error report:
 *   code = EMPTY_BITVECTOR
 */
bool yices_check_bvlogic_buffer(bvlogic_buffer_t *b) {
  error_report_t *error = get_yices_error();
  if (bvlogic_buffer_is_empty(b)) {
    error->code = EMPTY_BITVECTOR;
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
  error_report_t *error = get_yices_error();
  if (s < 0 || s > bvlogic_buffer_bitsize(b)) {
    error->code = INVALID_BITSHIFT;
    error->badval = s;
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
  error_report_t *error = get_yices_error();
  if (i < 0 || i > j || j >= n) {
    error->code = INVALID_BVEXTRACT;
    return false;
  }

  return true;
}


/*
 * Check whether repeat_concat(b, n) is valid
 * - return true if it is
 * - return false and set error report if it's not.
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
  error_report_t *error = get_yices_error();
  uint64_t m;

  if (n <= 0) {
    error->code = POS_INT_REQUIRED;
    error->badval = n;
    return false;
  }

  m = ((uint64_t) n) * bvlogic_buffer_bitsize(b);
  if (m > ((uint64_t) YICES_MAX_BVSIZE)) {
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = m;
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
  error_report_t *error = get_yices_error();
  uint64_t m;

  if (n < 0) {
    error->code = NONNEG_INT_REQUIRED;
    error->badval = n;
    return false;
  }

  m = bvlogic_buffer_bitsize(b);
  if (m == 0) {
    error->code = EMPTY_BITVECTOR;
    return false;
  }

  m += n;
  if (m >= ((uint64_t) YICES_MAX_BVSIZE)) {
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = m;
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
 *   code = DEGREE_OVERFLOW
 *   badval = degree of the product
 *
 * All return true if there's no overflow.
 */
bool yices_check_bvmul64_term(bvarith64_buffer_t *b, term_t t) {
  term_table_t *tbl;
  uint32_t d1, d2;

  tbl = __yices_globals.terms;

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

  tbl = __yices_globals.terms;

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

/*
 * Apply the substitution defined by arrays var and map to a term t -
 * var must be an array of n variables (variables are created using
 * yices_new_variables).
 * - map must be an array of n terms
 * - the type of map[i] must be a subtype of var[i]'s type
 * - every occurrence of var[i] in t is replaced by map[i]
 *
 *
 * Return the resulting term or NULL_TERM if there's an error.
 *
 * Error codes:
 * - INVALID_TERM if var[i] or map[i] is not valid
 * - VARIABLE_REQUIRED if var[i] is not a variable
 * - TYPE_MISMATCH if map[i]'s type is not a subtype of var[i]'s type
 * - DEGREE_OVERFLOW if the substitution causes an overflow
 */

/* locking version */
EXPORTED term_t yices_subst_term(uint32_t n, term_t var[], term_t map[], term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_subst_term(n, var, map, t);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_subst_term(uint32_t n, term_t var[], term_t map[], term_t t) {
  error_report_t *error = get_yices_error();
  term_manager_t *manager = __yices_globals.manager;
  term_subst_t subst;
  term_t u;

  if (! check_good_term(manager, t) ||
      ! check_good_substitution(manager, n, var, map)) {
    return NULL_TERM;
  }

  init_term_subst(&subst, manager, n, var, map);
  u = apply_term_subst(&subst, t);
  delete_term_subst(&subst);

  if (u < 0) {
    if (u == -1) {
      // degree overflow
      error->code = DEGREE_OVERFLOW;
      error->badval = YICES_MAX_DEGREE + 1;
    } else {
      // BUG
      error->code = INTERNAL_EXCEPTION;
    }
    u = NULL_TERM;
  }

  return u;
}


/*
 * Variant: apply the substitution to m terms t[0 .. m-1]
 */

/* locking version */
EXPORTED int32_t yices_subst_term_array(uint32_t n, term_t var[], term_t map[], uint32_t m, term_t t[]) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_subst_term_array(n, var, map, m, t);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_subst_term_array(uint32_t n, term_t var[], term_t map[], uint32_t m, term_t t[]) {
  error_report_t *error = get_yices_error();
  term_manager_t *manager = __yices_globals.manager;
  term_subst_t subst;
  term_t u;
  uint32_t i;

  if (! check_good_terms(manager, m, t) ||
      ! check_good_substitution(manager, n, var, map)) {
    return -1;
  }

  init_term_subst(&subst, manager, n, var, map);
  for (i=0; i<m; i++) {
    u = apply_term_subst(&subst, t[i]);
    if (u < 0)  goto subst_error;
    t[i] = u;
  }
  delete_term_subst(&subst);

  return 0;

 subst_error:
  if (u == -1) {
    // degree overflow
    error->code = DEGREE_OVERFLOW;
    error->badval = YICES_MAX_DEGREE + 1;
  } else {
    // BUG
    error->code = INTERNAL_EXCEPTION;
  }
  delete_term_subst(&subst);

  return -1;
}



/**************
 *  PARSING   *
 *************/

/*
 * Parse s as a type expression in the Yices language.
 * Return NULL_TYPE if there's an error.
 */

/* locking version */
EXPORTED type_t yices_parse_type(const char *s) {
  yices_lock_t *lock = &__yices_globals.lock;
  type_t retval;

  get_yices_lock(lock);

  retval = _o_yices_parse_type(s);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
type_t _o_yices_parse_type(const char *s) {
  parser_t *p;

  p = get_parser(s);
  return parse_yices_type(p, NULL);
}


/*
 * Parse s as a term in the Yices language.
 * Return NULL_TERM if there's an error.
 */

/* locking version */
EXPORTED term_t yices_parse_term(const char *s) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_parse_term(s);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_parse_term(const char *s) {
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

/* locking version */
EXPORTED int32_t yices_set_type_name(type_t tau, const char *name) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_set_type_name(tau, name);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_set_type_name(type_t tau, const char *name) {
  char *clone;

  if (! check_good_type(__yices_globals.types, tau)) {
    return -1;
  }

  // make a copy of name
  clone = clone_string(name);
  set_type_name(__yices_globals.types, tau, clone);

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

/* locking version */
EXPORTED int32_t yices_set_term_name(term_t t, const char *name) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_set_term_name(t, name);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_set_term_name(term_t t, const char *name) {
  char *clone;

  if (! check_good_term(__yices_globals.manager, t)) {
    return -1;
  }

  // make a copy of name
  clone = clone_string(name);
  set_term_name(__yices_globals.terms, t, clone);

  return 0;
}


/*
 * Get name of type tau
 * - return NULL if tau has no name (or if tau is not a valid type)
 */

/* locking version */
EXPORTED const char *yices_get_type_name(type_t tau) {
  yices_lock_t *lock = &__yices_globals.lock;
  const char *retval;

  get_yices_lock(lock);

  retval = _o_yices_get_type_name(tau);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
const char *_o_yices_get_type_name(type_t tau) {
  if (! check_good_type(__yices_globals.types, tau)) {
    return NULL;
  }
  return type_name(__yices_globals.types, tau);
}


/*
 * Get name of term t
 * - return NULL is t has no name (or if t is not a valid term)
 */

/* locking version */
EXPORTED const char *yices_get_term_name(term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;
  const char *retval;

  get_yices_lock(lock);

  retval = _o_yices_get_term_name(t);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
const char *_o_yices_get_term_name(term_t t) {
  if (! check_good_term(__yices_globals.manager, t)) {
    return NULL;
  }
  return term_name(__yices_globals.terms, t);
}



/*
 * Remove name from the type table.
 */

/* locking version */
EXPORTED void yices_remove_type_name(const char *name) {
  yices_lock_t *lock = &__yices_globals.lock;

  get_yices_lock(lock);

  _o_yices_remove_type_name(name);

  release_yices_lock(lock);

}

/* non-locking version */
void _o_yices_remove_type_name(const char *name) {
  remove_type_name(__yices_globals.types, name);
}


/*
 * Remove name from the term table.
 */

/* locking version */
EXPORTED void yices_remove_term_name(const char *name) {
  yices_lock_t *lock = &__yices_globals.lock;

  get_yices_lock(lock);

  _o_yices_remove_term_name(name);

  release_yices_lock(lock);

}

/* non-locking version */
void _o_yices_remove_term_name(const char *name) {
  remove_term_name(__yices_globals.terms, name);
}


/*
 * Get type of the given name or return NULL_TYPE (-1)
 */

/* locking version */
EXPORTED type_t yices_get_type_by_name(const char *name) {
  yices_lock_t *lock = &__yices_globals.lock;
  type_t retval;

  get_yices_lock(lock);

  retval = _o_yices_get_type_by_name(name);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
type_t _o_yices_get_type_by_name(const char *name) {
  return get_type_by_name(__yices_globals.types, name);
}


/*
 * Get term of the given name or return NULL_TERM
 */

/* locking version */
EXPORTED term_t yices_get_term_by_name(const char *name) {
  yices_lock_t *lock = &__yices_globals.lock;
  term_t retval;

  get_yices_lock(lock);

  retval = _o_yices_get_term_by_name(name);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
term_t _o_yices_get_term_by_name(const char *name) {
  return get_term_by_name(__yices_globals.terms, name);
}


/*
 * Remove the name of type tau (if any)
 * Return -1 if tau is not a valid type and set the error code.
 * Return 0 otherwise.
 */

/* locking version */
EXPORTED int32_t yices_clear_type_name(type_t tau) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_clear_type_name(tau);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_clear_type_name(type_t tau) {
  if (! check_good_type(__yices_globals.types, tau)) {
    return -1;
  }

  clear_type_name(__yices_globals.types, tau);
  return 0;
}


/*
 * Remove the name of term t (if any)
 *
 * Return -1 if t is not a valid term (and set the error code)
 * Return 0 otherwise.
 */

/* locking version */
EXPORTED int32_t yices_clear_term_name(term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_clear_term_name(t);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_clear_term_name(term_t t) {
  if (! check_good_term(__yices_globals.manager, t)) {
    return -1;
  }

  clear_term_name(__yices_globals.terms, t);
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
  error_report_t *error = get_yices_error();
  int32_t k;
  int32_t retval;

  get_yices_lock(&(config->lock));

  k = config_set_field(config, name, value);
  if (k < 0) {
    if (k == -1) {
      // invalid name
      error->code = CTX_UNKNOWN_PARAMETER;
    } else {
      error->code = CTX_INVALID_PARAMETER_VALUE;
    }
    retval = -1;
  } else {
    retval = 0;
  }

  release_yices_lock(&(config->lock));

  return retval;
}


/*
 * Set config to a default solver combination for the given logic
 * - return -1 if there's an error
 * - return 0 otherwise
 */
EXPORTED int32_t yices_default_config_for_logic(ctx_config_t *config, const char *logic) {
  error_report_t *error = get_yices_error();
  int32_t k;
  int32_t retval;

  get_yices_lock(&(config->lock));

  k = config_set_logic(config, logic);
  if (k < 0) {
    if (k == -1) {
      error->code = CTX_UNKNOWN_LOGIC;
    } else {
      error->code = CTX_LOGIC_NOT_SUPPORTED;
    }
    retval = -1;
  } else {
    retval = 0;
  }

  release_yices_lock(&(config->lock));

  return retval;

}



/*******************************************
 *  SIMPLIFICATION/PREPROCESSING OPTIONS   *
 ******************************************/

/*
 * Parameters are identified by an integer in the following range
 */
typedef enum ctx_option {
  CTX_OPTION_VAR_ELIM,
  CTX_OPTION_BVARITH_ELIM,
  CTX_OPTION_FLATTEN,
} ctx_option_t;

#define NUM_CTX_OPTIONS (CTX_OPTION_FLATTEN+1)


/*
 * Option names in lexicographic order
 */
static const char * const ctx_option_names[NUM_CTX_OPTIONS] = {
  "bvarith-elim",
  "flatten",
  "var-elim",
};


/*
 * Corresponding index (cf. string_utils.h for parse_as_keyword)
 */
static const int32_t ctx_option_key[NUM_CTX_OPTIONS] = {
  CTX_OPTION_BVARITH_ELIM,
  CTX_OPTION_FLATTEN,
  CTX_OPTION_VAR_ELIM,
};


/*
 * Enable a specific option
 */

/* locking version */
EXPORTED int32_t yices_context_enable_option(context_t *ctx, const char *option) {
  yices_lock_t *lock = &(ctx->lock);
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_context_enable_option(ctx, option);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_context_enable_option(context_t *ctx, const char *option) {
  int32_t k, r;
  error_report_t *error = get_yices_error();

  r = 0; // default return code: no error
  k = parse_as_keyword(option, ctx_option_names, ctx_option_key, NUM_CTX_OPTIONS);
  switch (k) {
  case CTX_OPTION_VAR_ELIM:
    enable_variable_elimination(ctx);
    break;

  case CTX_OPTION_BVARITH_ELIM:
    enable_bvarith_elimination(ctx);
    break;

  case CTX_OPTION_FLATTEN:
    enable_diseq_and_or_flattening(ctx);
    break;

  default:
    assert(k == -1);
    // not recognized
    error->code = CTX_UNKNOWN_PARAMETER;
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
  error_report_t *error = get_yices_error();

  get_yices_lock(&(ctx->lock));

  r = 0; // default return code: no error
  k = parse_as_keyword(option, ctx_option_names, ctx_option_key, NUM_CTX_OPTIONS);
  switch (k) {
  case CTX_OPTION_VAR_ELIM:
    disable_variable_elimination(ctx);
    break;

  case CTX_OPTION_BVARITH_ELIM:
    enable_bvarith_elimination(ctx);
    break;

  case CTX_OPTION_FLATTEN:
    disable_diseq_and_or_flattening(ctx);
    break;

  default:
    assert(k == -1);
    // not recognized
    error->code = CTX_UNKNOWN_PARAMETER;
    r = -1;
    break;
  }

  release_yices_lock(&(ctx->lock));

  return r;
}


/*
 * For backward compatibility: functions to enable/disable one option
 */
EXPORTED void yices_enable_var_elim(context_t *ctx) {

  get_yices_lock(&(ctx->lock));

  enable_variable_elimination(ctx);

  release_yices_lock(&(ctx->lock));

}

EXPORTED void yices_disable_var_elim(context_t *ctx) {

  get_yices_lock(&(ctx->lock));

  disable_variable_elimination(ctx);

  release_yices_lock(&(ctx->lock));

}

EXPORTED void yices_enable_flattening(context_t *ctx) {

  get_yices_lock(&(ctx->lock));

  enable_diseq_and_or_flattening(ctx);

  release_yices_lock(&(ctx->lock));

}

EXPORTED void yices_disable_flattening(context_t *ctx) {

  get_yices_lock(&(ctx->lock));

  disable_diseq_and_or_flattening(ctx);

  release_yices_lock(&(ctx->lock));

}

EXPORTED void yices_enable_bvarith_elim(context_t *ctx) {

  get_yices_lock(&(ctx->lock));

  enable_bvarith_elimination(ctx);

  release_yices_lock(&(ctx->lock));

}

EXPORTED void yices_disable_bvarith_elim(context_t *ctx) {

  get_yices_lock(&(ctx->lock));

  disable_bvarith_elimination(ctx);

  release_yices_lock(&(ctx->lock));

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
  error_report_t *error = get_yices_error();
  int32_t k;
  int32_t retval;

  get_yices_lock(&(param->lock));


  k = params_set_field(param, name, value);
  if (k < 0) {
    if (k == -1) {
      error->code = CTX_UNKNOWN_PARAMETER;
    } else {
      error->code = CTX_INVALID_PARAMETER_VALUE;
    }
    retval =-1;
  } else {
    retval =  0;
  }

  release_yices_lock(&(param->lock));

  return retval;
}



/*************************
 *  CONTEXT OPERATIONS   *
 ************************/


/*
 * Set the default preprocessing options for a context
 * - arch = architecture
 * - iflag = true if integer solver is active
 * - qflag = true if quantifier support is required
 *
 * Note: these settings are based on benchmarking using the SMT-LIB 1.2
 * benchmarks (cf. yices_smtcomp.c)
 */
static void context_set_default_options(context_t *ctx, context_arch_t arch, bool iflag, bool qflag) {
  enable_variable_elimination(ctx);
  enable_bvarith_elimination(ctx);
  enable_diseq_and_or_flattening(ctx);

  // disable flattening for QF_BV (flattening may make things worse)
  if (arch == CTX_ARCH_BV) {
    disable_diseq_and_or_flattening(ctx);
  }
}


/*
 * Allocate and initialize a new context.
 * The configuration is specified by arch/mode/iflag/qflag.
 * - arch = architecture to use
 * - mode = which optional features are supported
 * - iflag = true to active the integer solver
 * - qflag = true to support quantifiers
 */
context_t *yices_create_context(context_arch_t arch, context_mode_t mode, bool iflag, bool qflag) {
  context_t *ctx;

  ctx = alloc_context();
  init_context(ctx, __yices_globals.terms, mode, arch, qflag);
  context_set_default_options(ctx, arch, iflag, qflag);

  return ctx;
}



/*
 * For backward compatibiltiy:
 * - use the following default configuration:
 *   mode = CTX_MODE_MULTICHECKS
 *   logic = QF_BV
 */
EXPORTED context_t *yices_new_context(void) {
  return yices_create_context(CTX_ARCH_BV, CTX_MODE_MULTICHECKS, false, false);
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

/* locking version */
EXPORTED smt_status_t yices_context_status(context_t *ctx) {
  yices_lock_t *lock = &(ctx->lock);
  smt_status_t retval;

  get_yices_lock(lock);

  retval = _o_yices_context_status(ctx);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
smt_status_t _o_yices_context_status(context_t *ctx) {
  smt_status_t retval;
  yices_lock_t *lock = &(ctx->lock);
  
  get_yices_lock(lock);
  
  retval = context_status(ctx);

  release_yices_lock(lock);

  return retval;
}


/*
 * Reset: remove all assertions and restore ctx's status to IDLE
 */

/* locking version */
EXPORTED  void yices_reset_context(context_t *ctx) {
  yices_lock_t *lock = &(ctx->lock);

  get_yices_lock(lock);

  _o_yices_reset_context(ctx);

  release_yices_lock(lock);

}

/* non-locking version */
void _o_yices_reset_context(context_t *ctx) {
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

/* locking version */
EXPORTED int32_t yices_push(context_t *ctx) {
  yices_lock_t *lock = &(ctx->lock);
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_push(ctx);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_push(context_t *ctx) {
  error_report_t *error = get_yices_error();

  if (! context_supports_pushpop(ctx)) {
    error->code = CTX_OPERATION_NOT_SUPPORTED;
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
    error->code = CTX_INVALID_OPERATION;
    return -1;
    
  case STATUS_ERROR:
  default:
    error->code = INTERNAL_EXCEPTION;
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

/* locking version */
EXPORTED int32_t yices_pop(context_t *ctx) {
  yices_lock_t *lock = &(ctx->lock);
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_pop(ctx);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_pop(context_t *ctx) {
  error_report_t *error = get_yices_error();

  if (! context_supports_pushpop(ctx)) {
    error->code = CTX_OPERATION_NOT_SUPPORTED;
    return -1;
  }

  if (context_base_level(ctx) == 0) {
    error->code = CTX_INVALID_OPERATION;
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
    error->code = CTX_INVALID_OPERATION;
    return -1;

  case STATUS_ERROR:
  default:
    error->code = INTERNAL_EXCEPTION;
    return -1;
  }

  context_pop(ctx);
  return 0;
}



/*
 * Convert an error code reported by assert_formula
 * into the corresponding yices_error value.
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
  CTX_LAMBDAS_NOT_SUPPORTED,
  CTX_FORMULA_NOT_IDL,
  CTX_FORMULA_NOT_RDL,
  CTX_NONLINEAR_ARITH_NOT_SUPPORTED,
  CTX_TOO_MANY_ARITH_VARS,
  CTX_TOO_MANY_ARITH_ATOMS,
  CTX_ARITH_SOLVER_EXCEPTION,
  CTX_BV_SOLVER_EXCEPTION,
};

static inline void convert_internalization_error(int32_t code) {
  error_report_t *error = get_yices_error();
  assert(-NUM_INTERNALIZATION_ERRORS < code && code < 0);
  error->code = intern_code2error[-code];
}


/*
 * Assert formula t in ctx
 * - ctx status must be IDLE or UNSAT or SAT or UNKNOWN
 * - t must be a boolean term
 *
 * If ctx's status is UNSAT, nothing is done.
 *
 * If ctx's status is IDLE, SAT, or UNKNOWN, then the formula is
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

/* locking version */
EXPORTED int32_t yices_assert_formula(context_t *ctx, term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;
  yices_lock_t *ctxlock = &(ctx->lock);
  int32_t retval;

  get_yices_lock(lock);

  get_yices_lock(ctxlock);

  retval = _o_yices_assert_formula(ctx, t);

  release_yices_lock(ctxlock);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_assert_formula(context_t *ctx, term_t t) {
  term_manager_t *manager = __yices_globals.manager;
  error_report_t *error = get_yices_error();
  int32_t code;

  if (! check_good_term(manager, t) ||
      ! check_boolean_term(manager, t)) {
    return -1;
  }

  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    if (! context_supports_multichecks(ctx)) {
      error->code = CTX_OPERATION_NOT_SUPPORTED;
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
    error->code = CTX_INVALID_OPERATION;
    return -1;

  case STATUS_ERROR:
  default:
    error->code = INTERNAL_EXCEPTION;
    return -1;
  }

  return 0;
}



/*
 * Same thing for an array of n formulas t[0 ... n-1]
 */

/* locking version */
EXPORTED int32_t yices_assert_formulas(context_t *ctx, uint32_t n, term_t t[]) {
  yices_lock_t *lock = &__yices_globals.lock;
  yices_lock_t *ctxlock = &(ctx->lock);
  int32_t retval;

  get_yices_lock(lock);

  get_yices_lock(ctxlock);


  retval = _o_yices_assert_formulas(ctx, n, t);

  release_yices_lock(ctxlock);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_assert_formulas(context_t *ctx, uint32_t n, term_t t[]) {
  term_manager_t *manager = __yices_globals.manager;
  error_report_t *error = get_yices_error();
  int32_t code;

  if (! check_good_terms(manager, n, t) ||
      ! check_boolean_args(manager, n, t)) {
    return -1;
  }

  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    if (! context_supports_multichecks(ctx)) {
      error->code = CTX_OPERATION_NOT_SUPPORTED;
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
    error->code = CTX_INVALID_OPERATION;
    return -1;

  case STATUS_ERROR:
  default:
    error->code = INTERNAL_EXCEPTION;
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

/* locking version */
EXPORTED int32_t yices_assert_blocking_clause(context_t *ctx) {
  yices_lock_t *lock = &(ctx->lock);
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_assert_blocking_clause(ctx);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_assert_blocking_clause(context_t *ctx) {
  error_report_t *error = get_yices_error();
  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    if (context_supports_multichecks(ctx)) {
      assert_blocking_clause(ctx);
      return 0;
    } else {
      error->code = CTX_OPERATION_NOT_SUPPORTED;
      return -1;
    }

  case STATUS_IDLE:
  case STATUS_UNSAT:
  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
    error->code = CTX_INVALID_OPERATION;
    return -1;

  case STATUS_ERROR:
  default:
    error->code = INTERNAL_EXCEPTION;
    return -1;
  }
}


/*
 * Set default search parameters for ctx (based on architecture and theories)
 * - this is based on benchmarking on the SMT-LIB 1.2 benchmarks (cf. yices_smtcomp.c)
 */

/* locking version */
EXPORTED void yices_set_default_params(context_t *ctx, param_t *params) {
  yices_lock_t *lock = &(params->lock);

  get_yices_lock(lock);

  _o_yices_set_default_params(ctx, params);

  release_yices_lock(lock);

}

/* non-locking version */
void _o_yices_set_default_params(context_t *ctx, param_t *params) {
  init_params_to_defaults(params);
  switch (ctx->arch) {
  case CTX_ARCH_BV:
    // QF_BV options: --var-elim --fast-restarts --randomness=0 --bvarith-elim
    params->fast_restart = true;
    params->c_factor = 1.1;
    params->d_factor = 1.1;
    params->randomness = 0.0;
    // EXPERIMENTAL: EVEN FASTER RESTARTS
    // this seems to help overall but it's not uniformly better
    // in particular, this makes yices slower on example/jinpeng.ys
    params->c_factor = 1.05;
    params->d_factor = 1.05;
    break;

  default:
    // nothing required
    break;
  }
}


/*
 * Check satisfiability: check whether the assertions stored in ctx
 * are satisfiable.
 * - params is an optional structure that stores heuristic parameters.
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

/* locking version */
EXPORTED smt_status_t yices_check_context(context_t *ctx, const param_t *params) {
  yices_lock_t *lock = &(ctx->lock);
  smt_status_t retval;

  get_yices_lock(lock);

  retval = _o_yices_check_context(ctx, params);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
smt_status_t _o_yices_check_context(context_t *ctx, const param_t *params) {
  error_report_t *error = get_yices_error();
  param_t default_params;
  smt_status_t stat;

  stat = context_status(ctx);
  switch (stat) {
  case STATUS_UNKNOWN:
  case STATUS_UNSAT:
  case STATUS_SAT:
    break;

  case STATUS_IDLE:
    if (params == NULL) {
      yices_set_default_params(ctx, &default_params);
      params = &default_params;
    }
    stat = check_context(ctx, params);
    if (stat == STATUS_INTERRUPTED && context_supports_cleaninterrupt(ctx)) {
      context_cleanup(ctx);
    }
    break;

  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
    error->code = CTX_INVALID_OPERATION;
    stat = STATUS_ERROR;
    break;

  case STATUS_ERROR:
  default:
    error->code = INTERNAL_EXCEPTION;
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
 *
 * N.B. Doesn't need to get the lock (presumably because it can't)
 *
 */
EXPORTED void yices_stop_search(context_t *ctx) {
  if (context_status(ctx) == STATUS_SEARCHING) {
    context_stop_search(ctx);
  }
}



/************
 *  MODELS  *
 ***********/

/*
 * Build a model from ctx
 * - keep_subst indicates whether the model should include
 *   the eliminated variables:
 *   keep_subst = 0 means don't keep substitutions,
 *   keep_subst != 0 means keep them
 * - ctx status must be SAT or UNKNOWN
 *
 * The function returns NULL if the status isn't SAT or UNKNOWN and
 * sets an error report.
 *
 */

/* locking version */
EXPORTED model_t *yices_get_model(context_t *ctx, int32_t keep_subst) {
  yices_lock_t *lock = &__yices_globals.lock;
  yices_lock_t *ctxlock = &(ctx->lock);
  model_t *retval;

  get_yices_lock(lock);

  get_yices_lock(ctxlock);

  retval = _o_yices_get_model(ctx, keep_subst);

  release_yices_lock(ctxlock);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
model_t *_o_yices_get_model(context_t *ctx, int32_t keep_subst) {
  error_report_t *error = get_yices_error();
  model_t *mdl;

  assert(ctx != NULL);

  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    mdl = alloc_model();
    init_model(mdl, __yices_globals.terms, (keep_subst != 0));
    context_build_model(mdl, ctx);
    break;

  default:
    error->code = CTX_INVALID_OPERATION;
    mdl = NULL;
    break;
  }

  return mdl;
}


/*
 * Delete mdl
 */
EXPORTED void yices_free_model(model_t *mdl) {
  delete_model(mdl);
  free_model(mdl);
}


/*
 * Print model mdl on FILE f
 * - f must be open/writable
 */

/* locking version */
EXPORTED void yices_print_model(FILE *f, model_t *mdl) {
  yices_lock_t *lock = &__yices_globals.lock;
  yices_lock_t *mdllock = &(mdl->lock);

  get_yices_lock(lock);

  get_yices_lock(mdllock);

  _o_yices_print_model(f, mdl);

  release_yices_lock(mdllock);

  release_yices_lock(lock);

}

/* non-locking version */
void _o_yices_print_model(FILE *f, model_t *mdl) {
  model_print_full(f, mdl);
}


/*
 * Pretty print mdl
 * - f = output file to use
 * - width, height, offset = print area
 */

/* locking version */
EXPORTED int32_t yices_pp_model(FILE *f, model_t *mdl, uint32_t width, uint32_t height, uint32_t offset) {
  yices_lock_t *lock = &__yices_globals.lock;
  yices_lock_t *mdllock = &(mdl->lock);
  int32_t retval;

  get_yices_lock(lock);

  get_yices_lock(mdllock);

  retval = _o_yices_pp_model(f, mdl, width, height, offset);

  release_yices_lock(mdllock);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_pp_model(FILE *f, model_t *mdl, uint32_t width, uint32_t height, uint32_t offset) {
  error_report_t *error = get_yices_error();
  yices_pp_t printer;
  pp_area_t area;
  int32_t code;

  if (width < 4) width = 4;
  if (height == 0) height = 1;

  area.width = width;
  area.height = height;
  area.offset = offset;
  area.stretch = false;
  area.truncate = true;

  init_default_yices_pp(&printer, f, &area);
  model_pp_full(&printer, mdl);
  flush_yices_pp(&printer);

  // check for error
  code = 0;
  if (yices_pp_print_failed(&printer)) {
    code = -1;
    errno = yices_pp_errno(&printer);
    error->code = OUTPUT_ERROR;
  }
  delete_yices_pp(&printer, false);

  return code;
}






/*
 * Convert a negative evaluation code v to
 * the corresponding yices error code.
 * - v is a code returned by eval_in_model
 */
#define NUM_EVAL_ERROR_CODES ((-MDL_EVAL_FAILED) + 1)

static const error_code_t eval_error2code[NUM_EVAL_ERROR_CODES] = {
  NO_ERROR,              // v = 0
  EVAL_FAILED,           // v = null_value (-1)
  INTERNAL_EXCEPTION,    // v = MDL_EVAL_INTERNAL_ERROR (-2)
  EVAL_UNKNOWN_TERM,     // v = MDL_EVAL_UNKNOWN_TERM (-3)
  EVAL_FREEVAR_IN_TERM,  // v = MDL_EVAL_FREEVAR_IN_TERM (4)
  EVAL_QUANTIFIER,       // v = MDL_EVAL_QUANTIFIER (-5)
  EVAL_LAMBDA,           // v = MDL_EVAL_LAMBDA (-6)
  EVAL_FAILED,           // v = MDL_EVAL_FAILED (-7)
};

static inline error_code_t yices_eval_error(value_t v) {
  assert(0 <= -v && -v <= NUM_EVAL_ERROR_CODES);
  return eval_error2code[-v];
}


/*
 * Value of boolean term t: returned as an integer val
 * - val = 0 means t is false in mdl
 * - val = 1 means t is true in mdl
 *
 * Error codes:
 * If t is not boolean
 *   code = TYPE_MISMATCH
 *   term1 = t
 *   type1 = bool (expected type)
 * + the other evaluation error codes above.
 */

/* locking version */
EXPORTED int32_t yices_get_bool_value(model_t *mdl, term_t t, int32_t *val) {
  yices_lock_t *lock = &__yices_globals.lock;
  yices_lock_t *mdllock = &(mdl->lock);
  int32_t retval;

  get_yices_lock(lock);
 
  get_yices_lock(mdllock);
 
  retval = _o_yices_get_bool_value(mdl, t, val);

  release_yices_lock(mdllock);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_get_bool_value(model_t *mdl, term_t t, int32_t *val) {
  error_report_t *error = get_yices_error();
  term_manager_t *manager = __yices_globals.manager;
  evaluator_t evaluator;
  value_table_t *vtbl;
  value_t v;

  if (! check_good_term(manager, t) ||
      ! check_boolean_term(manager, t)) {
    return -1;
  }

  v = model_find_term_value(mdl, t);
  if (v == null_value) {
    init_evaluator(&evaluator, mdl);
    v = eval_in_model(&evaluator, t);
    delete_evaluator(&evaluator);
  }

  if (v < 0) {
    error->code = yices_eval_error(v);
    return -1;
  }

  vtbl = model_get_vtbl(mdl);
  if (! object_is_boolean(vtbl, v)) {
    error->code = INTERNAL_EXCEPTION;
    return -1;
  }

  *val = boolobj_value(vtbl, v);

  return 0;
}


// same function under a different name for backward compatibility
EXPORTED int32_t yices_eval_bool_term_in_model(model_t *mdl, term_t t, int32_t *val) {
  return yices_get_bool_value(mdl, t, val);
}



/*
 * Value of bitvector term t in mdl
 * - the value is returned in array val
 * - val must be an integer array of sufficient size to store all bits of t
 * - bit i of t is stored in val[i] (val[i] is either 0 or 1)
 * - the value is returned using small-endian convention:
 *    val[0] is the low order bit
 *    ...
 *    val[n-1] is the high order bit
 *
 * If t is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 */

/* locking version */
EXPORTED int32_t yices_get_bv_value(model_t *mdl, term_t t, int32_t val[]) {
  yices_lock_t *lock = &__yices_globals.lock;
  yices_lock_t *mdllock = &(mdl->lock);
  int32_t retval;

  get_yices_lock(lock);

  get_yices_lock(mdllock);

  retval = _o_yices_get_bv_value(mdl, t, val);

  release_yices_lock(mdllock);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_get_bv_value(model_t *mdl, term_t t, int32_t val[]) {
  error_report_t *error = get_yices_error();
  term_manager_t *manager = __yices_globals.manager;
  evaluator_t evaluator;
  value_table_t *vtbl;
  value_bv_t *bv;
  value_t v;

  if (! check_good_term(manager, t) ||
      ! check_bitvector_term(manager, t)) {
    return -1;
  }

  v = model_find_term_value(mdl, t);
  if (v == null_value) {
    init_evaluator(&evaluator, mdl);
    v = eval_in_model(&evaluator, t);
    delete_evaluator(&evaluator);
  }

  if (v < 0) {
    error->code = yices_eval_error(v);
    return -1;
  }

  vtbl = model_get_vtbl(mdl);
  if (! object_is_bitvector(vtbl, v)) {
    error->code = INTERNAL_EXCEPTION;
    return -1;
  }

  bv = vtbl_bitvector(vtbl, v);
  bvconst_get_array(bv->data, val, bv->nbits);

  return 0;
}

// same function under a different name for backward compatibility
EXPORTED int32_t yices_eval_bv_term_in_model(model_t *mdl, term_t t, int32_t val[]) {
  return yices_get_bv_value(mdl, t, val);
}




/*************************
 *  GARBAGE COLLECTION   *
 ************************/

/*
 * Allocate and initialize the registry tables
 */
static sparse_array_t *_o_get_root_terms(void) {  //bruno: _o_ means the calling function needs to already have the lock.
  if (root_terms == NULL) {
    init_sparse_array(&the_root_terms, 0);
    root_terms = &the_root_terms;
  }
  return root_terms;
}

static sparse_array_t *_o_get_root_types(void) {
  if (root_types == NULL) {
    init_sparse_array(&the_root_types, 0);
    root_types = &the_root_types;
  }
  return root_types;
}


/*
 * Increment/decrement the reference counters
 */

/* locking version */
EXPORTED int32_t yices_incref_term(term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_incref_term(t);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_incref_term(term_t t) {
  sparse_array_t *roots;
  

  if (!check_good_term(__yices_globals.manager, t)) {
    return -1;
  }

  get_yices_lock(&root_lock);

  // we keep the ref count on the term index
  // (i.e., we ignore t's polarity)
  roots = _o_get_root_terms();
  sparse_array_incr(roots, index_of(t));

  release_yices_lock(&root_lock);
  
  return 0;
}

/* locking version */
EXPORTED int32_t yices_incref_type(type_t tau) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_incref_type(tau);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_incref_type(type_t tau) {
  sparse_array_t *roots;


  if (!check_good_type(__yices_globals.types, tau)) {
    return -1;
  }

  get_yices_lock(&root_lock);

  roots = _o_get_root_types();
  sparse_array_incr(roots, tau);

  release_yices_lock(&root_lock);

  return 0;
}

/* locking version */
EXPORTED int32_t yices_decref_term(term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_decref_term(t);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_decref_term(term_t t) {
  error_report_t *error = get_yices_error();
  int32_t retval = -1;


  if (!check_good_term(__yices_globals.manager, t)) {
    return retval;
  }

  get_yices_lock(&root_lock);

  if (root_terms == NULL ||
      sparse_array_read(root_terms, index_of(t)) == 0) {
    error->code = BAD_TERM_DECREF;
    error->term1 = t;
  } else {
    sparse_array_decr(root_terms, index_of(t));
    retval = 0;
  }
  
  release_yices_lock(&root_lock);
  
  return retval;
}

/* locking version */
EXPORTED int32_t yices_decref_type(type_t tau) {
  yices_lock_t *lock = &__yices_globals.lock;
  int32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_decref_type(tau);

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
int32_t _o_yices_decref_type(type_t tau) {
  error_report_t *error = get_yices_error();
  int32_t retval = -1;

  if (! check_good_type(__yices_globals.types, tau)) {
    return retval;
  }

  get_yices_lock(&root_lock);

  if (root_types == NULL ||
      sparse_array_read(root_types, tau) == 0) {
    error->code = BAD_TYPE_DECREF;
    error->type1 = tau;
  } else {
    sparse_array_decr(root_types, tau);
    retval = 0;
  }

  release_yices_lock(&root_lock);

  return retval;
}


/*
 * Number of live terms and types
 */

/* locking version */
EXPORTED uint32_t yices_num_terms(void) {
  yices_lock_t *lock = &__yices_globals.lock;
  uint32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_num_terms();

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
uint32_t _o_yices_num_terms(void) {
  return __yices_globals.terms->live_terms;
}

/* locking version */
EXPORTED uint32_t yices_num_types(void) {
  yices_lock_t *lock = &__yices_globals.lock;
  uint32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_num_types();

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
uint32_t _o_yices_num_types(void) {
  return __yices_globals.types->live_types;
}


/*
 * Number of terms/types with a positive reference count
 */

/* locking version */
EXPORTED uint32_t yices_num_posref_terms(void) {
  yices_lock_t *lock = &__yices_globals.lock;
  uint32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_num_posref_terms();

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
uint32_t _o_yices_num_posref_terms(void) {
  uint32_t n;

  get_yices_lock(&root_lock);

  n = 0;
  if (root_terms != NULL) {
    n = root_terms->nelems;
  }

  release_yices_lock(&root_lock);

  return n;
}

/* locking version */
EXPORTED uint32_t yices_num_posref_types(void) {
  yices_lock_t *lock = &__yices_globals.lock;
  uint32_t retval;

  get_yices_lock(lock);

  retval = _o_yices_num_posref_types();

  release_yices_lock(lock);

  return retval;
}

/* non-locking version */
uint32_t _o_yices_num_posref_types(void) {
  uint32_t n;

  get_yices_lock(&root_lock);

  n = 0;
  if (root_types != NULL) {
    n = root_types->nelems;
  }

  release_yices_lock(&root_lock);

  return n;
}



/*
 * GC: mark roots
 */

// iterator for the root_terms array
static void term_idx_marker(void *aux, uint32_t i) {
  assert(aux == __yices_globals.terms);
  if (good_term_idx(aux, i)) {
    term_table_set_gc_mark(aux, i);
  }
}

// iterator for the root_types array
static void type_marker(void *aux, uint32_t i) {
  assert(aux == __yices_globals.types);
  if (good_type(aux, i)) {
    type_table_set_gc_mark(aux, i);
  }
}

// scan the list of contexts and mark
static void context_list_gc_mark(void) {
  dl_list_t *elem;

  get_yices_lock(&context_lock);


  elem = context_list.next;
  while (elem != &context_list) {
    context_gc_mark(context_of_header(elem));
    elem = elem->next;
  }
 
  release_yices_lock(&context_lock);

}

// scan the list of models and call the mark procedure
static void model_list_gc_mark(void) {
  dl_list_t *elem;

  get_yices_lock(&model_lock);

  elem = model_list.next;
  while (elem != &model_list) {
    model_gc_mark(model_of_header(elem));
    elem = elem->next;
  }

  release_yices_lock(&model_lock);

}

// mark all terms in array a, n = size of a
static void mark_term_array(term_table_t *tbl, term_t *a, uint32_t n) {
  uint32_t i;
  int32_t idx;

  for (i=0; i<n; i++) {
    idx = index_of(a[i]);
    if (good_term_idx(tbl, idx)) {
      term_table_set_gc_mark(tbl, idx);
    }
  }
}

// mark all types in array a
static void mark_type_array(type_table_t *tbl, type_t *a, uint32_t n) {
  uint32_t i;
  type_t tau;

  for (i=0; i<n; i++) {
    tau = a[i];
    if (good_type(tbl, tau)) {
      type_table_set_gc_mark(tbl, tau);
    }
  }
}


/*
 * Call the garbage collector
 * - t = optional array of terms
 * - nt = size of t
 * - tau = optional array of types
 * - ntau = size of tau
 * - keep_named specifies whether the named terms and types should
 *   all be presered
 */

/* locking version */
EXPORTED void yices_garbage_collect(term_t *t, uint32_t nt,
				    type_t *tau, uint32_t ntau,
				    int32_t keep_named) {
  yices_lock_t *lock = &__yices_globals.lock;

  get_yices_lock(lock);

  _o_yices_garbage_collect(t, nt, tau, ntau, keep_named);

  release_yices_lock(lock);

}

/* non-locking version */
void _o_yices_garbage_collect(term_t *t, uint32_t nt,
                              type_t *tau, uint32_t ntau,
                              int32_t keep_named) {
  bool keep;
  term_table_t *terms = __yices_globals.terms;
  type_table_t *types = __yices_globals.types;


  /*
   * Default roots: all terms and types in all live models and context
   */
  context_list_gc_mark();
  model_list_gc_mark();

  /*
   * Add roots if t and tau
   */
  if (t != NULL) mark_term_array(terms, t, nt);
  if (tau != NULL) mark_type_array(types, tau, ntau);

  get_yices_lock(&root_lock);

  /*
   * Roots from the reference counting
   */
  if (root_terms != NULL) {
    sparse_array_iterate(root_terms, terms, term_idx_marker);
  }
  if (root_types != NULL) {
    sparse_array_iterate(root_types, types, type_marker);
  }

  release_yices_lock(&root_lock);

  /*
   * Call the garbage collector
   */
  keep = (keep_named != 0);
  term_table_gc(terms, keep);


}
