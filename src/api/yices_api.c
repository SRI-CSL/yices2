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
 * YICES API
 */

/*
 * This module implements the API defined in yices.h.
 *
 * It also implements the functions defined in yices_extensions.h, yices_api_lock_free.h and
 * yices_iterators.h
 */


/*
 * Visibility control: all extern functions declared here are in libyices's API
 * Other extern functions should have visibility=hidden (cf. Makefile).
 *
 * On cygwin/mingw, we have two cases:
 * - static build: NOYICES_DLL is defined.
 * - dynamic build: NOYICES_DLL is not defined.
 *
 * We don't want the attribute __declspec(dllexport) when NOYICES_DLL is defined
 * otherwise clang gives compilation warnings
 */
#if defined(CYGWIN) || defined(MINGW)
// Windows build
#if defined(NOYICES_DLL)
#define EXPORTED
#else
#define EXPORTED __declspec(dllexport)
#define __YICES_DLLSPEC__ EXPORTED
#endif
#else
// Not Windows
#define EXPORTED __attribute__((visibility("default")))
#endif

#include <assert.h>
#include <stddef.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>

#include "api/context_config.h"
#include "api/search_parameters.h"
#include "api/smt_logic_codes.h"
#include "api/yices_error.h"
#include "api/yices_error_report.h"
#include "api/yices_api_lock_free.h"
#include "api/yices_extensions.h"
#include "api/yices_globals.h"
#include "api/yices_iterators.h"
#include "api/yval.h"

#include "context/context.h"

#include "frontend/yices/yices_parser.h"

#include "io/model_printer.h"
#include "io/term_printer.h"
#include "io/type_printer.h"
#include "io/yices_pp.h"

#include "model/generalization.h"
#include "model/literal_collector.h"
#include "model/map_to_model.h"
#include "model/model_queries.h"
#include "model/models.h"
#include "model/val_to_term.h"

#include "solvers/cdcl/delegate.h"

#include "terms/bv64_constants.h"
#include "terms/bvarith64_buffer_terms.h"
#include "terms/bvarith_buffer_terms.h"
#include "terms/rba_buffer_terms.h"
#include "terms/term_explorer.h"
#include "terms/term_manager.h"
#include "terms/term_substitution.h"
#include "terms/term_utils.h"
#include "terms/types.h"

#include "utils/dl_lists.h"
#include "utils/int_array_sort.h"
#include "utils/refcount_strings.h"
#include "utils/sparse_arrays.h"
#include "utils/string_utils.h"

#ifdef HAVE_MCSAT
#include <poly/algebraic_number.h>
#else
// We need a definition for (lp_algebraic_number_t *)
typedef void lp_algebraic_number_t;
#endif


#include "mt/thread_macros.h"
#include "mt/yices_thread_local.h"


#include "yices.h"


/****************************
 *  GLOBAL DATA STRUCTURES  *
 ***************************/


// rational for building terms: protected by ownership of global lock.
static YICES_PTS_LOCAL rational_t r0;

// buffer for building bitvector constants: protected by ownership of global lock.
static YICES_PTS_LOCAL bvconstant_t bv0;

/*
 * Initial sizes of the type and term tables.
 */
#define INIT_TYPE_SIZE  16
#define INIT_TERM_SIZE  64

/*
 * Global table. The actual initialization is done in yices_init() and
 * init_globals().
 */
YICES_PTS_LOCAL yices_globals_t __yices_globals = {
};


  
/*
 * SYNCHRONIZING ACCESS TO GLOBAL TABLE.
 */

/*
 * Attempt to obtain sole access to yices' global data structures.
 * In thread safe mode, calling this function will block all other
 * yices API routines from accessing the global data structures.
 *
 * It is an error to call this more than once.
 */
int32_t yices_obtain_mutex(void){
#ifdef THREAD_SAFE
  return get_yices_lock(&__yices_globals.lock);
#else
  return 0;
#endif
}

/*
 * Release the claim to sole access to yices' global data structures.
 *
 * The callee must have already obtained sole access via yices_obtain_mutex();
 */
int32_t yices_release_mutex(void){
#ifdef THREAD_SAFE
  return release_yices_lock(&__yices_globals.lock);
#else
  return 0;
#endif
}




/*
 * Registry tables for root terms and types (for garbage collection).
 * - the two tables are statically allocated but initialized only
 *   when needed.
 * - we keep pointers to the tables:
 *   Initially, we set root_terms = NULL and root_types = NULL
 *   On the first call to register a term or type, we initialize the
 *   static tables and update root_terms/root_types to point to it
 *
 * - In the thread safe version they are protected by the __yices_globals.lock
 *
 */
static YICES_PTS_LOCAL sparse_array_t *root_terms;
static YICES_PTS_LOCAL sparse_array_t *root_types;

static YICES_PTS_LOCAL sparse_array_t the_root_terms;
static YICES_PTS_LOCAL sparse_array_t the_root_types;



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
 * BD says: move into globals
 */
typedef struct {
  dl_list_t header;
  rba_buffer_t buffer;
} arith_buffer_elem_t;

static YICES_PTS_LOCAL dl_list_t arith_buffer_list;
#ifdef THREAD_SAFE
static YICES_PTS_LOCAL yices_lock_t arith_buffer_list_lock;
#endif

/*
 * Doubly-linked list of bitvector arithmetic buffers
 * BD says: move into globals
 */
typedef struct {
  dl_list_t header;
  bvarith_buffer_t buffer;
} bvarith_buffer_elem_t;

static YICES_PTS_LOCAL dl_list_t bvarith_buffer_list;
#ifdef THREAD_SAFE
static YICES_PTS_LOCAL yices_lock_t bvarith_buffer_list_lock;
#endif


/*
 * Variant: 64bit buffers
 * BD says: move into globals
 */
typedef struct {
  dl_list_t header;
  bvarith64_buffer_t buffer;
} bvarith64_buffer_elem_t;

static YICES_PTS_LOCAL dl_list_t bvarith64_buffer_list;
#ifdef THREAD_SAFE
static YICES_PTS_LOCAL yices_lock_t bvarith64_buffer_list_lock;
#endif


/*
 * Doubly-linked list of bitvector buffers
 * BD says: move into globals
 */
typedef struct {
  dl_list_t header;
  bvlogic_buffer_t buffer;
} bvlogic_buffer_elem_t;

static YICES_PTS_LOCAL dl_list_t bvlogic_buffer_list;
#ifdef THREAD_SAFE
static YICES_PTS_LOCAL yices_lock_t bvlogic_buffer_list_lock;
#endif


/*
 * Doubly-linked list of contexts
 * BD says: move into globals
 */
typedef struct {
  dl_list_t header;
  context_t context;
} context_elem_t;

static YICES_PTS_LOCAL dl_list_t context_list;
#ifdef THREAD_SAFE
static YICES_PTS_LOCAL yices_lock_t context_list_lock;
#endif


/*
 * Models
 * BD says: move into globals
 */
typedef struct {
  dl_list_t header;
  model_t model;
} model_elem_t;

static YICES_PTS_LOCAL dl_list_t model_list;
#ifdef THREAD_SAFE
static YICES_PTS_LOCAL yices_lock_t model_list_lock;
#endif


/*
 * Context configuration and parameter descriptors
 * are stored in one list.
 * Context configurations
 * BD says: move into globals
 */
typedef struct {
  dl_list_t header;
  ctx_config_t config;
} ctx_config_elem_t;

static YICES_PTS_LOCAL dl_list_t config_list;
#ifdef THREAD_SAFE
static YICES_PTS_LOCAL yices_lock_t config_list_lock;
#endif

/*
 * Solver parameter descriptors
 * BD says: move into globals
 */
typedef struct {
  dl_list_t header;
  param_t param;
} param_structure_elem_t;

static YICES_PTS_LOCAL dl_list_t parameter_list;
#ifdef THREAD_SAFE
static YICES_PTS_LOCAL yices_lock_t parameter_list_lock;
#endif


static inline void init_list_locks(void){
#ifdef THREAD_SAFE
  create_yices_lock(&arith_buffer_list_lock);
  create_yices_lock(&bvarith_buffer_list_lock);
  create_yices_lock(&bvarith64_buffer_list_lock);
  create_yices_lock(&bvlogic_buffer_list_lock);
  create_yices_lock(&context_list_lock);
  create_yices_lock(&model_list_lock);
  create_yices_lock(&generic_list_lock);
#endif
}

static inline void delete_list_locks(void){
#ifdef THREAD_SAFE
  destroy_yices_lock(&arith_buffer_list_lock);
  destroy_yices_lock(&bvarith_buffer_list_lock);
  destroy_yices_lock(&bvarith64_buffer_list_lock);
  destroy_yices_lock(&bvlogic_buffer_list_lock);
  destroy_yices_lock(&context_list_lock);
  destroy_yices_lock(&model_list_lock);
  destroy_yices_lock(&generic_list_lock);
#endif
}

/* the garbage collector must get all the locks */
static inline void get_list_locks(void){
#ifdef THREAD_SAFE
  get_yices_lock(&arith_buffer_list_lock);
  get_yices_lock(&bvarith_buffer_list_lock);
  get_yices_lock(&bvarith64_buffer_list_lock);
  get_yices_lock(&bvlogic_buffer_list_lock);
  get_yices_lock(&context_list_lock);
  get_yices_lock(&model_list_lock);
  get_yices_lock(&generic_list_lock);
#endif
}

/* the garbage collector must also release all the locks */
static inline void release_list_locks(void){
#ifdef THREAD_SAFE
  release_yices_lock(&arith_buffer_list_lock);
  release_yices_lock(&bvarith_buffer_list_lock);
  release_yices_lock(&bvarith64_buffer_list_lock);
  release_yices_lock(&bvlogic_buffer_list_lock);
  release_yices_lock(&context_list_lock);
  release_yices_lock(&model_list_lock);
  release_yices_lock(&generic_list_lock);
#endif
}




/**********************************
 *  ARITHMETIC-BUFFER ALLOCATION  *
 *********************************/

/*
 * Get header of buffer b, assuming b is embedded into an arith_buffer_elem
 */
static inline dl_list_t *arith_buffer_header(rba_buffer_t *b) {
  return (dl_list_t *)(((char *)b) - offsetof(arith_buffer_elem_t, buffer));
}

/*
 * Get buffer of header l
 */
static inline rba_buffer_t *arith_buffer(dl_list_t *l) {
  return (rba_buffer_t *)(((char *) l) + offsetof(arith_buffer_elem_t, buffer));
}

/*
 * Allocate an arithmetic buffer and insert it into the list
 */
static inline rba_buffer_t *alloc_arith_buffer(void) {
  arith_buffer_elem_t *new_elem;

  new_elem = (arith_buffer_elem_t *) safe_malloc(sizeof(arith_buffer_elem_t));
  MT_PROTECT_VOID(arith_buffer_list_lock, list_insert_next(&arith_buffer_list, &new_elem->header));
  return &new_elem->buffer;
}

/*
 * Remove b from the list and free b
 */
static inline void _o_free_arith_buffer(rba_buffer_t *b) {
  dl_list_t *elem;

  elem = arith_buffer_header(b);
  list_remove(elem);
  safe_free(elem);
}
static void free_arith_buffer(rba_buffer_t *b) {  //BD could this be inline?
  MT_PROTECT_VOID(arith_buffer_list_lock, _o_free_arith_buffer(b));
}

/*
 * Clean up the arith buffer list: free all elements and empty the list
 */
static void _o_free_arith_buffer_list(void) {
  dl_list_t *elem, *aux;

  elem = arith_buffer_list.next;
  while (elem != &arith_buffer_list) {
    aux = elem->next;
    delete_rba_buffer(arith_buffer(elem));
    safe_free(elem);
    elem = aux;
  }

  clear_list(&arith_buffer_list);
}
static void free_arith_buffer_list(void) {
  MT_PROTECT_VOID(arith_buffer_list_lock, _o_free_arith_buffer_list());
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
static inline bvarith_buffer_t *_o_alloc_bvarith_buffer(void) {
  bvarith_buffer_elem_t *new_elem;

  new_elem = (bvarith_buffer_elem_t *) safe_malloc(sizeof(bvarith_buffer_elem_t));
  list_insert_next(&bvarith_buffer_list, &new_elem->header);
  return &new_elem->buffer;
}

static bvarith_buffer_t *alloc_bvarith_buffer(void) {
  MT_PROTECT(bvarith_buffer_t *, bvarith_buffer_list_lock, _o_alloc_bvarith_buffer());
}

/*
 * Remove b from the list and free b
 */
static inline void _o_free_bvarith_buffer(bvarith_buffer_t *b) {
  dl_list_t *elem;

  elem = bvarith_buffer_header(b);
  list_remove(elem);
  safe_free(elem);
}

static void free_bvarith_buffer(bvarith_buffer_t *b) {
  MT_PROTECT_VOID(bvarith_buffer_list_lock, _o_free_bvarith_buffer(b));
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
static inline bvarith64_buffer_t *_o_alloc_bvarith64_buffer(void) {
  bvarith64_buffer_elem_t *new_elem;

  new_elem = (bvarith64_buffer_elem_t *) safe_malloc(sizeof(bvarith64_buffer_elem_t));
  list_insert_next(&bvarith64_buffer_list, &new_elem->header);
  return &new_elem->buffer;
}

static bvarith64_buffer_t *alloc_bvarith64_buffer(void) {
  MT_PROTECT(bvarith64_buffer_t *, bvarith64_buffer_list_lock, _o_alloc_bvarith64_buffer());
}

/*
 * Remove b from the list and free b
 */
static inline void _o_free_bvarith64_buffer(bvarith64_buffer_t *b) {
  dl_list_t *elem;

  elem = bvarith64_buffer_header(b);
  list_remove(elem);
  safe_free(elem);
}

static void free_bvarith64_buffer(bvarith64_buffer_t *b) {
  MT_PROTECT_VOID(bvarith64_buffer_list_lock, _o_free_bvarith64_buffer(b));
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
static inline bvlogic_buffer_t *_o_alloc_bvlogic_buffer(void) {
  bvlogic_buffer_elem_t *new_elem;

  new_elem = (bvlogic_buffer_elem_t *) safe_malloc(sizeof(bvlogic_buffer_elem_t));
  list_insert_next(&bvlogic_buffer_list, &new_elem->header);
  return &new_elem->buffer;
}

static bvlogic_buffer_t *alloc_bvlogic_buffer(void) {
  MT_PROTECT(bvlogic_buffer_t *, bvlogic_buffer_list_lock, _o_alloc_bvlogic_buffer());
}

/*
 * Remove b from the list and free b
 */
static inline void _o_free_bvlogic_buffer(bvlogic_buffer_t *b) {
  dl_list_t *elem;

  elem = bvlogic_buffer_header(b);
  list_remove(elem);
  safe_free(elem);
}

static void free_bvlogic_buffer(bvlogic_buffer_t *b) {
  MT_PROTECT_VOID(bvlogic_buffer_list_lock, _o_free_bvlogic_buffer(b));
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
static inline context_t *_o_alloc_context(void) {
  context_elem_t *new_elem;

  new_elem = (context_elem_t *) safe_malloc(sizeof(context_elem_t));
  list_insert_next(&context_list, &new_elem->header);
  return &new_elem->context;
}

static context_t *alloc_context(void) {
  MT_PROTECT(context_t *, context_list_lock, _o_alloc_context());
}


/*
 * Remove c from the list and free c
 * - WARNING: make sure to call delete_context(c) before this
 *   function
 */
static inline void _o_free_context(context_t *c) {
  dl_list_t *elem;

  elem = header_of_context(c);
  list_remove(elem);
  safe_free(elem);
}

static void free_context(context_t *c) {
  MT_PROTECT_VOID(context_list_lock, _o_free_context(c));
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
static inline model_t *_o_alloc_model(void) {
  model_elem_t *new_elem;

  new_elem = (model_elem_t *) safe_malloc(sizeof(model_elem_t));
  list_insert_next(&model_list, &new_elem->header);
  return &new_elem->model;
}

static model_t *alloc_model(void) {
  MT_PROTECT(model_t *, model_list_lock, _o_alloc_model());
}


/*
 * Remove c from the list and free m
 * - WARNING: make sure to call delete_model(c) before this
 *   function
 */
static inline void _o_free_model(model_t *m) {
  dl_list_t *elem;

  elem = header_of_model(m);
  list_remove(elem);
  safe_free(elem);
}
static inline void free_model(model_t *m) {
  MT_PROTECT_VOID(model_list_lock, _o_free_model(m));
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
 * Allocate a structure and insert it into the generic
 * WARNING: the record is not initialized
 */
static inline ctx_config_t *_o_alloc_config_structure(void) {
  ctx_config_elem_t *new_elem;

  new_elem = (ctx_config_elem_t *) safe_malloc(sizeof(ctx_config_elem_t));
  list_insert_next(&generic_list, &new_elem->header);
  return &new_elem->config;
}

static ctx_config_t *alloc_config_structure(void) {
  MT_PROTECT(ctx_config_t *, generic_list_lock, _o_alloc_config_structure());
}

static inline param_t *_o_alloc_param_structure(void) {
  param_structure_elem_t *new_elem;

  new_elem = (param_structure_elem_t *) safe_malloc(sizeof(param_structure_elem_t));
  list_insert_next(&generic_list, &new_elem->header);
  return &new_elem->param;
}

static param_t *alloc_param_structure(void) {
  MT_PROTECT(param_t *, generic_list_lock,  _o_alloc_param_structure());
}

/*
 * Remove a structure form the generic list
 */
static inline void _o_free_config_structure(ctx_config_t *c) {
  dl_list_t *elem;

  elem = header_of_config_structure(c);
  list_remove(elem);
  safe_free(elem);
}

static void free_config_structure(ctx_config_t *c) {
  MT_PROTECT_VOID(generic_list_lock, _o_free_config_structure(c));
}

static inline void _o_free_param_structure(param_t *p) {
  dl_list_t *elem;

  elem = header_of_param_structure(p);
  list_remove(elem);
  safe_free(elem);
}

static void free_param_structure(param_t *p) {
  MT_PROTECT_VOID(generic_list_lock, _o_free_param_structure(p));
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


/************************
 *  VARIABLE COLLECTOR  *
 ***********************/

/*
 * Return the free variable collector
 * - allocate and initialize it if necessary
 */
static fvar_collector_t *get_fvars(void) {
  if (__yices_globals.fvars == NULL) {
    __yices_globals.fvars = (fvar_collector_t *) safe_malloc(sizeof(fvar_collector_t));
    init_fvar_collector(__yices_globals.fvars, __yices_globals.terms);
  }

  return __yices_globals.fvars;
}


/*
 * Delete the free variable collector if it exists
 */
static void delete_fvars(void) {
  if (__yices_globals.fvars != NULL) {
    delete_fvar_collector(__yices_globals.fvars);
    safe_free(__yices_globals.fvars);
    __yices_globals.fvars = NULL;
  }
}



/***************************************
 *  GLOBAL INITIALIZATION AND CLEANUP  *
 **************************************/

/*
 * Initialize the table of global objects
 */
static void init_globals(yices_globals_t *glob) {
  type_table_t *types = (type_table_t *)safe_malloc(sizeof(type_table_t));
  term_table_t *terms = (term_table_t *)safe_malloc(sizeof(term_table_t));
  term_manager_t *manager = (term_manager_t *)safe_malloc(sizeof(term_manager_t));
  pprod_table_t *pprods = (pprod_table_t *)safe_malloc(sizeof(pprod_table_t));

  memset(types, 0, sizeof(type_table_t));
  memset(terms, 0, sizeof(term_table_t));
  memset(manager, 0, sizeof(term_manager_t));
  memset(pprods, 0, sizeof(pprod_table_t));

  glob->types = types;
  glob->terms = terms;
  glob->manager = manager;
  glob->pprods = pprods;

  glob->parser = NULL;
  glob->lexer = NULL;
  glob->tstack = NULL;
  glob->fvars = NULL;

#ifdef THREAD_SAFE
  create_yices_lock(&(glob->lock));
#endif

}


/*
 * Reset all to NULL
 */
static void clear_globals(yices_globals_t *glob) {
  safe_free(glob->types);
  safe_free(glob->terms);
  safe_free(glob->manager);
  safe_free(glob->pprods);

  glob->types = NULL;
  glob->terms = NULL;
  glob->manager = NULL;

#ifdef THREAD_SAFE
  destroy_yices_lock(&(glob->lock));
#endif

}


/*
 * Initialize all global objects
 */

EXPORTED void yices_global_init(void){
  init_yices_pp_tables();
}

EXPORTED void yices_per_thread_init(void){
  error_report_t *error;
  // setup the TLS and error report structure
  init_yices_error();
  error = get_yices_error();
  error->code = NO_ERROR;

  // prepare the global table
  init_globals(&__yices_globals);

  // make the global list locks
  init_list_locks();

 init_bvconstants();
  init_rationals();

  q_init(&r0);
  init_bvconstant(&bv0);

  // tables
  init_type_table(__yices_globals.types, INIT_TYPE_SIZE);
  init_pprod_table(__yices_globals.pprods, 0);
  init_term_table(__yices_globals.terms, INIT_TERM_SIZE, __yices_globals.types, __yices_globals.pprods);
  init_term_manager(__yices_globals.manager, __yices_globals.terms);

  // buffer lists
  clear_list(&arith_buffer_list);
  clear_list(&bvarith_buffer_list);
  clear_list(&bvarith64_buffer_list);
  clear_list(&bvlogic_buffer_list);

  // other dynamic object lists
  clear_list(&context_list);
  clear_list(&model_list);
  clear_list(&generic_list);

  // registries for garbage collection
  root_terms = NULL;
  root_types = NULL;
}


EXPORTED void yices_init(void) {
  yices_global_init();
  yices_per_thread_init();
}


/*
 * Cleanup: delete all tables and internal data structures
 */

EXPORTED void yices_global_exit(void){
  // nothing here yet
}

EXPORTED void yices_per_thread_exit(void){
  // registries
  if (root_terms != NULL) {
    assert(root_terms == &the_root_terms);
    delete_sparse_array(&the_root_terms);
  }
  if (root_types != NULL) {
    assert(root_types == &the_root_types);
    delete_sparse_array(&the_root_types);
  }

  delete_parsing_objects();
  delete_fvars();

  delete_term_manager(__yices_globals.manager);
  delete_term_table(__yices_globals.terms);
  delete_pprod_table(__yices_globals.pprods);
  delete_type_table(__yices_globals.types);

  clear_globals(&__yices_globals);

  free_bvlogic_buffer_list();
  free_bvarith_buffer_list();
  free_bvarith64_buffer_list();
  free_arith_buffer_list();

  free_context_list();
  free_model_list();
  free_generic_list();

  delete_list_locks();

  q_clear(&r0);
  delete_bvconstant(&bv0);

  cleanup_rationals();
  cleanup_bvconstants();

  free_yices_error();
}


EXPORTED void yices_exit(void) {
  yices_per_thread_exit();
  yices_global_exit();
}

/*
 * Full reset: delete everything
 */
EXPORTED void yices_reset(void) {
  yices_exit();
  yices_init();
}


/**********************************
 *  ERRORS AND FILE IO UTILITIES  *
 *********************************/

/*
 * Open a stream for output file fd
 * - fd = file descriptor
 * - return NULL if something goes wrong
 */
static FILE *fd_2_tmp_fp(int fd) {
  int tmp_fd;

  tmp_fd = dup(fd);
  if (tmp_fd < 0) {
    return NULL;
  }
  return fdopen(tmp_fd, "a");
}


/*
 * Get the last error report
 */
EXPORTED error_report_t *yices_error_report(void) {
  return get_yices_error();
}


/*
 * Get the last error code
 */
EXPORTED error_code_t yices_error_code(void) {
  error_report_t *error = get_yices_error();
  return error->code;
}


/*
 * Set an error code. Leave other fields unchanged
 */
static void set_error_code(error_code_t code) {
  error_report_t *error = get_yices_error();
  error->code = code;
}

/*
 * Clear the last error report
 */
EXPORTED void yices_clear_error(void) {
  set_error_code(NO_ERROR);
}


/*
 * Record that a file io operation failed
 * set the error_code to OUTPUT_ERROR
 */
static inline void file_output_error(void) {
  set_error_code(OUTPUT_ERROR);
}


/*
 * Print an errormessage on f
 */
EXPORTED int32_t yices_print_error(FILE *f) {
  return print_error(f);
}

EXPORTED int32_t yices_print_error_fd(int fd) {
  FILE *tmp_fp;
  int32_t retval;

  tmp_fp = fd_2_tmp_fp(fd);
  if (tmp_fp == NULL) {
    file_output_error();
    return -1;
  }
  retval = print_error(tmp_fp);
  fclose(tmp_fp);

  return retval;
}


/*
 * Build an error string
 */
EXPORTED char *yices_error_string(void) {
  return error_string();
}


/*
 * Reset the internal term/types/pprod tables
 */
void yices_reset_tables(void) {
  reset_term_manager(__yices_globals.manager);
  reset_term_table(__yices_globals.terms);
  reset_pprod_table(__yices_globals.pprods);
  reset_type_table(__yices_globals.types);
}


/*
 * Install a call back function that will be invoked
 * if Yices runs out of memory.
 * - if this callback returns, the process is killed
 */
static void _o_yices_set_out_of_mem_callback(void (*callback)(void)) {
  __out_of_mem_callback = callback;
}

EXPORTED void yices_set_out_of_mem_callback(void (*callback)(void)) {
  MT_PROTECT_VOID(__yices_globals.lock,_o_yices_set_out_of_mem_callback(callback));
}


/*
 * Test support for MCSAT
 */
#if HAVE_MCSAT
EXPORTED int32_t yices_has_mcsat(void) {
  return 1;
}
#else
EXPORTED int32_t yices_has_mcsat(void) {
  return 0;
}
#endif

/*
 * Test for thread safety.
 */
#ifdef THREAD_SAFE
EXPORTED int32_t yices_is_thread_safe(void) {
  return 1;
}
#else
EXPORTED int32_t yices_is_thread_safe(void) {
  return 0;
}
#endif



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
static inline node_table_t *get_nodes(void) {
  return term_manager_get_nodes(__yices_globals.manager);
}

static inline object_store_t *get_bvarith_store(void) {
  return term_manager_get_bvarith_store(__yices_globals.manager);
}

static inline object_store_t *get_bvarith64_store(void) {
  return term_manager_get_bvarith64_store(__yices_globals.manager);
}


static inline rba_buffer_t *get_arith_buffer(void) {
  return term_manager_get_arith_buffer(__yices_globals.manager);
}

static inline bvarith_buffer_t *get_bvarith_buffer(void) {
  return term_manager_get_bvarith_buffer(__yices_globals.manager);
}

static inline bvarith64_buffer_t *get_bvarith64_buffer(void) {
  return term_manager_get_bvarith64_buffer(__yices_globals.manager);
}

static inline bvlogic_buffer_t *get_bvlogic_buffer(void) {
  return term_manager_get_bvlogic_buffer(__yices_globals.manager);
}


/*
 * Allocate an arithmetic buffer, initialized to the zero polynomial.
 * Add it to the buffer list
 */
rba_buffer_t *yices_new_arith_buffer(void) {
  rba_buffer_t *b;

  b = alloc_arith_buffer();
  init_rba_buffer(b, __yices_globals.pprods);
  return b;
}


/*
 * Free an allocated buffer
 */
void yices_free_arith_buffer(rba_buffer_t *b) {
  delete_rba_buffer(b);
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
  init_bvarith_buffer(b, __yices_globals.pprods, get_bvarith_store());
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
  init_bvarith64_buffer(b, __yices_globals.pprods, get_bvarith64_store());
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

void arith_buffer_iterate(void *aux, void (*f)(void *, rba_buffer_t *)) {
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



/****************************************
 *  VECTOR INITIALIZATION AND DELETION  *
 ***************************************/

EXPORTED void yices_init_term_vector(term_vector_t *v) {
  v->capacity = 0;
  v->size = 0;
  v->data = NULL;
}

EXPORTED void yices_init_type_vector(type_vector_t *v) {
  v->capacity = 0;
  v->size = 0;
  v->data = NULL;
}

EXPORTED void yices_delete_term_vector(term_vector_t *v) {
  safe_free(v->data);
  v->data = NULL;
}

EXPORTED void yices_delete_type_vector(type_vector_t *v) {
  safe_free(v->data);
  v->data = NULL;
}

#define VECTOR_REDUCE_THRESHOLD 16384

EXPORTED void yices_reset_term_vector(term_vector_t *v) {
  v->size = 0;
  if (v->capacity > VECTOR_REDUCE_THRESHOLD) {
    safe_free(v->data);
    v->data = NULL;
    v->capacity = 0;
  }
}

EXPORTED void yices_reset_type_vector(type_vector_t *v) {
  v->size = 0;
  if (v->capacity > VECTOR_REDUCE_THRESHOLD) {
    safe_free(v->data);
    v->data = NULL;
    v->capacity = 0;
  }
}


/*
 * Add data at the end of a vector
 */
static inline void type_vector_push(type_vector_t *v, type_t tau) {
  ivector_push((ivector_t *) v, tau);
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
    error_report_t *error = get_yices_error();
    error->code = POS_INT_REQUIRED;
    error->badval = n;
    return false;
  }
  return true;
}

// Check whether n is less than YICES_MAX_ARITY
static bool check_arity(uint32_t n) {
  if (n > YICES_MAX_ARITY) {
    error_report_t *error = get_yices_error();
    error->code = TOO_MANY_ARGUMENTS;
    error->badval = n;
    return false;
  }
  return true;
}

// Check whether n is less than TYPE_MACRO_MAX_ARITY
static bool check_macro_arity(uint32_t n) {
  if (n == 0) {
    error_report_t *error = get_yices_error();
    error->code = POS_INT_REQUIRED;
    error->badval = n;
    return false;
  }
  if (n > TYPE_MACRO_MAX_ARITY) {
    error_report_t *error = get_yices_error();
    error->code = TOO_MANY_MACRO_PARAMS;
    error->badval = n;
    return false;
  }
  return true;
}

// Check whether n is less than YICES_MAX_VARS
static bool check_maxvars(uint32_t n) {
  if (n > YICES_MAX_VARS) {
    error_report_t *error = get_yices_error();
    error->code = TOO_MANY_VARS;
    error->badval = n;
    return false;
  }
  return true;
}

// Check whether n is less than YICES_MAX_BVSIZE
static bool check_maxbvsize(uint32_t n) {
  if (n > YICES_MAX_BVSIZE) {
    error_report_t *error = get_yices_error();
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = n;
    return false;
  }
  return true;
}

// Check whether d is no more than YICES_MAX_DEGREE
static bool check_maxdegree(uint32_t d) {
  if (d > YICES_MAX_DEGREE) {
    error_report_t *error = get_yices_error();
    error->code = DEGREE_OVERFLOW;
    error->badval = d;
    return false;
  }
  return true;
}

// Check whether tau is a valid type
static bool check_good_type(type_table_t *tbl, type_t tau) {
  if (bad_type(tbl, tau)) {
    error_report_t *error = get_yices_error();
    error->code = INVALID_TYPE;
    error->type1 = tau;
    return false;
  }
  return true;
}

// Check whether all types in a[0 ... n-1] are valid
static bool check_good_types(type_table_t *tbl, uint32_t n, const type_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (bad_type(tbl, a[i])) {
      error_report_t *error = get_yices_error();
      error->code = INVALID_TYPE;
      error->type1 = a[i];
      return false;
    }
  }
  return true;
}

// Check whether all types in a[0 ... n-1] are type variables
static bool check_all_type_variables(type_table_t *tbl, uint32_t n, const type_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (! is_type_variable(tbl, a[i])) {
      error_report_t *error = get_yices_error();
      error->code = TYPE_VAR_REQUIRED;
      error->type1 = a[i];
      return false;
    }
  }
  return true;
}

// Check whether all variables in a[0...n-1] are distinct
static bool check_no_duplicate_type_vars(uint32_t n, const type_t *a) {
  type_t aux[10];
  type_t *b;
  uint32_t i;
  bool result;

  assert(n <= UINT32_MAX/sizeof(type_t)); // because n <= TYPE_MACRO_MAX_ARITY

  result = true;
  if (n > 1) {
    b = aux;
    if (n > 10) {
      b = (int32_t *) safe_malloc(n * sizeof(int32_t));
    }
    for (i=0; i<n; i++) {
      b[i] = a[i];
    }
    int_array_sort(b, n);
    for (i=1; i<n; i++) {
      if (b[i-1] == b[i]) {
	error_report_t *error = get_yices_error();
	error->code = DUPLICATE_TYPE_VAR;
	error->type1 = b[i];
	result = false;
	break;
      }
    }
    if (n > 10) {
      safe_free(b);
    }
  }

  return result;
}


// Check whether tau is a scalar type. tau must be a good type in tbl
static bool check_scalar_type(type_table_t *tbl, type_t tau) {
  if (! is_scalar_type(tbl, tau)) {
    error_report_t *error = get_yices_error();
    error->code = INVALID_TYPE_OP;
    error->type1 = tau;
    return false;
  }
  return true;
}

// Check whether tau is uninterpreted or scalar, and whether
// i a valid constant index for type tau.
static bool check_good_constant(type_table_t *tbl, type_t tau, int32_t i) {
  type_kind_t kind;

  if (bad_type(tbl, tau)) {
    error_report_t *error = get_yices_error();
    error->code = INVALID_TYPE;
    error->type1 = tau;
    return false;
  }
  kind = type_kind(tbl, tau);
  if (kind != UNINTERPRETED_TYPE && kind != SCALAR_TYPE) {
    error_report_t *error = get_yices_error();
    error->code = SCALAR_OR_UTYPE_REQUIRED;
    error->type1 = tau;
    return false;
  }
  if (i < 0 ||
      (kind == SCALAR_TYPE && i >= scalar_type_cardinal(tbl, tau))) {
    error_report_t *error = get_yices_error();
    error->code = INVALID_CONSTANT_INDEX;
    error->type1 = tau;
    error->badval = i;
    return false;
  }
  return true;
}

// Check whether tau is a bitvector type (tau is valid)
static bool check_bvtype(type_table_t *tbl, type_t tau) {
  if (! is_bv_type(tbl, tau)) {
    error_report_t *error = get_yices_error();
    error->code = BVTYPE_REQUIRED;
    error->type1 = tau;
    return false;
  }
  return true;
}

// Check whether t is a valid term
static bool check_good_term(term_manager_t *mngr, term_t t) {
  term_table_t *tbl;

  tbl = term_manager_get_terms(mngr);
  if (bad_term(tbl, t)) {
    error_report_t *error = get_yices_error();
    error->code = INVALID_TERM;
    error->term1 = t;
    return false;
  }
  return true;
}

// Check that terms in a[0 ... n-1] are valid
static bool check_good_terms(term_manager_t *mngr, uint32_t n, const term_t *a) {
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    if (bad_term(tbl, a[i])) {
      error_report_t *error = get_yices_error();
      error->code = INVALID_TERM;
      error->term1 = a[i];
      return false;
    }
  }
  return true;
}

// check that terms a[0 ... n-1] have types that match tau[0 ... n-1].
static bool check_arg_types(term_manager_t *mngr, uint32_t n, const term_t *a, const type_t *tau) {
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    if (! is_subtype(tbl->types, term_type(tbl, a[i]), tau[i])) {
      error_report_t *error = get_yices_error();
      error->code = TYPE_MISMATCH;
      error->term1 = a[i];
      error->type1 = tau[i];
      return false;
    }
  }

  return true;
}

// check whether (f a[0] ... a[n-1]) is type correct
static bool check_good_application(term_manager_t *mngr, term_t f, uint32_t n, const term_t *a) {
  term_table_t *tbl;
  function_type_t *ft;

  if (! check_positive(n) ||
      ! check_good_term(mngr, f) ||
      ! check_good_terms(mngr, n, a)) {
    return false;
  }

  tbl = term_manager_get_terms(mngr);

  if (! is_function_term(tbl, f)) {
    error_report_t *error = get_yices_error();
    error->code = FUNCTION_REQUIRED;
    error->term1 = f;
    return false;
  }

  ft = function_type_desc(tbl->types, term_type(tbl, f));
  if (n != ft->ndom) {
    error_report_t *error = get_yices_error();
    error->code = WRONG_NUMBER_OF_ARGUMENTS;
    error->type1 = term_type(tbl, f);
    error->badval = n;
    return false;
  }

  return check_arg_types(mngr, n, a, ft->domain);
}

// Check whether t is a boolean term. t must be a valid term
static bool check_boolean_term(term_manager_t *mngr, term_t t) {
  term_table_t *tbl;

  tbl = term_manager_get_terms(mngr);

  if (! is_boolean_term(tbl, t)) {
    error_report_t *error = get_yices_error();
    error->code = TYPE_MISMATCH;
    error->term1 = t;
    error->type1 = bool_type(tbl->types);
    return false;
  }
  return true;
}

// Check whether t is an arithmetic term, t must be valid.
static bool check_arith_term(term_manager_t *mngr, term_t t) {
  term_table_t *tbl;

  tbl = term_manager_get_terms(mngr);

  if (! is_arithmetic_term(tbl, t)) {
    error_report_t *error = get_yices_error();
    error->code = ARITHTERM_REQUIRED;
    error->term1 = t;
    return false;
  }
  return true;
}

// Check whether t is an arithmetic constant, t must be valid
static bool check_arith_constant(term_manager_t *mngr, term_t t) {
  term_table_t *tbl;

  tbl = term_manager_get_terms(mngr);

  if (term_kind(tbl, t) != ARITH_CONSTANT) {
    error_report_t *error = get_yices_error();
    error->code = ARITHCONSTANT_REQUIRED;
    error->term1 = t;
    return false;
  }

  return true;
}

// Check whether t is a bitvector term, t must be valid
static bool check_bitvector_term(term_manager_t *mngr, term_t t) {
  term_table_t *tbl;

  tbl = term_manager_get_terms(mngr);

  if (! is_bitvector_term(tbl, t)) {
    error_report_t *error = get_yices_error();
    error->code = BITVECTOR_REQUIRED;
    error->term1 = t;
    return false;
  }
  return true;
}

// Check whether t has a scalar or uninterpreted type, t must be valid
static bool check_scalar_term(term_manager_t *mngr, term_t t) {
  term_table_t *tbl;

  tbl = term_manager_get_terms(mngr);

  if (!is_scalar_term(tbl, t) && !is_utype_term(tbl, t)) {
    error_report_t *error = get_yices_error();
    error->code = SCALAR_TERM_REQUIRED;
    error->term1 = t;
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
    error_report_t *error = get_yices_error();
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
static bool check_boolean_args(term_manager_t *mngr, uint32_t n, const term_t *a) {
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    if (! is_boolean_term(tbl, a[i])) {
      error_report_t *error = get_yices_error();
      error->code = TYPE_MISMATCH;
      error->term1 = a[i];
      error->type1 = bool_type(tbl->types);
      return false;
    }
  }

  return true;
}

// Check whether a[0 ... n-1] are all valid bitvectors
static bool check_bitvector_args(term_manager_t *mngr, uint32_t n, const term_t *a) {
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    if (! is_bitvector_term(tbl, a[i])) {
      error_report_t *error = get_yices_error();
      error->code = BITVECTOR_REQUIRED;
      error->term1 = a[i];
      return false;
    }
  }
  return true;
}


// Check whether a[0 ... n-1] all have the same type (n must be positive)
// this is used for (bv-and a[0] .... a[n-1]) and other associative bit-vector
// operators
static bool check_same_type(term_manager_t *mngr, uint32_t n, const term_t *a) {
  term_table_t *tbl;
  type_t tau0, tau;
  uint32_t i;

  assert(n > 0);

  tbl = term_manager_get_terms(mngr);

  tau0 = term_type(tbl, a[0]);
  for (i=1; i<n; i++) {
    tau = term_type(tbl, a[i]);
    if (tau != tau0) {
      error_report_t *error = get_yices_error();
      error->code = INCOMPATIBLE_TYPES;
      error->term1 = a[0];
      error->type1 = tau0;
      error->term2 = a[i];
      error->type2 = tau;
      return false;
    }
  }

  return true;
}



// Check whether terms a[0 ... n-1] are all arithmetic terms
static bool check_arithmetic_args(term_manager_t *mngr, uint32_t n, const term_t *a) {
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    if (! is_arithmetic_term(tbl, a[i])) {
      error_report_t *error = get_yices_error();
      error->code = ARITHTERM_REQUIRED;
      error->term1 = a[i];
      return false;
    }
  }

  return true;
}


// Check whether all numbers den[0 ... n-1] are positive
static bool check_denominators32(uint32_t n, const uint32_t *den) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (den[i] == 0) {
      set_error_code(DIVISION_BY_ZERO);
      return false;
    }
  }

  return true;
}


static bool check_denominators64(uint32_t n, const uint64_t *den) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (den[i] == 0) {
      set_error_code(DIVISION_BY_ZERO);
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
    error_report_t *error = get_yices_error();
    error->code = TUPLE_REQUIRED;
    error->term1 = t;
    return false;
  }

  if (i == 0 || i > tuple_type_arity(tbl->types, tau)) {
    error_report_t *error = get_yices_error();
    error->code = INVALID_TUPLE_INDEX;
    error->type1 = tau;
    error->badval = i;
    return false;
  }

  return true;
}

// Check that (update f (a_1 ... a_n) v) is well typed
static bool check_good_update(term_manager_t *mngr, term_t f, uint32_t n, const term_t *a, term_t v) {
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
    error_report_t *error = get_yices_error();
    error->code = FUNCTION_REQUIRED;
    error->term1 = f;
    return false;
  }

  ft = function_type_desc(tbl->types, term_type(tbl, f));
  if (n != ft->ndom) {
    error_report_t *error = get_yices_error();
    error->code = WRONG_NUMBER_OF_ARGUMENTS;
    error->type1 = term_type(tbl, f);
    error->badval = n;
    return false;
  }

  if (! is_subtype(tbl->types, term_type(tbl, v), ft->range)) {
    error_report_t *error = get_yices_error();
    error->code = TYPE_MISMATCH;
    error->term1 = v;
    error->type1 = ft->range;
    return false;
  }

  return check_arg_types(mngr, n, a, ft->domain);
}

// Check (distinct t_1 ... t_n)
static bool check_good_distinct_term(term_manager_t *mngr, uint32_t n, const term_t *a) {
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
      error_report_t *error = get_yices_error();
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

// Check whether all elements of v are variables
// (this assumes that they are all good terms)
static bool check_good_variables(term_manager_t *mngr, uint32_t n, const term_t *v) {
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    if (is_neg_term(v[i]) || term_kind(tbl, v[i]) != VARIABLE) {
      error_report_t *error = get_yices_error();
      error->code = VARIABLE_REQUIRED;
      error->term1 = v[i];
      return false;
    }
  }

  return true;
}

// Check quantified formula (FORALL/EXISTS (v_1 ... v_n) body)
// v must be sorted.
static bool check_good_quantified_term(term_manager_t *mngr, uint32_t n, const term_t *v, term_t body) {
  uint32_t i;

  if (! check_positive(n) ||
      ! check_maxvars(n) ||
      ! check_good_term(mngr, body) ||
      ! check_good_terms(mngr, n, v) ||
      ! check_good_variables(mngr, n, v) ||
      ! check_boolean_term(mngr, body)) {
    return false;
  }

  for (i=1; i<n; i++) {
    if (v[i-1] == v[i]) {
      error_report_t *error = get_yices_error();
      error->code = DUPLICATE_VARIABLE;
      error->term1 = v[i];
      return false;
    }
  }

  return true;
}

// Check for duplicates in array v: don't modify v
static bool check_no_duplicates(uint32_t n, const term_t *v) {
  term_t buffer[10];
  term_t *a;
  uint32_t i;
  bool result;

  assert(n <= UINT32_MAX/sizeof(term_t)); // because n <= YICES_MAX_VARS

  result = true;
  if (n > 1) {
    a = buffer;
    if (n > 10) {
      a = (term_t *) safe_malloc(n * sizeof(term_t));
    }

    for (i=0; i<n; i++) {
      a[i] = v[i];
    }
    int_array_sort(a, n);
    for (i=1; i<n; i++) {
      if (a[i-1] == a[i]) {
	error_report_t *error = get_yices_error();
        error->code = DUPLICATE_VARIABLE;
        error->term1 = a[i];
        result = false;
        break;
      }
    }

    if (n > 10) {
      safe_free(a);
    }
  }

  return result;
}

// Check lambda term: (LAMBDA (v_1 ... v_n) body)
static bool check_good_lambda_term(term_manager_t *mngr, uint32_t n, const term_t *v, term_t body) {
  return
    check_positive(n) &&
    check_maxvars(n) &&
    check_good_term(mngr, body) &&
    check_good_terms(mngr, n, v) &&
    check_good_variables(mngr, n, v) &&
    check_no_duplicates(n, v);
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
    error_report_t *error = get_yices_error();
    error->code = TUPLE_REQUIRED;
    error->term1 = t;
    return false;
  }

  desc = tuple_type_desc(tbl->types, tau);
  if (i == 0 || i > desc->nelem) {
    error_report_t *error = get_yices_error();
    error->code = INVALID_TUPLE_INDEX;
    error->type1 = tau;
    error->badval = i;
    return false;
  }

  // types are indexed from 0 to desc->elem-1 in desc
  i --;
  if (! is_subtype(tbl->types, term_type(tbl, v), desc->elem[i])) {
    error_report_t *error = get_yices_error();
    error->code = TYPE_MISMATCH;
    error->term1 = v;
    error->type1 = desc->elem[i];
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

  d = (uint64_t) term_degree(tbl, t) * n;
  if (d > ((uint64_t) YICES_MAX_DEGREE)) {
    error_report_t *error = get_yices_error();
    error->code = DEGREE_OVERFLOW;
    error->badval = UINT32_MAX;
    return false;
  }

  return check_maxdegree((uint32_t) d);
}


// Check that the degree of t[0] x .... x t[n-1] does not overflow
static bool check_multi_prod_degree(term_manager_t *mngr, uint32_t n, const term_t *t) {
  term_table_t *tbl;
  uint32_t i, d;

  tbl = term_manager_get_terms(mngr);

  d = 0;
  for (i=0; i<n; i++) {
    d += term_degree(tbl, t[i]);
    if (d > YICES_MAX_DEGREE) {
      error_report_t *error = get_yices_error();
      error->code = DEGREE_OVERFLOW;
      error->badval = d;
      return false;
    }
  }

  return true;
}


// Check whether i is a valid shift for bitvectors of size n
static bool check_bitshift(uint32_t i, uint32_t n) {
  if (i > n) {
    error_report_t *error = get_yices_error();
    error->code = INVALID_BITSHIFT;
    error->badval = i;
    return false;
  }

  return true;
}

// Check whether [i, j] is a valid segment for bitvectors of size n
static bool check_bvextract(uint32_t i, uint32_t j, uint32_t n) {
  if (i > j || j >= n) {
    set_error_code(INVALID_BVEXTRACT);
    return false;
  }
  return true;
}

// Check whether i is a valid bit index for a bitvector of size n
static bool check_bitextract(uint32_t i, uint32_t n) {
  if (i >= n) {
    set_error_code(INVALID_BITEXTRACT);
    return false;
  }
  return true;
}


// Check that t is either a variable or an uninterpreted term
static bool term_is_var_or_uninterpreted(term_table_t *tbl, term_t t) {
  assert(good_term(tbl, t) && is_pos_term(t));
  switch (term_kind(tbl, t)) {
  case VARIABLE:
  case UNINTERPRETED_TERM:
    return true;
  default:
  return false;
 }
}

// Check that all terms of v are variables or uninterpreted terms
// all elements of v must be good terms
static bool check_good_vars_or_uninterpreted(term_manager_t *mngr, uint32_t n, const term_t *v) {
  term_table_t *tbl;
  uint32_t i;

  tbl = term_manager_get_terms(mngr);
  for (i=0; i<n; i++) {
    if (is_neg_term(v[i]) || !term_is_var_or_uninterpreted(tbl, v[i])) {
      error_report_t *error = get_yices_error();
      error->code = VARIABLE_REQUIRED;
      error->term1 = v[i];
      return false;
    }
  }

  return true;
}

// Check whether arrays v and a define a valid substitution
// both must be arrays of n elements
static bool check_good_substitution(term_manager_t *mngr, uint32_t n, const term_t *v, const term_t *a) {
  term_table_t *tbl;
  type_t tau;
  uint32_t i;

  if (! check_good_terms(mngr, n, v) ||
      ! check_good_terms(mngr, n, a) ||
      ! check_good_vars_or_uninterpreted(mngr, n, v)) {
    return false;
  }

  tbl = term_manager_get_terms(mngr);

  for (i=0; i<n; i++) {
    tau = term_type(tbl, v[i]);
    if (! is_subtype(tbl->types, term_type(tbl, a[i]), tau)) {
      error_report_t *error = get_yices_error();
      error->code = TYPE_MISMATCH;
      error->term1 = a[i];
      error->type1 = tau;
      return false;
    }
  }

  return true;
}


/*
 * Support for direct model construction given two arrays var and map
 */

// Check that all elements of v are uninterpreted terms
static bool check_all_uninterpreted(term_table_t *terms, uint32_t n, const term_t *var) {
  uint32_t i;
  term_t x;

  for (i=0; i<n; i++) {
    x = var[i];
    if (is_neg_term(x) || term_kind(terms, x) != UNINTERPRETED_TERM) {
      error_report_t *error = get_yices_error();
      error->code = MDL_UNINT_REQUIRED;
      error->term1 = x;
      return false;
    }
  }

  return true;
}


// Check that all elements of map are constant (tuple or primitive constants)
static bool check_all_constant(term_table_t *terms, uint32_t n, const term_t *map) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (! is_constant_term(terms, map[i])) {
      error_report_t *error = get_yices_error();
      error->code = MDL_CONSTANT_REQUIRED;
      error->term1 = map[i];
      return false;
    }
  }

  return true;
}

// Check that all elements of var are distinct
// Could be improved: avoid sorting for large n?
static bool check_all_distinct(term_table_t *terms, uint32_t n, const term_t *var) {
  term_t buffer[100];
  term_t *a;
  uint32_t i;
  bool result;


  result = true;
  if (n > 1) {

    if (n > terms->live_terms) {
      /*
       * there must be duplicates
       * we check this first just to be safe
       * since n <= terms->live_terms <= YICES_MAX_TERMS,
       * we know that n * sizeof(term_t) fits in 32bits
       * (which matters when we call safe_malloc(n * sizeof(term_t)).
       */
      error_report_t *error = get_yices_error();
      error->code = MDL_DUPLICATE_VAR;
      error->term1 = NULL_TERM;
      return false;
    }

    assert(n <= UINT32_MAX/sizeof(term_t));

    a = buffer;
    if (n > 100) {
      a = (term_t *) safe_malloc(n * sizeof(term_t));
    }

    for (i=0; i<n; i++) {
      a[i] = var[i];
    }
    int_array_sort(a, n);

    for (i=1; i<n; i++) {
      if (a[i-1] == a[i]) {
	error_report_t *error = get_yices_error();
	error->code = MDL_DUPLICATE_VAR;
	error->term1 = a[i];
	result = false;
	break;
      }
    }

    if (n > 100) {
      safe_free(a);
    }
  }

  return result;
}


static bool check_good_model_map(term_manager_t *mngr, uint32_t n, const term_t *var, const term_t *map) {
  term_table_t *terms;
  type_t tau;
  uint32_t i;

  terms = term_manager_get_terms(mngr);

  if (! check_good_terms(mngr, n, var) ||
      ! check_good_terms(mngr, n, map) ||
      ! check_all_uninterpreted(terms, n, var) ||
      ! check_all_constant(terms, n, map)) {
    return false;
  }

  for (i=0; i<n; i++) {
    tau = term_type(terms, var[i]);
    if (! is_subtype(terms->types, term_type(terms, map[i]), tau)) {
      error_report_t *error = get_yices_error();
      error->code = TYPE_MISMATCH;
      error->term1 = map[i];
      error->type1 = tau;
      return false;
    }
  }

  if (! check_all_distinct(terms, n, var)) {
    return false;
  }

  return true;
}



/*
 * Check that all elements in var are uninterpreted and have a simple type (for model generalization)
 * - for now, simple means either Boolean, or bit-vector, or real, or a scalar type
 */
static bool check_elim_vars(term_manager_t *mngr, uint32_t n, const term_t *var) {
  term_table_t *terms;
  type_table_t *types;
  type_t tau;
  uint32_t i;

  terms = term_manager_get_terms(mngr);
  types = term_manager_get_types(mngr);

  if (! check_good_terms(mngr, n, var) ||
      ! check_all_uninterpreted(terms, n, var)) {
    return false;
  }

  for (i=0; i<n; i++) {
    tau = term_type(terms, var[i]);
    switch (type_kind(types, tau)) {
    case BOOL_TYPE:
    case INT_TYPE:
    case REAL_TYPE:
    case BITVECTOR_TYPE:
    case SCALAR_TYPE:
      break;

    default:
      {
	error_report_t *error = get_yices_error();
	error->code = MDL_GEN_TYPE_NOT_SUPPORTED;
	error->type1 = tau;
	return false;
      }
    }
  }

  return true;
}



/*
 * Checks for the term-exploration functions.
 * All these checks set the error code to INVALID_TERM_OP
 * - t must be a valid term.
 */
static bool check_composite(term_table_t *terms, term_t t) {
  if (! term_is_composite(terms, t)) {
    set_error_code(INVALID_TERM_OP);
    return false;
  }

  return true;
}

static bool check_projection(term_table_t *terms, term_t t) {
  if (! term_is_projection(terms, t)) {
    set_error_code(INVALID_TERM_OP);
    return false;
  }
  return true;
}

static bool check_constructor(term_table_t *terms, term_t t, term_constructor_t c) {
  if (term_constructor(terms, t) != c) {
    set_error_code(INVALID_TERM_OP);
    return false;
  }
  return true;
}

static bool check_child_idx(term_table_t *terms, term_t t, int32_t i) {
  if (i < 0 || i >= term_num_children(terms, t)) {
    set_error_code(INVALID_TERM_OP);
    return false;
  }

  return true;
}




/***********************
 *  TYPE CONSTRUCTORS  *
 **********************/

EXPORTED type_t yices_bool_type(void) {
  MT_PROTECT(type_t, __yices_globals.lock, _o_yices_bool_type());
}

type_t _o_yices_bool_type(void) {
  return bool_type(__yices_globals.types);
}

EXPORTED type_t yices_int_type(void) {
  MT_PROTECT(type_t, __yices_globals.lock, _o_yices_int_type());
}

type_t _o_yices_int_type(void) {
  return int_type(__yices_globals.types);
}

EXPORTED type_t yices_real_type(void) {
  MT_PROTECT(type_t, __yices_globals.lock, _o_yices_real_type());
}

type_t _o_yices_real_type(void) {
  return real_type(__yices_globals.types);
}

EXPORTED type_t yices_bv_type(uint32_t size) {
  MT_PROTECT(type_t, __yices_globals.lock, _o_yices_bv_type(size));
}

type_t _o_yices_bv_type(uint32_t size) {
  if (! check_positive(size) || ! check_maxbvsize(size)) {
    return NULL_TYPE;
  }
  return bv_type(__yices_globals.types, size);
}

EXPORTED type_t yices_new_uninterpreted_type(void) {
  MT_PROTECT(type_t, __yices_globals.lock, _o_yices_new_uninterpreted_type());
}

type_t _o_yices_new_uninterpreted_type(void) {
  return new_uninterpreted_type(__yices_globals.types);
}

EXPORTED type_t yices_new_scalar_type(uint32_t card) {
  MT_PROTECT(type_t, __yices_globals.lock, _o_yices_new_scalar_type(card));
}

type_t _o_yices_new_scalar_type(uint32_t card) {
  if (! check_positive(card)) {
    return NULL_TYPE;
  }
  return new_scalar_type(__yices_globals.types, card);
}

EXPORTED type_t yices_tuple_type(uint32_t n, const type_t elem[]) {
  MT_PROTECT(type_t, __yices_globals.lock, _o_yices_tuple_type(n, elem));
}

type_t _o_yices_tuple_type(uint32_t n, const type_t elem[]) {
  if (! check_positive(n) ||
      ! check_arity(n) ||
      ! check_good_types(__yices_globals.types, n, elem)) {
    return NULL_TYPE;
  }
  return tuple_type(__yices_globals.types, n, elem);
}

EXPORTED type_t yices_function_type(uint32_t n, const type_t dom[], type_t range) {
  MT_PROTECT( type_t, __yices_globals.lock, _o_yices_function_type(n, dom, range));
}

type_t _o_yices_function_type(uint32_t n, const type_t dom[], type_t range) {
  if (! check_positive(n) ||
      ! check_arity(n) ||
      ! check_good_type(__yices_globals.types, range) ||
      ! check_good_types(__yices_globals.types, n, dom)) {
    return NULL_TYPE;
  }
  return function_type(__yices_globals.types, range, n, dom);
}


/*
 * Variants/short cuts for tuple and function types
 */
EXPORTED type_t yices_tuple_type1(type_t tau1) {
  return yices_tuple_type(1, &tau1);
}

EXPORTED type_t yices_tuple_type2(type_t tau1, type_t tau2) {
  type_t aux[2];

  aux[0] = tau1;
  aux[1] = tau2;

  return yices_tuple_type(2, aux);
}

EXPORTED type_t yices_tuple_type3(type_t tau1, type_t tau2, type_t tau3) {
  type_t aux[3];

  aux[0] = tau1;
  aux[1] = tau2;
  aux[2] = tau3;

  return yices_tuple_type(3, aux);
}

EXPORTED type_t yices_function_type1(type_t tau1, type_t range) {
  return yices_function_type(1, &tau1, range);
}

EXPORTED type_t yices_function_type2(type_t tau1, type_t tau2, type_t range) {
  type_t aux[2];

  aux[0] = tau1;
  aux[1] = tau2;

  return yices_function_type(2, aux, range);
}

EXPORTED type_t yices_function_type3(type_t tau1, type_t tau2, type_t tau3, type_t range) {
  type_t aux[3];

  aux[0] = tau1;
  aux[1] = tau2;
  aux[2] = tau3;

  return yices_function_type(3, aux, range);
}



/*
 * Type macros and constructors
 */

/*
 * Type variable with the given id
 */
type_t yices_type_variable(uint32_t id) {
  return type_variable(__yices_globals.types, id);
}

/*
 * Create a type constructor:
 * - name = its name
 * - n = arity
 * return -1 if there's an error or the macro id otherwise
 */
int32_t yices_type_constructor(const char *name, uint32_t n) {
  char *clone;

  if (! check_macro_arity(n)) {
    return -1;
  }
  clone = clone_string(name);
  return add_type_constructor(__yices_globals.types, clone, n);
}

/*
 * Create a type macro:
 * - name = its name
 * - n = arity
 * - vars = array of n distinct type variables
 * - body = type
 *
 * return -1 if there's an error or the macro id otherwise
 */
int32_t yices_type_macro(const char *name, uint32_t n, type_t *vars, type_t body) {
  char *clone;

  if (! check_macro_arity(n) ||
      ! check_good_type(__yices_globals.types, body) ||
      ! check_good_types(__yices_globals.types, n, vars) ||
      ! check_all_type_variables(__yices_globals.types, n, vars) ||
      ! check_no_duplicate_type_vars(n, vars)) {
    return -1;
  }

  clone = clone_string(name);
  return add_type_macro(__yices_globals.types, clone, n, vars, body);
}


/*
 * Instance of a macro or constructor
 * - cid = constructor or macro id
 * - n = number of arguments
 * - tau[0 ... n-1] = argument types
 *
 * return NULL_TYPE if there's an error
 */
type_t yices_instance_type(int32_t cid, uint32_t n, type_t tau[]) {
  type_macro_t *macro;

  macro = type_macro(__yices_globals.types, cid);
  if (macro == NULL) {
    error_report_t *error = get_yices_error();
    error->code = INVALID_MACRO;
    error->badval = cid;
    return NULL_TYPE;
  }

  if (n != macro->arity) {
    error_report_t *error = get_yices_error();
    error->code = WRONG_NUMBER_OF_ARGUMENTS;
    error->type1 = NULL_TYPE;
    error->badval = n;
    return NULL_TYPE;
  }

  if (! check_good_types(__yices_globals.types, n, tau)) {
    return NULL_TYPE;
  }

  return instantiate_type_macro(__yices_globals.types, cid, n, tau);
}


/*
 * Get the macro id for a given name
 * - return -1 if there's no macro or constructor with that name
 */
int32_t yices_get_macro_by_name(const char *name) {
  return get_type_macro_by_name(__yices_globals.types, name);
}


/*
 * Remove the mapping of name --> macro id
 * - no change if no such mapping exists
 */
void yices_remove_type_macro_name(const char *name) {
  remove_type_macro_name(__yices_globals.types, name);
}

/*
 * Remove a macro with the given id
 * - id must be a valid macro index (non-negative)
 */
void yices_delete_type_macro(int32_t id) {
  delete_type_macro(__yices_globals.types, id);
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
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_constant(tau, index));
}

term_t _o_yices_constant(type_t tau, int32_t index) {
  if (! check_good_constant(__yices_globals.types, tau, index)) {
    return NULL_TERM;
  }

  return mk_constant(__yices_globals.manager, tau, index);
}

EXPORTED term_t yices_new_uninterpreted_term(type_t tau) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_new_uninterpreted_term(tau));
}

term_t _o_yices_new_uninterpreted_term(type_t tau) {
  if (! check_good_type(__yices_globals.types, tau)) {
    return NULL_TERM;
  }

  return mk_uterm(__yices_globals.manager, tau);
}

EXPORTED term_t yices_new_variable(type_t tau) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_new_variable(tau));
}

term_t _o_yices_new_variable(type_t tau) {
  if (! check_good_type(__yices_globals.types, tau)) {
    return NULL_TERM;
  }

  return mk_variable(__yices_globals.manager, tau);
}


/*
 * Apply fun to arg[0 ...n-1]
 * - we apply beta-reduction eagerly here
 */
EXPORTED term_t yices_application(term_t fun, uint32_t n, const term_t arg[]) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_application(fun, n, arg));
}

term_t _o_yices_application(term_t fun, uint32_t n, const term_t arg[]) {
  term_t t;

  if (! check_good_application(__yices_globals.manager, fun, n, arg)) {
    return NULL_TERM;
  }

  t = mk_application(__yices_globals.manager, fun, n, arg);
  t = beta_reduce(__yices_globals.manager, t);

  if (t < 0) {
    // error during beta reduction
    error_report_t *error = get_yices_error();
    if (t == -1) {
      // degree overflow
      error->code = DEGREE_OVERFLOW;
      error->badval = YICES_MAX_DEGREE + 1;
    } else {
      // BUG
      error->code = INTERNAL_EXCEPTION;
    }

    t = NULL_TERM;
  }

  return t;
}

/*
 * Variants for small n
 */
EXPORTED term_t yices_application1(term_t fun, term_t arg1) {
  return yices_application(fun, 1, &arg1);
}

EXPORTED term_t yices_application2(term_t fun, term_t arg1, term_t arg2) {
  term_t aux[2];

  aux[0] = arg1;
  aux[1] = arg2;
  return yices_application(fun, 2, aux);
}

EXPORTED term_t yices_application3(term_t fun, term_t arg1, term_t arg2, term_t arg3) {
  term_t aux[3];

  aux[0] = arg1;
  aux[1] = arg2;
  aux[2] = arg3;
  return yices_application(fun, 3, aux);
}


EXPORTED term_t yices_ite(term_t cond, term_t then_term, term_t else_term) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_ite(cond, then_term, else_term));
}

term_t _o_yices_ite(term_t cond, term_t then_term, term_t else_term) {
  term_table_t *tbl;
  type_t tau;

  // Check type correctness: first steps
  if (! check_good_term(__yices_globals.manager, cond) ||
      ! check_good_term(__yices_globals.manager, then_term) ||
      ! check_good_term(__yices_globals.manager, else_term) ||
      ! check_boolean_term(__yices_globals.manager, cond)) {
    return NULL_TERM;
  }

  // Check whether then/else are compatible and get the supertype
  tbl = __yices_globals.terms;
  tau = super_type(__yices_globals.types, term_type(tbl, then_term), term_type(tbl, else_term));

  if (tau == NULL_TYPE) {
    // type error
    error_report_t *error = get_yices_error();
    error->code = INCOMPATIBLE_TYPES;
    error->term1 = then_term;
    error->type1 = term_type(tbl, then_term);
    error->term2 = else_term;
    error->type2 = term_type(tbl, else_term);
    return NULL_TERM;
  }

  return mk_ite(__yices_globals.manager, cond, then_term, else_term, tau);
}

EXPORTED term_t yices_eq(term_t left, term_t right) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_eq(left, right));
}

term_t _o_yices_eq(term_t left, term_t right) {
  if (! check_good_eq(__yices_globals.manager, left, right)) {
    return NULL_TERM;
  }

  return mk_eq(__yices_globals.manager, left, right);
}

EXPORTED term_t yices_neq(term_t left, term_t right) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_neq(left, right));
}

term_t _o_yices_neq(term_t left, term_t right) {
  if (! check_good_eq(__yices_globals.manager, left, right)) {
    return NULL_TERM;
  }

  return mk_neq(__yices_globals.manager, left, right);
}


/*
 * BOOLEAN NEGATION
 */
EXPORTED term_t yices_not(term_t arg) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_not(arg));
}

term_t _o_yices_not(term_t arg) {
  if (! check_good_term(__yices_globals.manager, arg) ||
      ! check_boolean_term(__yices_globals.manager, arg)) {
    return NULL_TERM;
  }

  return opposite_term(arg);
}


/*
 * OR, AND, and XOR may modify arg
 */
EXPORTED term_t yices_or(uint32_t n, term_t arg[]) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_or(n, arg));
}

term_t _o_yices_or(uint32_t n, term_t arg[]) {
  if (! check_arity(n) ||
      ! check_good_terms(__yices_globals.manager, n, arg) ||
      ! check_boolean_args(__yices_globals.manager, n, arg)) {
    return NULL_TERM;
  }

  switch (n) {
  case 0:
    return false_term;
  case 1:
    return arg[0];
  case 2:
    return mk_binary_or(__yices_globals.manager, arg[0], arg[1]);
  default:
    return mk_or(__yices_globals.manager, n, arg);
  }
}

EXPORTED term_t yices_and(uint32_t n, term_t arg[]) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_and(n, arg));
}

term_t _o_yices_and(uint32_t n, term_t arg[]) {
  if (! check_arity(n) ||
      ! check_good_terms(__yices_globals.manager, n, arg) ||
      ! check_boolean_args(__yices_globals.manager, n, arg)) {
    return NULL_TERM;
  }

  switch (n) {
  case 0:
    return true_term;
  case 1:
    return arg[0];
  case 2:
    return mk_binary_and(__yices_globals.manager, arg[0], arg[1]);
  default:
    return mk_and(__yices_globals.manager, n, arg);
  }
}

EXPORTED term_t yices_xor(uint32_t n, term_t arg[]) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_xor(n, arg));
}

term_t _o_yices_xor(uint32_t n, term_t arg[]) {
  if (! check_arity(n) ||
      ! check_good_terms(__yices_globals.manager, n, arg) ||
      ! check_boolean_args(__yices_globals.manager, n, arg)) {
    return NULL_TERM;
  }

  switch (n) {
  case 0:
    return false_term;
  case 1:
    return arg[0];
  case 2:
    return mk_binary_xor(__yices_globals.manager, arg[0], arg[1]);
  default:
    return mk_xor(__yices_globals.manager, n, arg);
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
EXPORTED term_t yices_or2(term_t left, term_t right) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_or2(left, right));
}

term_t _o_yices_or2(term_t left, term_t right) {
  if (! check_good_term(__yices_globals.manager, left) ||
      ! check_good_term(__yices_globals.manager, right) ||
      ! check_boolean_term(__yices_globals.manager, left) ||
      ! check_boolean_term(__yices_globals.manager, right)) {
    return NULL_TERM;
  }

  return mk_binary_or(__yices_globals.manager, left, right);
}

EXPORTED term_t yices_and2(term_t left, term_t right) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_and2(left, right));
}

term_t _o_yices_and2(term_t left, term_t right) {
  if (! check_good_term(__yices_globals.manager, left) ||
      ! check_good_term(__yices_globals.manager, right) ||
      ! check_boolean_term(__yices_globals.manager, left) ||
      ! check_boolean_term(__yices_globals.manager, right)) {
    return NULL_TERM;
  }

  return mk_binary_and(__yices_globals.manager, left, right);
}

EXPORTED term_t yices_xor2(term_t left, term_t right) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_xor2(left, right));
}

term_t _o_yices_xor2(term_t left, term_t right) {
  if (! check_good_term(__yices_globals.manager, left) ||
      ! check_good_term(__yices_globals.manager, right) ||
      ! check_boolean_term(__yices_globals.manager, left) ||
      ! check_boolean_term(__yices_globals.manager, right)) {
    return NULL_TERM;
  }

  return mk_binary_xor(__yices_globals.manager, left, right);
}


EXPORTED term_t yices_iff(term_t left, term_t right) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_iff(left, right));
}

term_t _o_yices_iff(term_t left, term_t right) {
  if (! check_good_term(__yices_globals.manager, left) ||
      ! check_good_term(__yices_globals.manager, right) ||
      ! check_boolean_term(__yices_globals.manager, left) ||
      ! check_boolean_term(__yices_globals.manager, right)) {
    return NULL_TERM;
  }

  return mk_iff(__yices_globals.manager, left, right);
}

EXPORTED term_t yices_implies(term_t left, term_t right) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_implies(left, right));
}

term_t _o_yices_implies(term_t left, term_t right) {
  if (! check_good_term(__yices_globals.manager, left) ||
      ! check_good_term(__yices_globals.manager, right) ||
      ! check_boolean_term(__yices_globals.manager, left) ||
      ! check_boolean_term(__yices_globals.manager, right)) {
    return NULL_TERM;
  }

  return mk_implies(__yices_globals.manager, left, right);
}


EXPORTED term_t yices_tuple(uint32_t n, const term_t arg[]) {
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_tuple(n, arg));
}

term_t _o_yices_tuple(uint32_t n, const term_t arg[]) {
  if (! check_positive(n) ||
      ! check_arity(n) ||
      ! check_good_terms(__yices_globals.manager, n, arg)) {
    return NULL_TERM;
  }

  return mk_tuple(__yices_globals.manager, n, arg);
}

// variants for n=2 or n=3
EXPORTED term_t yices_pair(term_t arg1, term_t arg2) {
  term_t aux[2];

  aux[0] = arg1;
  aux[1] = arg2;

  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_tuple(2, aux));
}

EXPORTED term_t yices_triple(term_t arg1, term_t arg2, term_t arg3) {
  term_t aux[3];

  aux[0] = arg1;
  aux[1] = arg2;
  aux[2] = arg3;

  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_tuple(3, aux));
}



EXPORTED term_t yices_select(uint32_t index, term_t tuple) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_select(index, tuple));
}

term_t _o_yices_select(uint32_t index, term_t tuple) {
  if (! check_good_select(__yices_globals.manager, index, tuple)) {
    return NULL_TERM;
  }

  // Warning: internally, tuple components are indexed from 0 to n-1
  return mk_select(__yices_globals.manager, index-1, tuple);
}

EXPORTED term_t yices_update(term_t fun, uint32_t n, const term_t arg[], term_t new_v) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_update(fun, n, arg, new_v));
}

term_t _o_yices_update(term_t fun, uint32_t n, const term_t arg[], term_t new_v) {
  if (! check_good_update(__yices_globals.manager, fun, n, arg, new_v)) {
    return NULL_TERM;
  }

  return mk_update(__yices_globals.manager, fun, n, arg, new_v);
}

// Variants for n=1, 2, or 3
EXPORTED term_t yices_update1(term_t fun, term_t arg1, term_t new_v) {
  return yices_update(fun, 1, &arg1, new_v);
}

EXPORTED term_t yices_update2(term_t fun, term_t arg1, term_t arg2, term_t new_v) {
  term_t aux[2];

  aux[0] = arg1;
  aux[1] = arg2;
  return yices_update(fun, 2, aux, new_v);
}

EXPORTED term_t yices_update3(term_t fun, term_t arg1, term_t arg2, term_t arg3, term_t new_v) {
  term_t aux[3];

  aux[0] = arg1;
  aux[1] = arg2;
  aux[2] = arg3;
  return yices_update(fun, 3, aux, new_v);
}



EXPORTED term_t yices_distinct(uint32_t n, term_t arg[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_distinct(n, arg));
}

term_t _o_yices_distinct(uint32_t n, term_t arg[]) {
  if (! check_positive(n) ||
      ! check_arity(n) ||
      ! check_good_distinct_term(__yices_globals.manager, n, arg)) {
    return NULL_TERM;
  }

  return mk_distinct(__yices_globals.manager, n, arg);
}

EXPORTED term_t yices_tuple_update(term_t tuple, uint32_t index, term_t new_v) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_tuple_update(tuple, index, new_v));
}

term_t _o_yices_tuple_update(term_t tuple, uint32_t index, term_t new_v) {
  if (! check_good_tuple_update(__yices_globals.manager, index, tuple, new_v)) {
    return NULL_TERM;
  }

  // Warning: internally components are indexed from 0 to n-1
  return mk_tuple_update(__yices_globals.manager, tuple, index-1, new_v);
}

EXPORTED term_t yices_forall(uint32_t n, term_t var[], term_t body) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_forall(n, var, body));
}

term_t _o_yices_forall(uint32_t n, term_t var[], term_t body) {
  if (n > 1) {
    int_array_sort(var, n);
  }

  if (! check_good_quantified_term(__yices_globals.manager, n, var, body)) {
    return NULL_TERM;
  }

  return mk_forall(__yices_globals.manager, n, var, body);
}

EXPORTED term_t yices_exists(uint32_t n, term_t var[], term_t body) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_exists(n, var, body));
}

term_t _o_yices_exists(uint32_t n, term_t var[], term_t body) {
  if (n > 1) {
    int_array_sort(var, n);
  }

  if (! check_good_quantified_term(__yices_globals.manager, n, var, body)) {
    return NULL_TERM;
  }

  return mk_exists(__yices_globals.manager, n, var, body);
}

EXPORTED term_t yices_lambda(uint32_t n, const term_t var[], term_t body) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_lambda(n, var, body));
}

term_t _o_yices_lambda(uint32_t n, const term_t var[], term_t body) {
  if (! check_good_lambda_term(__yices_globals.manager, n, var, body)) {
    return NULL_TERM;
  }

  return mk_lambda(__yices_globals.manager, n, var, body);
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
  MT_PROTECT(term_t, __yices_globals.lock, _o_yices_int32(val));
}

term_t _o_yices_int32(int32_t val) {
  q_set32(&r0, val);
  return  mk_arith_constant(__yices_globals.manager, &r0);
}


EXPORTED term_t yices_int64(int64_t val) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_int64(val));
}

term_t _o_yices_int64(int64_t val) {
  q_set64(&r0, val);
  return mk_arith_constant(__yices_globals.manager, &r0);
}


/*
 * Rational constants
 */
EXPORTED term_t yices_rational32(int32_t num, uint32_t den) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_rational32(num, den));
}

term_t _o_yices_rational32(int32_t num, uint32_t den) {
  if (den == 0) {
    set_error_code(DIVISION_BY_ZERO);
    return NULL_TERM;
  }

  q_set_int32(&r0, num, den);
  return mk_arith_constant(__yices_globals.manager, &r0);
}


EXPORTED term_t yices_rational64(int64_t num, uint64_t den) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_rational64(num, den));
}

term_t _o_yices_rational64(int64_t num, uint64_t den) {
  if (den == 0) {
    set_error_code(DIVISION_BY_ZERO);
    return NULL_TERM;
  }

  q_set_int64(&r0, num, den);
  return mk_arith_constant(__yices_globals.manager, &r0);
}


/*
 * Constant from GMP integers or rationals
 */
EXPORTED term_t yices_mpz(const mpz_t z) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_mpz(z));
}

term_t _o_yices_mpz(const mpz_t z) {
  term_t t;

  q_set_mpz(&r0, z);
  t = mk_arith_constant(__yices_globals.manager, &r0);
  q_clear(&r0);

  return t;
}

EXPORTED term_t yices_mpq(const mpq_t q) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_mpq(q));
}

term_t _o_yices_mpq(const mpq_t q) {
  term_t t;

  q_set_mpq(&r0, q);
  t = mk_arith_constant(__yices_globals.manager, &r0);
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
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_parse_rational(s));
}

term_t _o_yices_parse_rational(const char *s) {
  int32_t code;
  term_t t;

  code = q_set_from_string(&r0, s);
  if (code < 0) {
    if (code == -1) {
      // wrong format
      set_error_code(INVALID_RATIONAL_FORMAT);
    } else {
      // denominator is 0
      set_error_code(DIVISION_BY_ZERO);
    }
    return NULL_TERM;
  }

  t = mk_arith_constant(__yices_globals.manager, &r0);
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
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_parse_float(s));
}

term_t _o_yices_parse_float(const char *s) {
  term_t t;

  if (q_set_from_float_string(&r0, s) < 0) {
    // wrong format
    set_error_code(INVALID_FLOAT_FORMAT);
    return NULL_TERM;
  }

  t = mk_arith_constant(__yices_globals.manager, &r0);
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
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_add(t1, t2));
}

term_t _o_yices_add(term_t t1, term_t t2) {
  rba_buffer_t *b;
  term_table_t *tbl;

  if (! check_both_arith_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  reset_rba_buffer(b);
  rba_buffer_add_term(b, tbl, t1);
  rba_buffer_add_term(b, tbl, t2);

  return mk_arith_term(__yices_globals.manager, b);
}


/*
 * Subtract t2 from t1
 */
EXPORTED term_t yices_sub(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_sub(t1, t2));
}

term_t _o_yices_sub(term_t t1, term_t t2) {
  rba_buffer_t *b;
  term_table_t *tbl;

  if (! check_both_arith_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  reset_rba_buffer(b);
  rba_buffer_add_term(b, tbl, t1);
  rba_buffer_sub_term(b, tbl, t2);

  return mk_arith_term(__yices_globals.manager, b);
}


/*
 * Negate t1
 */
EXPORTED term_t yices_neg(term_t t1) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_neg(t1));
}

term_t _o_yices_neg(term_t t1) {
  rba_buffer_t *b;
  term_table_t *tbl;

  if (! check_good_term(__yices_globals.manager, t1) ||
      ! check_arith_term(__yices_globals.manager, t1)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  reset_rba_buffer(b);
  rba_buffer_sub_term(b, tbl, t1);

  return mk_arith_term(__yices_globals.manager, b);
}


/*
 * Multiply t1 and t2
 */
EXPORTED term_t yices_mul(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_mul(t1, t2));
}

term_t _o_yices_mul(term_t t1, term_t t2) {
  rba_buffer_t *b;
  term_table_t *tbl;

  if (! check_both_arith_terms(__yices_globals.manager, t1, t2) ||
      ! check_product_degree(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  reset_rba_buffer(b);
  rba_buffer_add_term(b, tbl, t1);
  rba_buffer_mul_term(b, tbl, t2);

  return mk_arith_term(__yices_globals.manager, b);
}


/*
 * Compute the square of t1
 */
EXPORTED term_t yices_square(term_t t1) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_square(t1));
}

term_t _o_yices_square(term_t t1) {
  rba_buffer_t *b;
  term_table_t *tbl;

  if (! check_good_term(__yices_globals.manager, t1) ||
      ! check_arith_term(__yices_globals.manager, t1) ||
      ! check_square_degree(__yices_globals.manager, t1)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  reset_rba_buffer(b);
  rba_buffer_add_term(b, tbl, t1);
  rba_buffer_mul_term(b, tbl, t1);

  return mk_arith_term(__yices_globals.manager, b);
}


/*
 * Compute t1 ^ d
 */
EXPORTED term_t yices_power(term_t t1, uint32_t d) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_power(t1, d));
}

term_t _o_yices_power(term_t t1, uint32_t d) {
  rba_buffer_t *b;
  term_table_t *tbl;

  if (! check_good_term(__yices_globals.manager, t1) ||
      ! check_arith_term(__yices_globals.manager, t1) ||
      ! check_power_degree(__yices_globals.manager, t1, d)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  rba_buffer_set_one(b);
  rba_buffer_mul_term_power(b, tbl, t1, d);

  return mk_arith_term(__yices_globals.manager, b);
}


/*
 * Sum of n terms t[0] ... t[n-1]
 */
EXPORTED term_t yices_sum(uint32_t n, const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_sum(n, t));
}

term_t _o_yices_sum(uint32_t n, const term_t t[]) {
  rba_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_arithmetic_args(__yices_globals.manager, n, t)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  reset_rba_buffer(b);
  for (i=0; i<n; i++) {
    rba_buffer_add_term(b, tbl, t[i]);
  }

  return mk_arith_term(__yices_globals.manager, b);
}


/*
 * Product of n terms t[0] ... t[n-1]
 */
EXPORTED term_t yices_product(uint32_t n, const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_product(n, t));
}

term_t _o_yices_product(uint32_t n, const term_t t[]) {
  rba_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_arithmetic_args(__yices_globals.manager, n, t)) {
    return NULL_TERM;
  }

  /*
   * Check whether one of t[i] is zero.  We must do this first
   * otherwise the degree computation won't be correct.
   */
  for (i=0; i<n; i++) {
    if (t[i] == zero_term) {
      return zero_term;
    }
  }

  if (! check_multi_prod_degree(__yices_globals.manager, n, t)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  rba_buffer_set_one(b);
  for (i=0; i<n; i++) {
    rba_buffer_mul_term(b, tbl, t[i]);
  }

  return mk_arith_term(__yices_globals.manager, b);
}




/*
 * DIVISION
 */
EXPORTED term_t yices_division(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_division(t1, t2));
}

term_t _o_yices_division(term_t t1, term_t t2) {
  if (! check_good_term(__yices_globals.manager, t1) ||
      ! check_good_term(__yices_globals.manager, t2) ||
      ! check_arith_term(__yices_globals.manager, t1) ||
      ! check_arith_term(__yices_globals.manager, t2)) {
    return NULL_TERM;
  }

  return mk_arith_rdiv(__yices_globals.manager, t1, t2);
}



/***************************
 *  DIV/MOD AND RELATIVES  *
 **************************/

EXPORTED term_t yices_idiv(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_idiv(t1, t2));
}

term_t _o_yices_idiv(term_t t1, term_t t2) {
  if (! check_good_term(__yices_globals.manager, t1) ||
      ! check_good_term(__yices_globals.manager, t2) ||
      ! check_arith_term(__yices_globals.manager, t1) ||
      ! check_arith_term(__yices_globals.manager, t2)) {
    return NULL_TERM;
  }

  return mk_arith_idiv(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_imod(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_imod(t1, t2));
}

term_t _o_yices_imod(term_t t1, term_t t2) {
  if (! check_good_term(__yices_globals.manager, t1) ||
      ! check_good_term(__yices_globals.manager, t2) ||
      ! check_arith_term(__yices_globals.manager, t1) ||
      ! check_arith_term(__yices_globals.manager, t2)) {
    return NULL_TERM;
  }

  return mk_arith_mod(__yices_globals.manager, t1, t2);
}

/*
 * Divisibility test: check whether t1 divides t2
 */
EXPORTED term_t yices_divides_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_divides_atom(t1, t2));
}

term_t _o_yices_divides_atom(term_t t1, term_t t2) {
  if (! check_good_term(__yices_globals.manager, t1) ||
      ! check_good_term(__yices_globals.manager, t2) ||
      ! check_arith_constant(__yices_globals.manager, t1) ||
      ! check_arith_term(__yices_globals.manager, t2)) {
    return NULL_TERM;
  }

  return mk_arith_divides(__yices_globals.manager, t1, t2);
}

/*
 * Integer test
 */
EXPORTED term_t yices_is_int_atom(term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_is_int_atom(t));
}

term_t _o_yices_is_int_atom(term_t t) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_arith_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }

  return mk_arith_is_int(__yices_globals.manager, t);
}


/*
 * ABS/FLOOR/CEIL
 */
EXPORTED term_t yices_abs(term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_abs(t));
}

term_t _o_yices_abs(term_t t) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_arith_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }

  return mk_arith_abs(__yices_globals.manager, t);
}

EXPORTED term_t yices_floor(term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_floor(t));
}

term_t _o_yices_floor(term_t t) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_arith_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }

  return mk_arith_floor(__yices_globals.manager, t);
}

EXPORTED term_t yices_ceil(term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_ceil(t));
}

term_t _o_yices_ceil(term_t t) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_arith_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }

  return mk_arith_ceil(__yices_globals.manager, t);
}


/*******************
 *   POLYNOMIALS   *
 ******************/

/*
 * integer coefficients
 */
EXPORTED term_t yices_poly_int32(uint32_t n, const int32_t a[], const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_poly_int32(n, a, t));
}

term_t _o_yices_poly_int32(uint32_t n, const int32_t a[], const term_t t[]) {
  rba_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_arithmetic_args(__yices_globals.manager, n, t)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  reset_rba_buffer(b);
  for (i=0; i<n; i++) {
    q_set32(&r0, a[i]);
    rba_buffer_add_const_times_term(b, tbl, &r0, t[i]);
  }

  return mk_arith_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_poly_int64(uint32_t n, const int64_t a[], const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_poly_int64(n, a, t));
}

term_t _o_yices_poly_int64(uint32_t n, const int64_t a[], const term_t t[]) {

  rba_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_arithmetic_args(__yices_globals.manager, n, t)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  reset_rba_buffer(b);
  for (i=0; i<n; i++) {
    q_set64(&r0, a[i]);
    rba_buffer_add_const_times_term(b, tbl, &r0, t[i]);
  }

  return mk_arith_term(__yices_globals.manager, b);
}


/*
 * Polynomial with rational coefficients
 * - den, num, and t must be arrays of size n
 * - the coefficient a_i is num[i]/den[i]
 *
 * Error report:
 * if den[i] is 0
 *   code = DIVISION_BY_ZERO
 */
EXPORTED term_t yices_poly_rational32(uint32_t n, const int32_t num[], const uint32_t den[], const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_poly_rational32(n, num, den, t));
}

term_t _o_yices_poly_rational32(uint32_t n, const int32_t num[], const uint32_t den[], const term_t t[]) {
  rba_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_arithmetic_args(__yices_globals.manager, n, t) ||
      ! check_denominators32(n, den)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  reset_rba_buffer(b);
  for (i=0; i<n; i++) {
    q_set_int32(&r0, num[i], den[i]);
    rba_buffer_add_const_times_term(b, tbl, &r0, t[i]);
  }

  return mk_arith_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_poly_rational64(uint32_t n, const int64_t num[], const uint64_t den[], const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_poly_rational64(n, num, den, t));
}

term_t _o_yices_poly_rational64(uint32_t n, const int64_t num[], const uint64_t den[], const term_t t[]) {
  rba_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_arithmetic_args(__yices_globals.manager, n, t) ||
      ! check_denominators64(n, den)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  reset_rba_buffer(b);
  for (i=0; i<n; i++) {
    q_set_int64(&r0, num[i], den[i]);
    rba_buffer_add_const_times_term(b, tbl, &r0, t[i]);
  }

  return mk_arith_term(__yices_globals.manager, b);
}


/*
 * GMP integers and rationals
 */
EXPORTED term_t yices_poly_mpz(uint32_t n, const mpz_t z[], const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_poly_mpz(n, z, t));
}

term_t _o_yices_poly_mpz(uint32_t n, const mpz_t z[], const term_t t[]) {
  rba_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_arithmetic_args(__yices_globals.manager, n, t)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  reset_rba_buffer(b);
  for (i=0; i<n; i++) {
    q_set_mpz(&r0, z[i]);
    rba_buffer_add_const_times_term(b, tbl, &r0, t[i]);
  }

  q_clear(&r0);

  return mk_arith_term(__yices_globals.manager, b);
}



EXPORTED term_t yices_poly_mpq(uint32_t n, const mpq_t q[], const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_poly_mpq(n, q, t));
}

term_t _o_yices_poly_mpq(uint32_t n, const mpq_t q[], const term_t t[]) {
  rba_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_arithmetic_args(__yices_globals.manager, n, t)) {
    return NULL_TERM;
  }

  b = get_arith_buffer();
  tbl = __yices_globals.terms;
  reset_rba_buffer(b);
  for (i=0; i<n; i++) {
    q_set_mpq(&r0, q[i]);
    rba_buffer_add_const_times_term(b, tbl, &r0, t[i]);
  }

  q_clear(&r0);

  return mk_arith_term(__yices_globals.manager, b);
}






/**********************
 *  ARITHMETIC ATOMS  *
 *********************/

EXPORTED term_t yices_arith_eq_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_arith_eq_atom(t1, t2));
}

term_t _o_yices_arith_eq_atom(term_t t1, term_t t2) {
  if (! check_both_arith_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_arith_eq(__yices_globals.manager, t1, t2);
}

EXPORTED term_t yices_arith_neq_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_arith_neq_atom(t1, t2));
}

term_t _o_yices_arith_neq_atom(term_t t1, term_t t2) {
  if (! check_both_arith_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_arith_neq(__yices_globals.manager, t1, t2);
}

EXPORTED term_t yices_arith_geq_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_arith_geq_atom(t1, t2));
}

term_t _o_yices_arith_geq_atom(term_t t1, term_t t2) {
  if (! check_both_arith_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_arith_geq(__yices_globals.manager, t1, t2);
}

EXPORTED term_t yices_arith_lt_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_arith_lt_atom(t1, t2));
}

term_t _o_yices_arith_lt_atom(term_t t1, term_t t2) {
  if (! check_both_arith_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_arith_lt(__yices_globals.manager, t1, t2);
}

EXPORTED term_t yices_arith_gt_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_arith_gt_atom(t1, t2));
}

term_t _o_yices_arith_gt_atom(term_t t1, term_t t2) {
  if (! check_both_arith_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_arith_gt(__yices_globals.manager, t1, t2);
}

EXPORTED term_t yices_arith_leq_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_arith_leq_atom(t1, t2));
}

term_t _o_yices_arith_leq_atom(term_t t1, term_t t2) {
  if (! check_both_arith_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_arith_leq(__yices_globals.manager, t1, t2);
}


/*
 * Comparison with zero
 */
EXPORTED term_t yices_arith_eq0_atom(term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_arith_eq0_atom(t));
}

term_t _o_yices_arith_eq0_atom(term_t t) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_arith_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }
  return mk_arith_term_eq0(__yices_globals.manager, t);
}

EXPORTED term_t yices_arith_neq0_atom(term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_arith_neq0_atom(t));
}

term_t _o_yices_arith_neq0_atom(term_t t) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_arith_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }
  return mk_arith_term_neq0(__yices_globals.manager, t);
}

EXPORTED term_t yices_arith_geq0_atom(term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_arith_geq0_atom(t));
}

term_t _o_yices_arith_geq0_atom(term_t t) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_arith_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }
  return mk_arith_term_geq0(__yices_globals.manager, t);
}

EXPORTED term_t yices_arith_leq0_atom(term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_arith_leq0_atom(t));
}

term_t _o_yices_arith_leq0_atom(term_t t) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_arith_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }
  return mk_arith_term_leq0(__yices_globals.manager, t);
}

EXPORTED term_t yices_arith_gt0_atom(term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_arith_gt0_atom(t));
}

term_t _o_yices_arith_gt0_atom(term_t t) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_arith_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }
  return mk_arith_term_gt0(__yices_globals.manager, t);
}

EXPORTED term_t yices_arith_lt0_atom(term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_arith_lt0_atom(t));
}

term_t _o_yices_arith_lt0_atom(term_t t) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_arith_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }
  return mk_arith_term_lt0(__yices_globals.manager, t);
}



/**************************
 *  BITVECTOR CONSTANTS   *
 *************************/

EXPORTED term_t yices_bvconst_uint32(uint32_t n, uint32_t x) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvconst_uint32(n,x));
}

term_t _o_yices_bvconst_uint32(uint32_t n, uint32_t x) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set32(bv0.data, bv0.width, x);

  return mk_bv_constant(__yices_globals.manager, &bv0);
}

EXPORTED term_t yices_bvconst_uint64(uint32_t n, uint64_t x) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvconst_uint64(n,x));
}

term_t _o_yices_bvconst_uint64(uint32_t n, uint64_t x) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set64(bv0.data, bv0.width, x);

  return mk_bv_constant(__yices_globals.manager, &bv0);
}

EXPORTED term_t yices_bvconst_int32(uint32_t n, int32_t x) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvconst_int32(n,x));
}

term_t _o_yices_bvconst_int32(uint32_t n, int32_t x) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set32_signed(bv0.data, bv0.width, x);

  return mk_bv_constant(__yices_globals.manager, &bv0);
}

EXPORTED term_t yices_bvconst_int64(uint32_t n, int64_t x) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvconst_int64(n,x));
}

term_t _o_yices_bvconst_int64(uint32_t n, int64_t x) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set64_signed(bv0.data, bv0.width, x);

  return mk_bv_constant(__yices_globals.manager, &bv0);
}

EXPORTED term_t yices_bvconst_mpz(uint32_t n, const mpz_t x) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvconst_mpz(n,x));
}

term_t _o_yices_bvconst_mpz(uint32_t n, const mpz_t x) {
  mpz_t aux;

  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  /*
   * bvconst_set_mpz requires x>=0
   * for sign-extend, we copy |x| into aux
   * copy aux into bv0 then negate bv0
   */
  bvconstant_set_bitsize(&bv0, n);
  if (mpz_sgn(x) >= 0) {
    bvconst_set_mpz(bv0.data, bv0.width, x);
  } else {
    mpz_init_set(aux, x);
    mpz_abs(aux, aux);
    bvconst_set_mpz(bv0.data, bv0.width, aux);
    bvconst_negate(bv0.data, bv0.width);
    mpz_clear(aux);
  }

  return mk_bv_constant(__yices_globals.manager, &bv0);
}


/*
 * bvconst_zero: set all bits to 0
 * bvconst_one: set low-order bit to 1, all the others to 0
 * bvconst_minus_one: set all bits to 1
 */
EXPORTED term_t yices_bvconst_zero(uint32_t n) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvconst_zero(n));
}

term_t _o_yices_bvconst_zero(uint32_t n) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_all_zero(&bv0, n);

  return mk_bv_constant(__yices_globals.manager, &bv0);
}

EXPORTED term_t yices_bvconst_one(uint32_t n) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvconst_one(n));
}

term_t _o_yices_bvconst_one(uint32_t n) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set_one(bv0.data, bv0.width);

  return mk_bv_constant(__yices_globals.manager, &bv0);
}

EXPORTED term_t yices_bvconst_minus_one(uint32_t n) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvconst_minus_one(n));
}

term_t _o_yices_bvconst_minus_one(uint32_t n) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_all_one(&bv0, n);

  return mk_bv_constant(__yices_globals.manager, &bv0);
}


/*
 * Convert an integer array to a bit constant
 * - a[i] =  0 --> bit i = 0
 * - a[i] != 0 --> bit i = 1
 */
EXPORTED term_t yices_bvconst_from_array(uint32_t n, const int32_t a[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvconst_from_array(n,a));
}

term_t _o_yices_bvconst_from_array(uint32_t n, const int32_t a[]) {
  if (!check_positive(n) || !check_maxbvsize(n)) {
    return NULL_TERM;
  }

  bvconstant_set_bitsize(&bv0, n);
  bvconst_set_array(bv0.data, a, n);

  return mk_bv_constant(__yices_globals.manager, &bv0);
}



/*
 * Parse a string of '0' and '1' and convert to a bit constant
 * - the number of bits is the length of s
 * - the string is read in big-endian format: the first character
 *   is the high-order bit.
 */
EXPORTED term_t yices_parse_bvbin(const char *s) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_parse_bvbin(s));
}

term_t _o_yices_parse_bvbin(const char *s) {
  size_t len;
  uint32_t n;
  int32_t code;

  len = strlen(s);
  if (len == 0) {
    set_error_code(INVALID_BVBIN_FORMAT);
    return NULL_TERM;
  }

  if (len > YICES_MAX_BVSIZE) {
    error_report_t *error = get_yices_error();
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = len;
    return NULL_TERM;
  }

  n = (uint32_t) len;
  bvconstant_set_bitsize(&bv0, n);
  code = bvconst_set_from_string(bv0.data, n, s);
  if (code < 0) {
    set_error_code(INVALID_BVBIN_FORMAT);
    return NULL_TERM;
  }

  return mk_bv_constant(__yices_globals.manager, &bv0);
}


/*
 * Parse a string of hexadecimal digits and convert it to a bit constant
 * - return NULL_TERM if there's a format error
 * - the number of bits is four times the length of s
 * - the string is read in big-endian format (the first character defines
 *   the four high-order bits).
 */
EXPORTED term_t yices_parse_bvhex(const char *s) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_parse_bvhex(s));
}

term_t _o_yices_parse_bvhex(const char *s) {
  size_t len;
  uint32_t n;
  int32_t code;

  len = strlen(s);
  if (len == 0) {
    set_error_code(INVALID_BVHEX_FORMAT);
    return NULL_TERM;
  }

  if (len > YICES_MAX_BVSIZE/4) {
    error_report_t *error = get_yices_error();
    error->code = MAX_BVSIZE_EXCEEDED;

    // badval is int64_t. It could overflow or get negative here
    // if s is a giant string.  We ignore this issue, since it's
    // only for information.
    error->badval = ((uint64_t) len) * 4;
    return NULL_TERM;
  }

  n = (uint32_t) len;
  bvconstant_set_bitsize(&bv0, 4 * n);
  code = bvconst_set_from_hexa_string(bv0.data, n, s);
  if (code < 0) {
    set_error_code(INVALID_BVHEX_FORMAT);
    return NULL_TERM;
  }

  return mk_bv_constant(__yices_globals.manager, &bv0);
}



/***************************
 *  BIT-VECTOR ARITHMETIC  *
 ***************************/

/*
 * Every operation: add/sub/neg/mul/square has two variants
 * - one for bitvectors of small size (1 to 64 bits)
 * - one for bitvectors of more than 64 bits
 */
term_t mk_bvadd64(term_t t1, term_t t2) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith64_buffer();
  tbl = __yices_globals.terms;
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_add_term(b, tbl, t2);

  return mk_bvarith64_term(__yices_globals.manager, b);
}

term_t mk_bvadd(term_t t1, term_t t2) {
  bvarith_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith_buffer();
  tbl = __yices_globals.terms;
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_add_term(b, tbl, t2);

  return mk_bvarith_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvadd(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvadd(t1, t2));
}

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


term_t mk_bvsub64(term_t t1, term_t t2) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith64_buffer();
  tbl = __yices_globals.terms;
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_sub_term(b, tbl, t2);

  return mk_bvarith64_term(__yices_globals.manager, b);
}

term_t mk_bvsub(term_t t1, term_t t2) {
  bvarith_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith_buffer();
  tbl = __yices_globals.terms;
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_sub_term(b, tbl, t2);

  return mk_bvarith_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvsub(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvsub(t1, t2));
}

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


term_t mk_bvneg64(term_t t1) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith64_buffer();
  tbl = __yices_globals.terms;
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_negate(b);

  return mk_bvarith64_term(__yices_globals.manager, b);
}

term_t mk_bvneg(term_t t1) {
  bvarith_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith_buffer();
  tbl = __yices_globals.terms;
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_negate(b);

  return mk_bvarith_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvneg(term_t t1) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvneg(t1));
}

term_t _o_yices_bvneg(term_t t1) {
  if (! check_good_term(__yices_globals.manager, t1) ||
      ! check_bitvector_term(__yices_globals.manager, t1)) {
    return NULL_TERM;
  }

  if (term_bitsize(__yices_globals.terms, t1) <= 64) {
    return mk_bvneg64(t1);
  } else {
    return mk_bvneg(t1);
  }
}


term_t mk_bvmul64(term_t t1, term_t t2) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith64_buffer();
  tbl = __yices_globals.terms;
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_mul_term(b, tbl, t2);

  return mk_bvarith64_term(__yices_globals.manager, b);
}

term_t mk_bvmul(term_t t1, term_t t2) {
  bvarith_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith_buffer();
  tbl = __yices_globals.terms;
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_mul_term(b, tbl, t2);

  return mk_bvarith_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvmul(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvmul(t1, t2));
}

term_t _o_yices_bvmul(term_t t1, term_t t2) {
  /*
   * check_product_degree may overestimate the degree of the product
   * (since the product of the coefficients of the leading terms in t1
   * and t2 are could be zero).  We can't really do much about this,
   * because the bvarith_buffers can't represent the intermediate terms.
   */
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2) ||
      ! check_product_degree(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  if (term_bitsize(__yices_globals.terms, t1) <= 64) {
    return mk_bvmul64(t1, t2);
  } else {
    return mk_bvmul(t1, t2);
  }
}


static term_t mk_bvsquare64(term_t t1) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith64_buffer();
  tbl = __yices_globals.terms;
  bvarith64_buffer_set_term(b, tbl, t1);
  bvarith64_buffer_square(b);

  return mk_bvarith64_term(__yices_globals.manager, b);
}

static term_t mk_bvsquare(term_t t1) {
  bvarith_buffer_t *b;
  term_table_t *tbl;

  b = get_bvarith_buffer();
  tbl = __yices_globals.terms;
  bvarith_buffer_set_term(b, tbl, t1);
  bvarith_buffer_square(b);

  return mk_bvarith_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvsquare(term_t t1) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvsquare(t1));
}

term_t _o_yices_bvsquare(term_t t1) {
  /*
   * check_square_degree may overestimate the degree of the product
   * but we ignore this issue for now. (cf. yices_bvmul)
   */
  if (! check_good_term(__yices_globals.manager, t1) ||
      ! check_bitvector_term(__yices_globals.manager, t1) ||
      ! check_square_degree(__yices_globals.manager, t1)) {
    return NULL_TERM;
  }

  if (term_bitsize(__yices_globals.terms, t1) <= 64) {
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
  tbl = __yices_globals.terms;
  n = term_bitsize(tbl, t1);
  bvarith64_buffer_prepare(b, n);
  bvarith64_buffer_set_one(b);
  bvarith64_buffer_mul_term_power(b, tbl, t1, d);

  return mk_bvarith64_term(__yices_globals.manager, b);
}

static term_t mk_bvpower(term_t t1, uint32_t d) {
  bvarith_buffer_t *b;
  term_table_t *tbl;
  uint32_t n;

  b = get_bvarith_buffer();
  tbl = __yices_globals.terms;
  n = term_bitsize(tbl, t1);
  bvarith_buffer_prepare(b, n);
  bvarith_buffer_set_one(b);
  bvarith_buffer_mul_term_power(b, tbl, t1, d);

  return mk_bvarith_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvpower(term_t t1, uint32_t d) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvpower(t1, d));
}

term_t _o_yices_bvpower(term_t t1, uint32_t d) {
  /*
   * check_power_degree may overestimate the degree of (t1^d)
   * but we ignore this for now (cf. yices_bvmul).
   */
  if (! check_good_term(__yices_globals.manager, t1) ||
      ! check_bitvector_term(__yices_globals.manager, t1) ||
      ! check_power_degree(__yices_globals.manager, t1, d)) {
    return NULL_TERM;
  }

  if (term_bitsize(__yices_globals.terms, t1) <= 64) {
    return mk_bvpower64(t1, d);
  } else {
    return mk_bvpower(t1, d);
  }
}


/************************************
 *  N-ARY BIT-VECTOR SUMS/PRODUCTS  *
 ***********************************/

static term_t mk_bvsum64(uint32_t n, const term_t t[]) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  b = get_bvarith64_buffer();
  tbl = __yices_globals.terms;
  bvarith64_buffer_set_term(b, tbl, t[0]);
  for (i=1; i<n; i++) {
    bvarith64_buffer_add_term(b, tbl, t[i]);
  }

  return mk_bvarith64_term(__yices_globals.manager, b);
}

static term_t mk_bvsum(uint32_t n, const term_t t[]) {
  bvarith_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  b = get_bvarith_buffer();
  tbl = __yices_globals.terms;
  bvarith_buffer_set_term(b, tbl, t[0]);
  for (i=1; i<n; i++) {
    bvarith_buffer_add_term(b, tbl, t[i]);
  }

  return mk_bvarith_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvsum(uint32_t n, const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvsum(n,t));
}

term_t _o_yices_bvsum(uint32_t n, const term_t t[]) {
  if (! check_positive(n) ||
      ! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_bitvector_args(__yices_globals.manager, n, t) ||
      ! check_same_type(__yices_globals.manager, n, t)) {
    return NULL_TERM;
  }

  if (term_bitsize(__yices_globals.terms, t[0]) <= 64) {
    return mk_bvsum64(n, t);
  } else {
    return mk_bvsum(n, t);
  }
}


static term_t mk_bvproduct64(uint32_t n, const term_t t[]) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  b = get_bvarith64_buffer();
  tbl = __yices_globals.terms;
  bvarith64_buffer_set_term(b, tbl, t[0]);
  for (i=1; i<n; i++) {
    bvarith64_buffer_mul_term(b, tbl, t[i]);
  }

  return mk_bvarith64_term(__yices_globals.manager, b);
}

static term_t mk_bvproduct(uint32_t n, const term_t t[]) {
  bvarith_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  b = get_bvarith_buffer();
  tbl = __yices_globals.terms;
  bvarith_buffer_set_term(b, tbl, t[0]);
  for (i=1; i<n; i++) {
    bvarith_buffer_mul_term(b, tbl, t[i]);
  }

  return mk_bvarith_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvproduct(uint32_t n, const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvproduct(n,t));
}

term_t _o_yices_bvproduct(uint32_t n, const term_t t[]) {
  uint32_t i;

  if (! check_positive(n) ||
      ! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_bitvector_args(__yices_globals.manager, n, t) ||
      ! check_same_type(__yices_globals.manager, n, t)) {
    return NULL_TERM;
  }

  // check whether one t[i] is zero before checking degrees
  for (i=0; i<n; i++) {
    if (bvterm_is_zero(__yices_globals.terms, t[i])) {
      return t[i];
    }
  }

  if (! check_multi_prod_degree(__yices_globals.manager, n, t)) {
    /*
     * check_multi_prod_degree may overestimate  the actual degree but
     * a bvarith_buffer/bvarith64_buffer can't  store the intermediate
     * results  even  if  the  final   result  has  degree  less  than
     * MAX_DEGREE.
     */
    return NULL_TERM;
  }

  if (term_bitsize(__yices_globals.terms, t[0]) <= 64) {
    return mk_bvproduct64(n, t);
  } else {
    return mk_bvproduct(n, t);
  }

}



/***********************************
 *  BITWISE BIT-VECTOR OPERATIONS  *
 **********************************/


EXPORTED term_t yices_bvnot(term_t t1) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvnot(t1));
}

term_t _o_yices_bvnot(term_t t1) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_good_term(__yices_globals.manager, t1) ||
      ! check_bitvector_term(__yices_globals.manager, t1)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = __yices_globals.terms;
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_not(b);

  return mk_bvlogic_term(__yices_globals.manager, b);
}



EXPORTED term_t yices_bvnand(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvnand(t1, t2));
}

term_t _o_yices_bvnand(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = __yices_globals.terms;
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_and_term(b, tbl, t2);
  bvlogic_buffer_not(b);

  return mk_bvlogic_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvnor(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvnor(t1, t2));
}

term_t _o_yices_bvnor(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = __yices_globals.terms;
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_or_term(b, tbl, t2);
  bvlogic_buffer_not(b);

  return mk_bvlogic_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvxnor(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvxnor(t1, t2));
}

term_t _o_yices_bvxnor(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = __yices_globals.terms;
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_xor_term(b, tbl, t2);
  bvlogic_buffer_not(b);

  return mk_bvlogic_term(__yices_globals.manager, b);
}


/************************************
 *  ASSOCIATIVE BITWISE OPERATIONS  *
 ***********************************/

EXPORTED term_t yices_bvand(uint32_t n, const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvand(n, t));
}

term_t _o_yices_bvand(uint32_t n, const term_t t[]) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_positive(n) ||
      ! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_bitvector_args(__yices_globals.manager, n, t) ||
      ! check_same_type(__yices_globals.manager, n, t)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = __yices_globals.terms;
  bvlogic_buffer_set_term(b, tbl, t[0]);
  for (i=1; i<n; i++) {
    bvlogic_buffer_and_term(b, tbl, t[i]);
  }

  return mk_bvlogic_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvor(uint32_t n, const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvor(n, t));
}

term_t _o_yices_bvor(uint32_t n, const term_t t[]) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_positive(n) ||
      ! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_bitvector_args(__yices_globals.manager, n, t) ||
      ! check_same_type(__yices_globals.manager, n, t)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = __yices_globals.terms;
  bvlogic_buffer_set_term(b, tbl, t[0]);
  for (i=1; i<n; i++) {
    bvlogic_buffer_or_term(b, tbl, t[i]);
  }

  return mk_bvlogic_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvxor(uint32_t n, const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvxor(n, t));
}

term_t _o_yices_bvxor(uint32_t n, const term_t t[]) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  if (! check_positive(n) ||
      ! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_bitvector_args(__yices_globals.manager, n, t) ||
      ! check_same_type(__yices_globals.manager, n, t)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = __yices_globals.terms;
  bvlogic_buffer_set_term(b, tbl, t[0]);
  for (i=1; i<n; i++) {
    bvlogic_buffer_xor_term(b, tbl, t[i]);
  }

  return mk_bvlogic_term(__yices_globals.manager, b);
}


EXPORTED term_t yices_bvand2(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvand2(t1, t2));
}

term_t _o_yices_bvand2(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = __yices_globals.terms;
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_and_term(b, tbl, t2);

  return mk_bvlogic_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvor2(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvor2(t1, t2));
}

term_t _o_yices_bvor2(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = __yices_globals.terms;
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_or_term(b, tbl, t2);

  return mk_bvlogic_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_bvxor2(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvxor2(t1,t2));
}

term_t _o_yices_bvxor2(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = __yices_globals.terms;
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_xor_term(b, tbl, t2);

  return mk_bvlogic_term(__yices_globals.manager, b);
}


EXPORTED term_t yices_bvand3(term_t t1, term_t t2, term_t t3) {
  term_t aux[3];

  aux[0] = t1;
  aux[1] = t2;
  aux[2] = t3;

  return yices_bvand(3, aux);
}

EXPORTED term_t yices_bvor3(term_t t1, term_t t2, term_t t3) {
  term_t aux[3];

  aux[0] = t1;
  aux[1] = t2;
  aux[2] = t3;

  return yices_bvor(3, aux);
}

EXPORTED term_t yices_bvxor3(term_t t1, term_t t2, term_t t3) {
  term_t aux[3];

  aux[0] = t1;
  aux[1] = t2;
  aux[2] = t3;

  return yices_bvor(3, aux);
}




/*********************************************
 *   BITVECTOR SHIFT/ROTATION BY A CONSTANT  *
 ********************************************/

/*
 * Shift or rotation by an integer constant n
 * - shift_left0 sets the low-order bits to zero
 * - shift_left1 sets the low-order bits to one
 * - shift_right0 sets the high-order bits to zero
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
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_shift_left0(t, n));
}

term_t _o_yices_shift_left0(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = __yices_globals.terms;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_shift_left0(b, n);

  return mk_bvlogic_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_shift_left1(term_t t, uint32_t n) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_shift_left1(t, n));
}

term_t _o_yices_shift_left1(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = __yices_globals.terms;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_shift_left1(b, n);

  return mk_bvlogic_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_shift_right0(term_t t, uint32_t n) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_shift_right0(t, n));
}

term_t _o_yices_shift_right0(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = __yices_globals.terms;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_shift_right0(b, n);

  return mk_bvlogic_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_shift_right1(term_t t, uint32_t n) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_shift_right1(t, n));
}

term_t _o_yices_shift_right1(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = __yices_globals.terms;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_shift_right1(b, n);

  return mk_bvlogic_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_ashift_right(term_t t, uint32_t n) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_ashift_right(t, n));
}

term_t _o_yices_ashift_right(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = __yices_globals.terms;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_ashift_right(b, n);

  return mk_bvlogic_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_rotate_left(term_t t, uint32_t n) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_rotate_left(t, n));
}

term_t _o_yices_rotate_left(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = __yices_globals.terms;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  if (n < b->bitsize) {
    bvlogic_buffer_rotate_left(b, n);
  }

  return mk_bvlogic_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_rotate_right(term_t t, uint32_t n) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_rotate_right(t, n));
}

term_t _o_yices_rotate_right(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = __yices_globals.terms;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t) ||
      ! check_bitshift(n, term_bitsize(tbl, t))) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  if (n < b->bitsize) {
    bvlogic_buffer_rotate_right(b, n);
  }

  return mk_bvlogic_term(__yices_globals.manager, b);
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
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvextract(t, i, j));
}

term_t _o_yices_bvextract(term_t t, uint32_t i, uint32_t j) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;
  uint32_t n;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }

  tbl = __yices_globals.terms;
  n = term_bitsize(tbl, t);
  if (! check_bvextract(i, j, n)) {
    return NULL_TERM;
  }

  if (i == 0 && j == n-1) {
    return t;
  } else {
    b = get_bvlogic_buffer();
    bvlogic_buffer_set_slice_term(b, tbl, i, j, t);
    return mk_bvlogic_term(__yices_globals.manager, b);
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
EXPORTED term_t yices_bvconcat2(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvconcat2(t1, t2));
}

term_t _o_yices_bvconcat2(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  tbl = __yices_globals.terms;

  if (! check_good_term(__yices_globals.manager, t1) ||
      ! check_good_term(__yices_globals.manager, t2) ||
      ! check_bitvector_term(__yices_globals.manager, t1) ||
      ! check_bitvector_term(__yices_globals.manager, t2) ||
      ! check_maxbvsize(term_bitsize(tbl, t1) + term_bitsize(tbl, t2))) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t2);
  bvlogic_buffer_concat_left_term(b, tbl, t1);

  return mk_bvlogic_term(__yices_globals.manager, b);
}


/*
 * Generic form
 */
EXPORTED term_t yices_bvconcat(uint32_t n, const term_t t[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvconcat(n, t));
}

term_t _o_yices_bvconcat(uint32_t n, const term_t t[]) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;
  uint64_t bvsize;
  uint32_t i;

  if (! check_positive(n) ||
      ! check_good_terms(__yices_globals.manager, n, t) ||
      ! check_bitvector_args(__yices_globals.manager, n, t)) {
    return NULL_TERM;
  }

  tbl = __yices_globals.terms;
  bvsize = 0;
  for (i=0; i<n; i++) {
    bvsize += term_bitsize(tbl, t[i]);
  }
  if (bvsize > (uint64_t) YICES_MAX_BVSIZE) {
    error_report_t *error = get_yices_error();
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = bvsize;
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_clear(b);
  while (n>0) {
    n --;
    bvlogic_buffer_concat_left_term(b, tbl, t[n]);
  }

  return mk_bvlogic_term(__yices_globals.manager, b);
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
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvrepeat(t, n));
}

term_t _o_yices_bvrepeat(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;
  uint64_t m;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t) ||
      ! check_positive(n)) {
    return NULL_TERM;
  }

  // check size
  tbl = __yices_globals.terms;
  m = ((uint64_t) n) * term_bitsize(tbl, t);
  if (m > (uint64_t) YICES_MAX_BVSIZE) {
    error_report_t *error = get_yices_error();
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = m;
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_repeat_concat(b, n);

  return mk_bvlogic_term(__yices_globals.manager, b);
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
  MT_PROTECT(term_t,  __yices_globals.lock,_o_yices_sign_extend(t, n));
}

term_t _o_yices_sign_extend(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;
  uint64_t m;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }


  // check size
  tbl = __yices_globals.terms;
  m = ((uint64_t) n) + term_bitsize(tbl, t);
  if (m > (uint64_t) YICES_MAX_BVSIZE) {
    error_report_t *error = get_yices_error();
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = m;
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_sign_extend(b, b->bitsize + n);

  return mk_bvlogic_term(__yices_globals.manager, b);
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
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_zero_extend(t, n));
}

term_t _o_yices_zero_extend(term_t t, uint32_t n) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;
  uint64_t m;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }

  // check size
  tbl = __yices_globals.terms;
  m = ((uint64_t) n) + term_bitsize(tbl, t);
  if (m > (uint64_t) YICES_MAX_BVSIZE) {
    error_report_t *error = get_yices_error();
    error->code = MAX_BVSIZE_EXCEEDED;
    error->badval = m;
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_zero_extend(b, b->bitsize + n);

  return mk_bvlogic_term(__yices_globals.manager, b);
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
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_redand(t));
}

term_t _o_yices_redand(term_t t) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = __yices_globals.terms;
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_redand(b);

  return mk_bvlogic_term(__yices_globals.manager, b);
}

EXPORTED term_t yices_redor(term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_redor(t));
}

term_t _o_yices_redor(term_t t) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = __yices_globals.terms;
  bvlogic_buffer_set_term(b, tbl, t);
  bvlogic_buffer_redor(b);

  return mk_bvlogic_term(__yices_globals.manager, b);
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
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_redcomp(t1, t2));
}

term_t _o_yices_redcomp(term_t t1, term_t t2) {
  bvlogic_buffer_t *b;
  term_table_t *tbl;

  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  b = get_bvlogic_buffer();
  tbl = __yices_globals.terms;
  bvlogic_buffer_set_term(b, tbl, t1);
  bvlogic_buffer_comp_term(b, tbl, t2);

  return mk_bvlogic_term(__yices_globals.manager, b);
}




/*******************************
 *  GENERIC BIT-VECTOR SHIFTS  *
 *****************************/


EXPORTED term_t yices_bvshl(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvshl(t1, t2));
}

term_t _o_yices_bvshl(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  return mk_bvshl(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvlshr(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvlshr(t1, t2));
}

term_t _o_yices_bvlshr(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  return mk_bvlshr(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvashr(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvashr(t1, t2));
}

term_t _o_yices_bvashr(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }

  return mk_bvashr(__yices_globals.manager, t1, t2);
}





/**********************************
 *  BITVECTOR DIVISION OPERATORS  *
 *********************************/

EXPORTED term_t yices_bvdiv(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvdiv(t1, t2));
}

term_t _o_yices_bvdiv(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvdiv(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvrem(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvrem(t1,t2));
}

term_t _o_yices_bvrem(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvrem(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvsdiv(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock,  _o_yices_bvsdiv(t1, t2));
}

term_t _o_yices_bvsdiv(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsdiv(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvsrem(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvsrem(t1, t2));
}

term_t _o_yices_bvsrem(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsrem(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvsmod(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvsmod(t1, t2));
}

term_t _o_yices_bvsmod(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsmod(__yices_globals.manager, t1, t2);
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
EXPORTED term_t yices_bvarray(uint32_t n, const term_t arg[]) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvarray(n, arg));
}

term_t _o_yices_bvarray(uint32_t n, const term_t arg[]) {
  if (! check_positive(n) ||
      ! check_maxbvsize(n) ||
      ! check_good_terms(__yices_globals.manager, n, arg) ||
      ! check_boolean_args(__yices_globals.manager, n, arg)) {
    return NULL_TERM;
  }
  return mk_bvarray(__yices_globals.manager, n, arg);
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
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bitextract(t, i));
}

term_t _o_yices_bitextract(term_t t, uint32_t i) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t) ||
      ! check_bitextract(i, term_bitsize(__yices_globals.terms, t))) {
    return NULL_TERM;
  }
  return mk_bitextract(__yices_globals.manager, t, i);
}




/*********************
 *  BITVECTOR ATOMS  *
 ********************/

EXPORTED term_t yices_bveq_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bveq_atom(t1, t2));
}

term_t _o_yices_bveq_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bveq(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvneq_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvneq_atom(t1, t2));
}

term_t _o_yices_bvneq_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvneq(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvge_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvge_atom(t1, t2));
}

term_t _o_yices_bvge_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvge(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvgt_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvgt_atom(t1, t2));
}

term_t _o_yices_bvgt_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvgt(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvle_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvle_atom(t1, t2));
}

term_t _o_yices_bvle_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvle(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvlt_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock,  _o_yices_bvlt_atom(t1, t2));
}

term_t _o_yices_bvlt_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvlt(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvsge_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvsge_atom(t1, t2));
}

term_t _o_yices_bvsge_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsge(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvsgt_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvsgt_atom(t1, t2));
}

term_t _o_yices_bvsgt_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsgt(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvsle_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvsle_atom(t1, t2));
}

term_t _o_yices_bvsle_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvsle(__yices_globals.manager, t1, t2);
}


EXPORTED term_t yices_bvslt_atom(term_t t1, term_t t2) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_bvslt_atom(t1, t2));
}

term_t _o_yices_bvslt_atom(term_t t1, term_t t2) {
  if (! check_compatible_bv_terms(__yices_globals.manager, t1, t2)) {
    return NULL_TERM;
  }
  return mk_bvslt(__yices_globals.manager, t1, t2);
}



/*********************
 *  PRETTY PRINTING  *
 ********************/

/*
 * Pretty print type tau
 * - f = output file to use
 * - width, height, offset = print area
 */
EXPORTED int32_t yices_pp_type(FILE *f, type_t tau, uint32_t width, uint32_t height, uint32_t offset) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_pp_type(f, tau, width, height, offset));
}

int32_t _o_yices_pp_type(FILE *f, type_t tau, uint32_t width, uint32_t height, uint32_t offset) {
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
    file_output_error();
  }
  delete_yices_pp(&printer, false);

  return code;
}

EXPORTED int32_t yices_pp_type_fd(int fd, type_t tau, uint32_t width, uint32_t height, uint32_t offset) {
  FILE *tmp_fp;
  int32_t retval;

  tmp_fp = fd_2_tmp_fp(fd);
  if (tmp_fp == NULL) {
    file_output_error();
    return -1;
  }
  retval = yices_pp_type(tmp_fp, tau, width, height, offset);
  fclose(tmp_fp);

  return retval;
}



/*
 * Pretty print term t
 * - f = output file to use
 * - width, height, offset = print area
 */
EXPORTED int32_t yices_pp_term(FILE *f, term_t t, uint32_t width, uint32_t height, uint32_t offset) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_pp_term(f, t, width, height, offset));
}

int32_t _o_yices_pp_term(FILE *f, term_t t, uint32_t width, uint32_t height, uint32_t offset) {
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
    file_output_error();
  }
  delete_yices_pp(&printer, false);

  return code;
}

EXPORTED int32_t yices_pp_term_fd(int fd, term_t t, uint32_t width, uint32_t height, uint32_t offset) {
  FILE *tmp_fp;
  int32_t retval;

  tmp_fp = fd_2_tmp_fp(fd);
  if (tmp_fp == NULL) {
    file_output_error();
    return -1;
  }
  retval = yices_pp_term(tmp_fp, t, width, height, offset);
  fclose(tmp_fp);

  return retval;
}

/*
 * Pretty print terms a[0 ... n-1]
 * - f = output file to use
 * - width, height, offset = print area
 */
EXPORTED int32_t yices_pp_term_array(FILE *f, uint32_t n, const term_t a[], uint32_t width, uint32_t height, uint32_t offset, int32_t horiz) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_pp_term_array(f, n, a, width, height, offset, horiz));
}

int32_t _o_yices_pp_term_array(FILE *f, uint32_t n, const term_t a[], uint32_t width, uint32_t height, uint32_t offset, int32_t horiz) {
  yices_pp_t printer;
  pp_area_t area;
  int32_t code;
  uint32_t i;

  if (! check_good_terms(__yices_globals.manager, n, a)) {
    return -1;
  }

  if (width < 4) width = 4;
  if (height == 0) height = 1;

  area.width = width;
  area.height = height;
  area.offset = offset;
  area.stretch = false;
  area.truncate = true;

  if (horiz == 0) {
    init_default_yices_pp(&printer, f, &area); // default: PP_VMODE
  } else {
    init_yices_pp(&printer, f, &area, PP_HVMODE, 0); // horizontal/vertical mode
  }

  for (i=0; i<n; i++) {
    pp_term_full(&printer, __yices_globals.terms, a[i]);
  }
  flush_yices_pp(&printer);

  // check for error
  code = 0;
  if (yices_pp_print_failed(&printer)) {
    code = -1;
    errno = yices_pp_errno(&printer);
    file_output_error();
  }
  delete_yices_pp(&printer, false);

  return code;
}

EXPORTED int32_t yices_pp_term_array_fd(int fd, uint32_t n, const term_t a[], uint32_t width, uint32_t height, uint32_t offset, int32_t horiz) {
  FILE *tmp_fp;
  int32_t retval;

  tmp_fp = fd_2_tmp_fp(fd);
  if (tmp_fp == NULL) {
    file_output_error();
    return -1;
  }
  retval = yices_pp_term_array(tmp_fp, n, a, width, height, offset,  horiz);
  fclose(tmp_fp);

  return retval;
}



/*
 * Conversion to strings
 */
EXPORTED char *yices_type_to_string(type_t tau, uint32_t width, uint32_t height, uint32_t offset) {
  MT_PROTECT(char*,  __yices_globals.lock, _o_yices_type_to_string(tau, width, height, offset));
}

char *_o_yices_type_to_string(type_t tau, uint32_t width, uint32_t height, uint32_t offset) {
  yices_pp_t printer;
  pp_area_t area;
  char *str;
  uint32_t len;

  if (! check_good_type(__yices_globals.types, tau)) {
    return NULL;
  }

  if (width < 4) width = 4;
  if (height == 0) height = 1;

  area.width = width;
  area.height = height;
  area.offset = offset;
  area.stretch = false;
  area.truncate = true;

  init_default_yices_pp(&printer, NULL, &area);
  pp_type_exp(&printer, __yices_globals.types, tau);
  flush_yices_pp(&printer);

  str = yices_pp_get_string(&printer, &len);
  delete_yices_pp(&printer, false);

  return str;
}

EXPORTED char *yices_term_to_string(term_t t, uint32_t width, uint32_t height, uint32_t offset) {
  MT_PROTECT(char*,  __yices_globals.lock, _o_yices_term_to_string(t, width, height, offset));
}

char *_o_yices_term_to_string(term_t t, uint32_t width, uint32_t height, uint32_t offset) {
  yices_pp_t printer;
  pp_area_t area;
  char *str;
  uint32_t len;

  if (! check_good_term(__yices_globals.manager, t)) {
    return NULL;
  }

  if (width < 4) width = 4;
  if (height == 0) height = 1;

  area.width = width;
  area.height = height;
  area.offset = offset;
  area.stretch = false;
  area.truncate = true;

  init_default_yices_pp(&printer, NULL, &area);
  pp_term_full(&printer, __yices_globals.terms, t);
  flush_yices_pp(&printer);

  str = yices_pp_get_string(&printer, &len);
  delete_yices_pp(&printer, false);

  return str;
}


EXPORTED void yices_free_string(char *s) {
  safe_free(s);
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
EXPORTED int32_t yices_type_is_bool(type_t tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_type_is_bool(tau));
}

int32_t _o_yices_type_is_bool(type_t tau) {
  return check_good_type(__yices_globals.types, tau) && is_boolean_type(tau);
}

EXPORTED int32_t yices_type_is_int(type_t tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_type_is_int(tau));
}

int32_t _o_yices_type_is_int(type_t tau) {
  return check_good_type(__yices_globals.types, tau) && is_integer_type(tau);
}

EXPORTED int32_t yices_type_is_real(type_t tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_type_is_real(tau));
}

int32_t _o_yices_type_is_real(type_t tau) {
  return check_good_type(__yices_globals.types, tau) && is_real_type(tau);
}

EXPORTED int32_t yices_type_is_arithmetic(type_t tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_type_is_arithmetic(tau));
}

int32_t _o_yices_type_is_arithmetic(type_t tau) {
  return check_good_type(__yices_globals.types, tau) && is_arithmetic_type(tau);
}

EXPORTED int32_t yices_type_is_bitvector(type_t tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_type_is_bitvector(tau));
}

int32_t _o_yices_type_is_bitvector(type_t tau) {
  return check_good_type(__yices_globals.types, tau) && is_bv_type(__yices_globals.types, tau);
}

EXPORTED int32_t yices_type_is_tuple(type_t tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_type_is_tuple(tau));
}

int32_t _o_yices_type_is_tuple(type_t tau) {
  return check_good_type(__yices_globals.types, tau) && is_tuple_type(__yices_globals.types, tau);
}

EXPORTED int32_t yices_type_is_function(type_t tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_type_is_function(tau));
}

int32_t _o_yices_type_is_function(type_t tau) {
  return check_good_type(__yices_globals.types, tau) && is_function_type(__yices_globals.types, tau);
}

EXPORTED int32_t yices_type_is_scalar(type_t tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_type_is_scalar(tau));
}

int32_t _o_yices_type_is_scalar(type_t tau) {
  return check_good_type(__yices_globals.types, tau) && is_scalar_type(__yices_globals.types, tau);
}

EXPORTED int32_t yices_type_is_uninterpreted(type_t tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_type_is_uninterpreted(tau));
}

int32_t _o_yices_type_is_uninterpreted(type_t tau) {
  return check_good_type(__yices_globals.types, tau) && is_uninterpreted_type(__yices_globals.types, tau);
}


/*
 * Check whether tau is a subtype of sigma
 * - return 0 for false, 1 for true
 *
 * If tau or sigma is not a valid type, the function returns false
 * and sets the error report:
 *   code = INVALID_TYPE
 *   type1 = tau or sigma
 */
EXPORTED int32_t yices_test_subtype(type_t tau, type_t sigma) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_test_subtype(tau, sigma));
}

int32_t _o_yices_test_subtype(type_t tau, type_t sigma) {
  return check_good_type(__yices_globals.types, tau) && check_good_type(__yices_globals.types, sigma) && is_subtype(__yices_globals.types, tau, sigma);
}


/*
 * Check whether tau and sigma are compatible
 * - return 0 for false, 1 for true
 *
 * If tau or sigma is not a valid type, the function returns 0 and
 * Sets the error report:
 *   code = INVALID_TYPE
 *   type1 = tau or sigma
 */
EXPORTED int32_t yices_compatible_types(type_t tau, type_t sigma) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_compatible_types(tau, sigma));
}

int32_t _o_yices_compatible_types(type_t tau, type_t sigma) {
  return check_good_type(__yices_globals.types, tau) && check_good_type(__yices_globals.types, sigma)
    && compatible_types(__yices_globals.types, tau, sigma);
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
EXPORTED uint32_t yices_bvtype_size(type_t tau) {
  MT_PROTECT(uint32_t,  __yices_globals.lock, _o_yices_bvtype_size(tau));
}

uint32_t _o_yices_bvtype_size(type_t tau) {
  if (! check_good_type(__yices_globals.types, tau) ||
      ! check_bvtype(__yices_globals.types, tau)) {
    return 0;
  }
  return bv_type_size(__yices_globals.types, tau);
}


/*
 * Cardinality of a scalar type
 * - return 0 if there's an error
 */
EXPORTED uint32_t yices_scalar_type_card(type_t tau) {
  MT_PROTECT(uint32_t,  __yices_globals.lock, _o_yices_scalar_type_card(tau));
}

uint32_t _o_yices_scalar_type_card(type_t tau) {
  if (! check_good_type(__yices_globals.types, tau) ||
      ! check_scalar_type(__yices_globals.types, tau)) {
    return 0;
  }
  return scalar_type_cardinal(__yices_globals.types, tau);
}


/*
 * Number of children of type tau
 * - if tau is a tuple type (tuple tau_1 ... tau_n), returns n
 * - if tau is a function type (-> tau_1 ... tau_n sigma), returns n+1
 * - if tau is any other type, returns 0
 *
 * - returns -1 if tau is not a valid type
 *
 * Error report:
 * if tau is not a valid type
 *   code = INVALID_TYPE
 *   type1 = tau
 */
EXPORTED int32_t yices_type_num_children(type_t tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_type_num_children(tau));
}

int32_t _o_yices_type_num_children(type_t tau) {
  int32_t n;

  if (! check_good_type(__yices_globals.types, tau)) {
    return -1;
  }

  // it's safe to convert from unsigned to signed here
  // since YICES_MAX_ARITY is (UINT32_MAX/16)
  n = 0;
  if (is_tuple_type(__yices_globals.types, tau)) {
    n = tuple_type_arity(__yices_globals.types, tau);
  } else if (is_function_type(__yices_globals.types, tau)) {
    n = function_type_arity(__yices_globals.types, tau) + 1;
  }

  return n;
}


/*
 * Get the i-th child of type tau
 * - return NULL_TYPE if there's an error
 */
EXPORTED type_t yices_type_child(type_t tau, int32_t i) {
  MT_PROTECT(type_t,  __yices_globals.lock, _o_yices_type_child(tau, i));
}

type_t _o_yices_type_child(type_t tau, int32_t i) {
  tuple_type_t *tup;
  function_type_t *fun;

  if (! check_good_type(__yices_globals.types, tau)) {
    return NULL_TYPE;
  }

  if (i >= 0) {
    if (is_tuple_type(__yices_globals.types, tau)) {
      tup = tuple_type_desc(__yices_globals.types, tau);
      if (i < tup->nelem) {
	return tup->elem[i];
      }
    } else if (is_function_type(__yices_globals.types, tau)) {
      fun = function_type_desc(__yices_globals.types, tau);
      if (i < fun->ndom) {
	return fun->domain[i];
      } else if (i == fun->ndom) {
	return fun->range;
      }
    }
  } else {
    // bad index or atomic type
    set_error_code(INVALID_TYPE_OP);
  }
  return NULL_TYPE;
}



/*
 * Collect all the children in vector *v
 * - returns -1 for error, 0 if all fine.
 */
EXPORTED int32_t yices_type_children(type_t tau, type_vector_t *v) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_type_children(tau, v));
}

int32_t _o_yices_type_children(type_t tau, type_vector_t *v) {
  tuple_type_t *tup;
  function_type_t *fun;
  uint32_t i, n;

  if (! check_good_type(__yices_globals.types, tau)) {
    return -1;
  }

  v->size = 0;
  if (is_tuple_type(__yices_globals.types, tau)) {
    tup = tuple_type_desc(__yices_globals.types, tau);
    n = tup->nelem;
    for (i=0; i<n; i++) {
      type_vector_push(v, tup->elem[i]);
    }
  } else if (is_function_type(__yices_globals.types, tau)) {
    fun = function_type_desc(__yices_globals.types, tau);
    n = fun->ndom;
    for (i=0; i<n; i++) {
      type_vector_push(v, fun->domain[i]);
    }
    type_vector_push(v, fun->range);
  }

  return 0;
}




/***********************
 *  TERM EXPLORATION   *
 **********************/

/*
 * Get the type of term t
 * return NULL_TYPE if t is not a valid term
 * and set the error report:
 *   code = INVALID_TERM
 *   term1 = t
 *   index = -1
 */
EXPORTED type_t yices_type_of_term(term_t t) {
  MT_PROTECT(type_t,  __yices_globals.lock, _o_yices_type_of_term(t));
}

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
EXPORTED int32_t yices_term_is_bool(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_bool(t));
}

int32_t _o_yices_term_is_bool(term_t t) {
  return check_good_term(__yices_globals.manager, t) && is_boolean_term(__yices_globals.terms, t);
}

EXPORTED int32_t yices_term_is_int(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_int(t));
}

int32_t _o_yices_term_is_int(term_t t) {
  return check_good_term(__yices_globals.manager, t) && is_integer_term(__yices_globals.terms, t);
}

EXPORTED int32_t yices_term_is_real(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_real(t));
}

int32_t _o_yices_term_is_real(term_t t) {
  return check_good_term(__yices_globals.manager, t) && is_real_term(__yices_globals.terms, t);
}

EXPORTED int32_t yices_term_is_arithmetic(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_arithmetic(t));
}

int32_t _o_yices_term_is_arithmetic(term_t t) {
  return check_good_term(__yices_globals.manager, t) && is_arithmetic_term(__yices_globals.terms, t);
}

EXPORTED int32_t yices_term_is_bitvector(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_bitvector(t));
}

int32_t _o_yices_term_is_bitvector(term_t t) {
  return check_good_term(__yices_globals.manager, t) && is_bitvector_term(__yices_globals.terms, t);
}

EXPORTED int32_t yices_term_is_tuple(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_tuple(t));
}

int32_t _o_yices_term_is_tuple(term_t t) {
  return check_good_term(__yices_globals.manager, t) && is_tuple_term(__yices_globals.terms, t);
}

EXPORTED int32_t yices_term_is_function(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_function(t));
}

int32_t _o_yices_term_is_function(term_t t) {
  return check_good_term(__yices_globals.manager, t) && is_function_term(__yices_globals.terms, t);
}

EXPORTED int32_t yices_term_is_scalar(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_scalar(t));
}

int32_t _o_yices_term_is_scalar(term_t t) {
  term_table_t *tbl;

  tbl = __yices_globals.terms;
  return check_good_term(__yices_globals.manager, t) && (is_scalar_term(tbl, t) || is_utype_term(tbl, t));
}


/*
 * Size of bitvector term t.
 * return 0 if t is not a bitvector
 */
EXPORTED uint32_t yices_term_bitsize(term_t t) {
  MT_PROTECT(uint32_t,  __yices_globals.lock, _o_yices_term_bitsize(t));
}

uint32_t _o_yices_term_bitsize(term_t t) {
  if (! check_bitvector_term(__yices_globals.manager, t)) {
    return 0;
  }
  return term_bitsize(__yices_globals.terms, t);
}


/*
 * Check whether t is ground
 * - return false if t is not valid and set the error report
 */
EXPORTED int32_t yices_term_is_ground(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_ground(t));
}

int32_t _o_yices_term_is_ground(term_t t) {
  return check_good_term(__yices_globals.manager, t) && term_is_ground(get_fvars(), t);
}


/*
 * Get the free variables of t
 * - not part of the official API (because it exports a pointer
 *   to some internal data structures).
 * - return NULL if t is ground
 */
harray_t *yices_free_vars_of_term(term_t t) {
  assert(check_good_term(__yices_globals.manager, t));
  return get_free_vars_of_term(get_fvars(), t);
}


/*
 * Check structure of term t
 * - return false if t is not valid
 */
EXPORTED int32_t yices_term_is_atomic(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_atomic(t));
}

int32_t _o_yices_term_is_atomic(term_t t) {
  return check_good_term(__yices_globals.manager, t) && term_is_atomic(__yices_globals.terms, t);
}

EXPORTED int32_t yices_term_is_composite(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_composite(t));
}

int32_t _o_yices_term_is_composite(term_t t) {
  return check_good_term(__yices_globals.manager, t) && term_is_composite(__yices_globals.terms, t);
}

EXPORTED int32_t yices_term_is_projection(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_projection(t));
}

int32_t _o_yices_term_is_projection(term_t t) {
  return check_good_term(__yices_globals.manager, t) && term_is_projection(__yices_globals.terms, t);
}


EXPORTED int32_t yices_term_is_sum(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_sum(t));
}

int32_t _o_yices_term_is_sum(term_t t) {
  return check_good_term(__yices_globals.manager, t) && term_is_sum(__yices_globals.terms, t);
}

EXPORTED int32_t yices_term_is_bvsum(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_bvsum(t));
}

int32_t _o_yices_term_is_bvsum(term_t t) {
  return check_good_term(__yices_globals.manager, t) && term_is_bvsum(__yices_globals.terms, t);
}

EXPORTED int32_t yices_term_is_product(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_is_product(t));
}

int32_t _o_yices_term_is_product(term_t t) {
  return check_good_term(__yices_globals.manager, t) && term_is_product(__yices_globals.terms, t);
}


/*
 * Constructor for term t:
 * - the return code is defined in yices_types.h
 */
EXPORTED term_constructor_t yices_term_constructor(term_t t) {
  MT_PROTECT(term_constructor_t,  __yices_globals.lock, _o_yices_term_constructor(t));
}

term_constructor_t _o_yices_term_constructor(term_t t) {
  if (! check_good_term(__yices_globals.manager, t)) {
    return YICES_CONSTRUCTOR_ERROR;
  } else {
    return term_constructor(__yices_globals.terms, t);
  }
}


/*
 * Number of children of term t
 * - for atomic terms, returns 0
 * - for composite terms, returns the number of children
 * - for projections, returns 1
 * - for sums, returns the number of summands
 * - for products, returns the number of factors
 *
 * - returns -1 if t is not a valid term
 */
EXPORTED int32_t yices_term_num_children(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_num_children(t));
}

int32_t _o_yices_term_num_children(term_t t) {
  if (! check_good_term(__yices_globals.manager, t)) {
    return -1;
  }
  return term_num_children(__yices_globals.terms, t);
}


/*
 * Get i-th child of a composite term
 */
EXPORTED term_t yices_term_child(term_t t, int32_t i) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_term_child(t, i));
}

term_t _o_yices_term_child(term_t t, int32_t i) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_composite(__yices_globals.terms, t) ||
      ! check_child_idx(__yices_globals.terms, t, i)) {
    return NULL_TERM;
  }
  return term_child(__yices_globals.terms, t, i);
}


/*
 * Store all children of a composite term t in vector v
 */
EXPORTED int32_t yices_term_children(term_t t, term_vector_t *v) {
  MT_PROTECT(int32_t, __yices_globals.lock, _o_yices_term_children(t, v));
}

int32_t _o_yices_term_children(term_t t, term_vector_t *v) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_composite(__yices_globals.terms, t))  {
    return -1;
  }

  yices_reset_term_vector(v);
  get_term_children(__yices_globals.terms, t, (ivector_t *) v);

  return 0;
}


/*
 * Get the argument and index of a projection
 */
EXPORTED int32_t yices_proj_index(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_proj_index(t));
}

int32_t _o_yices_proj_index(term_t t) {
  int32_t idx;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_projection(__yices_globals.terms, t)) {
    return -1;
  }
  idx = proj_term_index(__yices_globals.terms, t);

  // for tuple projection: the internal index is between 0 and n-1
  // but the API uses an index between 1 and n
  if (term_kind(__yices_globals.terms, t) == SELECT_TERM) {
    idx ++;
  }
  return idx;
}

EXPORTED term_t yices_proj_arg(term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_proj_arg(t));
}

term_t _o_yices_proj_arg(term_t t) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_projection(__yices_globals.terms, t)) {
    return NULL_TERM;
  }
  return proj_term_arg(__yices_globals.terms, t);
}


/*
 * Value of a constant term
 */
EXPORTED int32_t yices_bool_const_value(term_t t, int32_t *val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_bool_const_value(t, val));
}

int32_t _o_yices_bool_const_value(term_t t, int32_t *val) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_constructor(__yices_globals.terms, t, YICES_BOOL_CONSTANT)) {
    return -1;
  }
  *val = bool_const_value(__yices_globals.terms, t);
  return 0;
}


EXPORTED int32_t yices_bv_const_value(term_t t, int32_t val[]) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_bv_const_value(t, val));
}

int32_t _o_yices_bv_const_value(term_t t, int32_t val[]) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_constructor(__yices_globals.terms, t, YICES_BV_CONSTANT)) {
    return -1;
  }
  bv_const_value(__yices_globals.terms, t, val);
  return 0;
}

EXPORTED int32_t yices_scalar_const_value(term_t t, int32_t *val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_scalar_const_value(t, val));
}

int32_t _o_yices_scalar_const_value(term_t t, int32_t *val) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_constructor(__yices_globals.terms, t, YICES_SCALAR_CONSTANT)) {
    return -1;
  }
  *val = generic_const_value(__yices_globals.terms, t);
  return 0;
}

EXPORTED int32_t yices_rational_const_value(term_t t, mpq_t q) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_rational_const_value(t, q));
}

int32_t _o_yices_rational_const_value(term_t t, mpq_t q) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_constructor(__yices_globals.terms, t, YICES_ARITH_CONSTANT)) {
    return -1;
  }
  arith_const_value(__yices_globals.terms, t, q);
  return 0;
}


/*
 * Components of a sum t
 * - i = index (must be between 0 and t's number of children - 1)
 * - for an arithmetic sum, each component is a pair (rational, term)
 * - for a bitvector sum, each component is a pair (bvconstant, term)
 * - the number of bits in the bvconstant is the same as in t
 */
EXPORTED int32_t yices_sum_component(term_t t, int32_t i, mpq_t coeff, term_t *term) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_sum_component(t, i, coeff, term));
}

int32_t _o_yices_sum_component(term_t t, int32_t i, mpq_t coeff, term_t *term) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_constructor(__yices_globals.terms, t, YICES_ARITH_SUM) ||
      ! check_child_idx(__yices_globals.terms, t, i)) {
    return -1;
  }
  sum_term_component(__yices_globals.terms, t, i, coeff, term);
  return 0;
}

EXPORTED int32_t yices_bvsum_component(term_t t, int32_t i, int32_t val[], term_t *term) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_bvsum_component(t, i, val, term));
}

int32_t _o_yices_bvsum_component(term_t t, int32_t i, int32_t val[], term_t *term) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_constructor(__yices_globals.terms, t, YICES_BV_SUM) ||
      ! check_child_idx(__yices_globals.terms, t, i)) {
    return -1;
  }
  bvsum_term_component(__yices_globals.terms, t, i, val, term);
  return 0;
}


/*
 * Component of power product t
 * - i = index (must be between 0 and t's arity - 1)
 * - the component is of the form (term, exponent)
 *   (where exponent is a positive integer)
 */
EXPORTED int32_t yices_product_component(term_t t, int32_t i, term_t *term, uint32_t *exp) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_product_component(t, i, term, exp));
}

int32_t _o_yices_product_component(term_t t, int32_t i, term_t *term, uint32_t *exp) {
  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_constructor(__yices_globals.terms, t, YICES_POWER_PRODUCT) ||
      ! check_child_idx(__yices_globals.terms, t, i)) {
    return -1;
  }
  product_term_component(__yices_globals.terms, t, i, term, exp);
  return 0;
}


/***********************************
 *  EXTENSIONS: TERM CONSTRUCTORS  *
 **********************************/

/*
 * These term constructors are used in term_stack
 *
 * IAM: we should probably have a naming convention that indicates their THREAD-SAFE use
 */
term_t arith_buffer_get_term(rba_buffer_t *b) {
  return mk_arith_term(__yices_globals.manager, b);
}

term_t arith_buffer_get_eq0_atom(rba_buffer_t *b) {
  return mk_arith_eq0(__yices_globals.manager, b);
}

term_t arith_buffer_get_geq0_atom(rba_buffer_t *b) {
  return mk_arith_geq0(__yices_globals.manager, b);
}

term_t arith_buffer_get_leq0_atom(rba_buffer_t *b) {
  return mk_arith_leq0(__yices_globals.manager, b);
}

term_t arith_buffer_get_gt0_atom(rba_buffer_t *b) {
  return mk_arith_gt0(__yices_globals.manager, b);
}

term_t arith_buffer_get_lt0_atom(rba_buffer_t *b) {
  return mk_arith_lt0(__yices_globals.manager, b);
}

term_t bvlogic_buffer_get_term(bvlogic_buffer_t *b) {
  return mk_bvlogic_term(__yices_globals.manager, b);
}

term_t bvlogic_buffer_get_bit(bvlogic_buffer_t *b, uint32_t i) {
  return bvl_get_bit(__yices_globals.manager, b, i);
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

term_t yices_rational_term(rational_t *q) {
  return arith_constant(__yices_globals.terms, q);
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
  return check_good_term(__yices_globals.manager, t) && check_boolean_term(__yices_globals.manager, t);
}

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
  return check_good_term(__yices_globals.manager, t) && check_arith_term(__yices_globals.manager, t);
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
bool yices_check_mul_term(rba_buffer_t *b, term_t t) {
  term_table_t *tbl;
  uint32_t d1, d2;

  tbl = __yices_globals.terms;

  assert(good_term(tbl, t) && is_arithmetic_term(tbl, t));

  d1 = rba_buffer_degree(b);
  d2 = term_degree(tbl, t);
  assert(d1 <= YICES_MAX_DEGREE && d2 <= YICES_MAX_DEGREE);

  return check_maxdegree(d1 + d2);
}


/*
 * Same thing for the product of two buffers b1 and b2.
 * - both must be buffers allocated using yices_new_arith_buffer().
 */
bool yices_check_mul_buffer(rba_buffer_t *b1, rba_buffer_t *b2) {
  uint32_t d1, d2;

  d1 = rba_buffer_degree(b1);
  d2 = rba_buffer_degree(b2);
  assert(d1 <= YICES_MAX_DEGREE && d2 <= YICES_MAX_DEGREE);

  return check_maxdegree(d1 + d2);
}


/*
 * Check whether t's type is a subtype of tau
 */
bool yices_check_term_type(term_t t, type_t tau) {
  term_table_t *tbl;

  tbl = __yices_globals.terms;
  if (! is_subtype(tbl->types, term_type(tbl, t), tau)) {
    error_report_t *error = get_yices_error();
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
  return check_good_term(__yices_globals.manager, t) && check_bitvector_term(__yices_globals.manager, t);
}


/*
 * Check whether b is non empty
 * Error report:
 *   code = EMPTY_BITVECTOR
 */
bool yices_check_bvlogic_buffer(bvlogic_buffer_t *b) {
  if (bvlogic_buffer_is_empty(b)) {
    set_error_code(EMPTY_BITVECTOR);
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
    error_report_t *error = get_yices_error();
    error->code = INVALID_BITSHIFT;
    error->badval = s;
    return false;
  }

  return true;
}


/*
 * Check whether s is a valid shift amount for rotate_left/rotate_right in SMT-LIB2
 * - SMT allows rotate by arbitrary amounts: ((_ rotate_left k) t) is the same
 *   as ((_ rotate_left (k % n) t)) where n = number of bits in t.
 *
 * This function
 * - return true if 0 <= s and store the normalize shift (s % b->nbits) in *s
 * - otherwise set the error report and return false.
 */
bool yices_check_smt2_rotate(bvlogic_buffer_t *b, int32_t *s) {
  int32_t shift;
  uint32_t n;

  shift = *s;
  if (shift < 0) {
    error_report_t *error = get_yices_error();
    error->code = INVALID_BITSHIFT;
    error->badval = shift;
    return false;
  }

  n = bvlogic_buffer_bitsize(b);
  if (shift >= n && n > 0) {
    shift = shift % n;
    *s = shift;
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
    set_error_code(INVALID_BVEXTRACT);
    return false;
  }

  return true;
}


/*
 * Check whether i is a valid bit index for a bitvector of size n
 * - return true if 0 <= i < n
 * - otherwise set the error report and return false.
 */
bool yices_check_bitextract(uint32_t n, int32_t i) {
  if (i < 0 || i >= n) {
    set_error_code(INVALID_BITEXTRACT);
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
  uint64_t m;

  if (n <= 0) {
    error_report_t *error = get_yices_error();
    error->code = POS_INT_REQUIRED;
    error->badval = n;
    return false;
  }

  m = ((uint64_t) n) * bvlogic_buffer_bitsize(b);
  if (m > ((uint64_t) YICES_MAX_BVSIZE)) {
    error_report_t *error = get_yices_error();
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
  uint64_t m;

  if (n < 0) {
    error_report_t *error = get_yices_error();
    error->code = NONNEG_INT_REQUIRED;
    error->badval = n;
    return false;
  }

  m = bvlogic_buffer_bitsize(b);
  if (m == 0) {
    set_error_code(EMPTY_BITVECTOR);
    return false;
  }

  m += n;
  if (m >= ((uint64_t) YICES_MAX_BVSIZE)) {
    error_report_t *error = get_yices_error();
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


/*
 * Check whether b contains an integer polynomial
 */
bool yices_arith_buffer_is_int(rba_buffer_t *b) {
  return arith_poly_is_integer(__yices_globals.terms, b);
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
EXPORTED term_t yices_subst_term(uint32_t n, const term_t var[], const term_t map[], term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_subst_term(n, var, map, t));
}

term_t _o_yices_subst_term(uint32_t n, const term_t var[], const term_t map[], term_t t) {
  term_subst_t subst;
  term_t u;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_good_substitution(__yices_globals.manager, n, var, map)) {
    return NULL_TERM;
  }

  init_term_subst(&subst, __yices_globals.manager, n, var, map);
  u = apply_term_subst(&subst, t);
  delete_term_subst(&subst);

  if (u < 0) {
    error_report_t *error = get_yices_error();
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
EXPORTED int32_t yices_subst_term_array(uint32_t n, const term_t var[], const term_t map[], uint32_t m, term_t t[]) {
  MT_PROTECT(int32_t, __yices_globals.lock, _o_yices_subst_term_array(n, var, map, m, t));
}

int32_t _o_yices_subst_term_array(uint32_t n, const term_t var[], const term_t map[], uint32_t m, term_t t[]) {
  term_subst_t subst;
  term_t u;
  uint32_t i;

  if (! check_good_terms(__yices_globals.manager, m, t) ||
      ! check_good_substitution(__yices_globals.manager, n, var, map)) {
    return -1;
  }

  init_term_subst(&subst, __yices_globals.manager, n, var, map);
  for (i=0; i<m; i++) {
    u = apply_term_subst(&subst, t[i]);
    if (u < 0)  goto subst_error;
    t[i] = u;
  }
  delete_term_subst(&subst);

  return 0;

 subst_error:
  if (u == -1) {
    error_report_t *error = get_yices_error();
    // degree overflow
    error->code = DEGREE_OVERFLOW;
    error->badval = YICES_MAX_DEGREE + 1;
  } else {
    // BUG
    set_error_code(INTERNAL_EXCEPTION);
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
EXPORTED type_t yices_parse_type(const char *s) {
  MT_PROTECT(type_t,  __yices_globals.lock, _o_yices_parse_type(s));
}

type_t _o_yices_parse_type(const char *s) {
  parser_t *p;

  p = get_parser(s);
  return parse_yices_type(p, NULL);
}


/*
 * Parse s as a term in the Yices language.
 * Return NULL_TERM if there's an error.
 */
EXPORTED term_t yices_parse_term(const char *s) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_parse_term(s));
}

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
EXPORTED int32_t yices_set_type_name(type_t tau, const char *name) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_set_type_name(tau, name));
}

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
EXPORTED int32_t yices_set_term_name(term_t t, const char *name) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_set_term_name(t, name));
}

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
EXPORTED const char *yices_get_type_name(type_t tau) {
  MT_PROTECT(const char *,  __yices_globals.lock, _o_yices_get_type_name(tau));
}

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
EXPORTED const char *yices_get_term_name(term_t t) {
  MT_PROTECT(const char *,  __yices_globals.lock, _o_yices_get_term_name(t));
}

const char *_o_yices_get_term_name(term_t t) {
  if (! check_good_term(__yices_globals.manager, t)) {
    return NULL;
  }
  return term_name(__yices_globals.terms, t);
}



/*
 * Remove name from the type table.
 */
EXPORTED void yices_remove_type_name(const char *name) {
  MT_PROTECT_VOID(__yices_globals.lock, _o_yices_remove_type_name(name));
}

void _o_yices_remove_type_name(const char *name) {
  remove_type_name(__yices_globals.types, name);
}


/*
 * Remove name from the term table.
 */
EXPORTED void yices_remove_term_name(const char *name) {
  MT_PROTECT_VOID(__yices_globals.lock, _o_yices_remove_term_name(name));
}

void _o_yices_remove_term_name(const char *name) {
  remove_term_name(__yices_globals.terms, name);
}


/*
 * Get type of the given name or return NULL_TYPE (-1)
 */
EXPORTED type_t yices_get_type_by_name(const char *name) {
  MT_PROTECT(type_t,  __yices_globals.lock, _o_yices_get_type_by_name(name));
}

type_t _o_yices_get_type_by_name(const char *name) {
  return get_type_by_name(__yices_globals.types, name);
}


/*
 * Get term of the given name or return NULL_TERM
 */
EXPORTED term_t yices_get_term_by_name(const char *name) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_get_term_by_name(name));
}

term_t _o_yices_get_term_by_name(const char *name) {
  return get_term_by_name(__yices_globals.terms, name);
}


/*
 * Remove the name of type tau (if any)
 * Return -1 if tau is not a valid type and set the error code.
 * Return 0 otherwise.
 */
EXPORTED int32_t yices_clear_type_name(type_t tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_clear_type_name(tau));
}

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
EXPORTED int32_t yices_clear_term_name(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_clear_term_name(t));
}

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
  int32_t k;

  k = config_set_field(config, name, value);
  if (k < 0) {
    if (k == -1) {
      // invalid name
      set_error_code(CTX_UNKNOWN_PARAMETER);
    } else {
      set_error_code(CTX_INVALID_PARAMETER_VALUE);
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
      set_error_code(CTX_UNKNOWN_LOGIC);
    } else {
      set_error_code(CTX_LOGIC_NOT_SUPPORTED);
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
  CTX_OPTION_BREAK_SYMMETRIES,
  CTX_OPTION_KEEP_ITE,
  CTX_OPTION_EAGER_ARITH_LEMMAS,
  CTX_OPTION_ASSERT_ITE_BOUNDS,
} ctx_option_t;

#define NUM_CTX_OPTIONS (CTX_OPTION_ASSERT_ITE_BOUNDS+1)


/*
 * Option names in lexicographic order
 */
static const char * const ctx_option_names[NUM_CTX_OPTIONS] = {
  "arith-elim",
  "assert-ite-bounds",
  "break-symmetries",
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
  CTX_OPTION_ASSERT_ITE_BOUNDS,
  CTX_OPTION_BREAK_SYMMETRIES,
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

  case CTX_OPTION_BREAK_SYMMETRIES:
    enable_symmetry_breaking(ctx);
    break;

  case CTX_OPTION_KEEP_ITE:
    enable_keep_ite(ctx);
    break;

  case CTX_OPTION_EAGER_ARITH_LEMMAS:
    enable_splx_eager_lemmas(ctx);
    break;

  case CTX_OPTION_ASSERT_ITE_BOUNDS:
    enable_assert_ite_bounds(ctx);
    break;

  default:
    assert(k == -1);
    // not recognized
    set_error_code(CTX_UNKNOWN_PARAMETER);
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
    disable_bvarith_elimination(ctx);
    break;

  case CTX_OPTION_FLATTEN:
    disable_diseq_and_or_flattening(ctx);
    break;

  case CTX_OPTION_LEARN_EQ:
    disable_eq_abstraction(ctx);
    break;

  case CTX_OPTION_BREAK_SYMMETRIES:
    disable_symmetry_breaking(ctx);
    break;

  case CTX_OPTION_KEEP_ITE:
    disable_keep_ite(ctx);
    break;

  case CTX_OPTION_EAGER_ARITH_LEMMAS:
    disable_splx_eager_lemmas(ctx);
    break;

  case CTX_OPTION_ASSERT_ITE_BOUNDS:
    disable_assert_ite_bounds(ctx);
    break;

  default:
    set_error_code(CTX_UNKNOWN_PARAMETER);
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
      set_error_code(CTX_UNKNOWN_PARAMETER);
    } else {
      set_error_code(CTX_INVALID_PARAMETER_VALUE);
    }
    return -1;
  }

  return 0;
}



/*************************
 *  CONTEXT OPERATIONS   *
 ************************/

/*
 * Set the default preprocessing options for a context
 * - logic = logic code (or SMT_UNKNOWN)
 * - arch = architecture
 * - iflag = true if integer solver is active
 * - qflag = true if quantifier support is required
 *
 * Note: these settings are based on benchmarking using the SMT-LIB 1.2
 * benchmarks (cf. yices_smtcomp.c)
 */
static void context_set_default_options(context_t *ctx, smt_logic_t logic, context_arch_t arch, bool iflag, bool qflag) {
  enable_variable_elimination(ctx);
  enable_eq_abstraction(ctx);
  enable_arith_elimination(ctx);
  enable_bvarith_elimination(ctx);

  if (iflag) {
    enable_splx_periodic_icheck(ctx);
  }

  // Special preprocessing
  if (logic == QF_LRA) {
    enable_cond_def_preprocessing(ctx);
  }
  if (logic == QF_LIRA) {
    enable_or_factoring(ctx);
  }

  switch (arch) {
  case CTX_ARCH_EG:
    enable_diseq_and_or_flattening(ctx);
    if (context_get_mode(ctx) == CTX_MODE_ONECHECK) {
      enable_symmetry_breaking(ctx);
    }
    break;

  case CTX_ARCH_BV:
    // flattening makes things worse for QF_BV
    //   disable_diseq_and_or_flattening(ctx); FOR TESTING THE SHARING STUFF (2015/04/22)
    enable_diseq_and_or_flattening(ctx); // FOR TESTING THE SHARING STUFF (2015/04/22)
    break;

  case CTX_ARCH_SPLX:
    enable_splx_eager_lemmas(ctx);
    enable_diseq_and_or_flattening(ctx);
    enable_assert_ite_bounds(ctx);
    enable_ite_flattening(ctx);
    break;

  case CTX_ARCH_EGSPLX:
  case CTX_ARCH_EGFUNSPLX:
    enable_splx_eager_lemmas(ctx);
    enable_diseq_and_or_flattening(ctx);
    enable_splx_eqprop(ctx);
    enable_assert_ite_bounds(ctx);
    enable_ite_flattening(ctx);
    break;

  case CTX_ARCH_EGBV:
  case CTX_ARCH_EGFUNBV:
    // no ite_flattening (TO BE CONFIRMED)
    enable_diseq_and_or_flattening(ctx);
    break;

  default:
    enable_diseq_and_or_flattening(ctx);
    break;
  }

}



/*
 * Allocate and initialize a new context.
 * The configuration is specified by logic/arch/mode/iflag/qflag.
 * - logic = SMT_UNKNOWN or a logic code
 * - arch = architecture to use
 * - mode = which optional features are supported
 * - iflag = true to active the integer solver
 * - qflag = true to support quantifiers
 */
static context_t *_o_yices_create_context(smt_logic_t logic, context_arch_t arch, context_mode_t mode, bool iflag, bool qflag) {
  context_t *ctx;

  ctx = alloc_context();
  init_context(ctx, __yices_globals.terms, logic, mode, arch, qflag);
  context_set_default_options(ctx, logic, arch, iflag, qflag);

  return ctx;
}

context_t *yices_create_context(smt_logic_t logic, context_arch_t arch, context_mode_t mode, bool iflag, bool qflag) {
  MT_PROTECT(context_t *, __yices_globals.lock, _o_yices_create_context(logic, arch, mode, iflag, qflag));
}


/*
 * Allocate and initialize and new context
 * - the configuration is defined by config.
 * - if config is NULL, the default is used.
 * - otherwise, if the configuration is not supported, the function returns NULL.
 */
EXPORTED context_t *yices_new_context(const ctx_config_t *config) {
  MT_PROTECT(context_t *, __yices_globals.lock, _o_yices_new_context(config));
}
context_t *_o_yices_new_context(const ctx_config_t *config) {
  smt_logic_t logic;
  context_arch_t arch;
  context_mode_t mode;
  bool iflag;
  bool qflag;
  int32_t k;

  if (config == NULL) {
    // Default configuration: all solvers, mode = push/pop
    logic = SMT_UNKNOWN;
    arch = CTX_ARCH_EGFUNSPLXBV;
    mode = CTX_MODE_PUSHPOP;
    iflag = true;
    qflag = false;
  } else {
    // read the config
    k = decode_config(config, &logic, &arch, &mode, &iflag, &qflag);
    if (k < 0) {
      // invalid configuration
      set_error_code(CTX_INVALID_CONFIG);
      return NULL;
    }
  }

  return _o_yices_create_context(logic, arch, mode, iflag, qflag);
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
    set_error_code(CTX_OPERATION_NOT_SUPPORTED);
    return -1;
  }

  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    context_clear(ctx);
    break;

  case STATUS_IDLE:
    break;

  case STATUS_UNSAT:
    // try to remove assumptions
    context_clear_unsat(ctx);
    if (context_status(ctx) == STATUS_IDLE) {
      break;
    }
    assert(context_status(ctx) == STATUS_UNSAT);
    // fall through
  case STATUS_INTERRUPTED:
  case STATUS_SEARCHING:
    set_error_code(CTX_INVALID_OPERATION);
    return -1;

  case STATUS_ERROR:
  default:
    set_error_code(INTERNAL_EXCEPTION);
    return -1;
  }

  assert(context_status(ctx) == STATUS_IDLE);
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
    set_error_code(CTX_OPERATION_NOT_SUPPORTED);
    return -1;
  }

  if (context_base_level(ctx) == 0) {
    set_error_code(CTX_INVALID_OPERATION);
    return -1;
  }

  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
  case STATUS_INTERRUPTED:
    context_clear(ctx);
    break;

  case STATUS_IDLE:
    break;

  case STATUS_UNSAT:
    context_clear_unsat(ctx);
    break;

  case STATUS_SEARCHING:
    set_error_code(CTX_INVALID_OPERATION);
    return -1;

  case STATUS_ERROR:
  default:
    set_error_code(INTERNAL_EXCEPTION);
    return -1;
  }

  assert(context_status(ctx) == STATUS_IDLE ||
	 context_status(ctx) == STATUS_UNSAT);
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
  CTX_SCALAR_NOT_SUPPORTED,
  CTX_TUPLE_NOT_SUPPORTED,
  CTX_UTYPE_NOT_SUPPORTED,
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
  MCSAT_ERROR_UNSUPPORTED_THEORY
};

static inline void convert_internalization_error(int32_t code) {
  assert(-NUM_INTERNALIZATION_ERRORS < code && code < 0);
  set_error_code(intern_code2error[-code]);
}


/*
 * Exports the previous function for front-end tools
 */
void yices_internalization_error(int32_t code) {
  convert_internalization_error(code);
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
static inline bool _o_yices_assert_formula_checks(term_t t) {
  return check_good_term(__yices_globals.manager, t) && check_boolean_term(__yices_globals.manager, t);
}

static inline bool yices_assert_formula_checks(term_t t) {
  MT_PROTECT(bool,  __yices_globals.lock, _o_yices_assert_formula_checks(t));
}

EXPORTED int32_t yices_assert_formula(context_t *ctx, term_t t) {
  int32_t code;

  if (! yices_assert_formula_checks(t)) {
    return -1;
  }

  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    if (! context_supports_multichecks(ctx)) {
      set_error_code(CTX_OPERATION_NOT_SUPPORTED);
      return -1;
    }
    context_clear(ctx);
    break;

  case STATUS_IDLE:
    break;

  case STATUS_UNSAT:
    // try to remove assumptions
    context_clear_unsat(ctx);
    if (context_status(ctx) == STATUS_UNSAT) {
      // nothing to do
      return 0;
    }
    break;

  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
    set_error_code(CTX_INVALID_OPERATION);
    return -1;

  case STATUS_ERROR:
  default:
    set_error_code(INTERNAL_EXCEPTION);
    return -1;
  }

  assert(context_status(ctx) == STATUS_IDLE);

  code = assert_formula(ctx, t);
  if (code < 0) {
    // error during internalization
    convert_internalization_error(code);
    return -1;
  }
  assert(code == TRIVIALLY_UNSAT || code == CTX_NO_ERROR);

  return 0;
}






/*
 * Same thing for an array of n formulas t[0 ... n-1]
 */

static inline bool _o_yices_assert_formulas_checks(uint32_t n, const term_t t[]) {
  return check_good_terms(__yices_globals.manager, n, t) && check_boolean_args(__yices_globals.manager, n, t);
}

static inline bool yices_assert_formulas_checks(uint32_t n, const term_t t[]) {
  MT_PROTECT(bool,  __yices_globals.lock, _o_yices_assert_formulas_checks(n, t));
}

EXPORTED int32_t yices_assert_formulas(context_t *ctx, uint32_t n, const term_t t[]) {
  int32_t code;

  if (! yices_assert_formulas_checks(n, t)) {
    return -1;
  }

  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    if (! context_supports_multichecks(ctx)) {
      set_error_code(CTX_OPERATION_NOT_SUPPORTED);
      return -1;
    }
    context_clear(ctx);
    break;

  case STATUS_IDLE:
    break;

  case STATUS_UNSAT:
    // try to remove assumptions
    context_clear_unsat(ctx);
    if (context_status(ctx) == STATUS_UNSAT) {
      // nothing to do
      return 0;
    }
    break;

  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
    set_error_code(CTX_INVALID_OPERATION);
    return -1;

  case STATUS_ERROR:
  default:
    set_error_code(INTERNAL_EXCEPTION);
    return -1;
  }

  assert(context_status(ctx) == STATUS_IDLE);

  code = assert_formulas(ctx, n, t);
  if (code < 0) {
    // error during internalization
    convert_internalization_error(code);
    return -1;
  }
  assert(code == TRIVIALLY_UNSAT || code == CTX_NO_ERROR);

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
      set_error_code(CTX_OPERATION_NOT_SUPPORTED);
      return -1;
    }

  case STATUS_UNSAT:
  case STATUS_IDLE:
  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
    set_error_code(CTX_INVALID_OPERATION);
    return -1;

  case STATUS_ERROR:
  default:
    set_error_code(INTERNAL_EXCEPTION);
    return -1;
  }
}



/*
 * Set default search parameters based on architecture, logic, and mode
 * - the parameter settings are based on SMT-LIB2 benchmarks
 */
void yices_set_default_params(param_t *params, smt_logic_t logic, context_arch_t arch, context_mode_t mode) {
  init_params_to_defaults(params);
  switch (arch) {
  case CTX_ARCH_EG:
    // QF_UF options: --var-elim --cache-tclauses --learn-eq --dyn-bool-ack
    params->use_bool_dyn_ack = true;
    params->use_dyn_ack = true;
    //    params->max_ackermann = 100;
    params->cache_tclauses = true;
    params->tclause_size = 12;
    break;

  case CTX_ARCH_SPLX:
    // options: --flatten --theory-branching --cache-tclauses --arith-elim --var-elim
    params->branching = BRANCHING_THEORY;
    params->cache_tclauses = true;
    params->tclause_size = 8;
    if (logic == QF_LIA || logic == QF_LIRA) {
      params->use_simplex_prop = true;
      params->tclause_size = 20;
    }
    break;

  case CTX_ARCH_BV:
#if 0
    // QF_BV options: --var-elim --fast-restarts --randomness=0 --bvarith-elim
    params->fast_restart = true;
    params->c_factor = 1.05;
    params->d_factor = 1.05;
    params->randomness = 0.0;
#endif
    // HACK: try Luby restart, period = 10
    params->fast_restart = true;
    params->c_factor = 0.0;
    params->c_threshold = 10;
    params->randomness = 0.0;
    break;

  case CTX_ARCH_EGSPLX:       // egraph+simplex
  case CTX_ARCH_EGFUNSPLX:    // egraph+fun+simplex
    params->use_dyn_ack = true;
    params->use_bool_dyn_ack = true;
    params->use_simplex_prop = true;
    params->adjust_simplex_model = true;
    params->cache_tclauses = true;
    params->tclause_size = 8;
    params->use_optimistic_fcheck = true;
    if (logic == QF_UFLIA || logic == QF_UFLIRA || logic == QF_AUFLIA || logic == QF_ALIA || logic == QF_UFIDL) {
      params->branching = BRANCHING_NEGATIVE;
      params->max_interface_eqs = 15;
    } else {
      params->branching = BRANCHING_THEORY;
      params->max_interface_eqs = 30;
    }

    /*
     * For QF_UFLIA: optimistic_fcheck works better on the incremental benchmarks
     * but it's worse on the non-incremental benchmarks.
     */
    if ((logic == QF_UFLIA || logic == QF_UFLIRA) && mode == CTX_MODE_ONECHECK) {
      params->use_optimistic_fcheck = false;
    }
    break;

  case CTX_ARCH_EGBV:         // egraph+bitvector solver
  case CTX_ARCH_EGFUNBV:      // egraph+fun+bitvector
    // QF_BV options: --var-elim --fast-restarts --randomness=0 --bvarith-elim
#if 1
    params->fast_restart = true;
    params->c_factor = 1.05;
    params->d_factor = 1.05;
#else
    // HACK: try Luby restart, period = 10
    // This didn't work.
    params->fast_restart = true;
    params->c_factor = 0.0;
    params->c_threshold = 10;
#endif
    params->randomness = 0.0;
    params->max_interface_eqs = 15;
    if (logic == QF_UFBV) {
      // randomness helps for the SMT benchmarks
      params->randomness = 0.02;
    }
    break;

  case CTX_ARCH_IFW:
  case CTX_ARCH_RFW:
    params->cache_tclauses = true;
    params->tclause_size = 20;
    params->fast_restart = true;
    params->c_factor = 1.1;
    params->d_factor = 1.1;
    break;

  case CTX_ARCH_EGFUNSPLXBV:
    // egraph+bitvector+simplex+fun solver
    // this is the default if no logic is specified
    params->use_dyn_ack = true;
    params->use_bool_dyn_ack = true;
    params->use_optimistic_fcheck = true;
    params->use_simplex_prop = true;
    params->adjust_simplex_model = true;
    params->cache_tclauses = true;
    params->tclause_size = 8;
    params->max_interface_eqs = 15;
    break;

  case CTX_ARCH_EGFUN:
  case CTX_ARCH_AUTO_IDL:
  case CTX_ARCH_AUTO_RDL:
  default:
    // nothing required
    break;
  }

}

/*
 * Set default search parameters for ctx (based on architecture and theories)
 * - this is based on benchmarking on the SMT-LIB 1.2 benchmarks (cf. yices_smtcomp.c)
 */
EXPORTED void yices_default_params_for_context(const context_t *ctx, param_t *params) {
  yices_set_default_params(params, ctx->logic, ctx->arch, ctx->mode);
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
EXPORTED smt_status_t yices_check_context(context_t *ctx, const param_t *params) {
  param_t default_params;
  smt_status_t stat;

  stat = context_status(ctx);
  switch (stat) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    break;

  case STATUS_UNSAT:
    // remove assumptions if any
    context_clear_unsat(ctx);
    if (context_status(ctx) == STATUS_UNSAT) {
      // no assumptions removed: still unsat
      break;
    }
    assert(context_status(ctx) == STATUS_IDLE);

    // fall through intended
  case STATUS_IDLE:
    if (params == NULL) {
      yices_default_params_for_context(ctx, &default_params);
      params = &default_params;
    }
    stat = check_context(ctx, params);
    if (stat == STATUS_INTERRUPTED && context_supports_cleaninterrupt(ctx)) {
      context_cleanup(ctx);
    }
    break;

  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
    set_error_code(CTX_INVALID_OPERATION);
    stat = STATUS_ERROR;
    break;

  case STATUS_ERROR:
  default:
    set_error_code(INTERNAL_EXCEPTION);
    stat = STATUS_ERROR;
    break;
  }

  return stat;
}

//IAM: experiment to see if we can keep some concurrency.
static bool _o_unsat_core_check_assumptions(uint32_t n, const term_t a[]) {
  if (! check_good_terms(__yices_globals.manager, n, a) ||
      ! check_boolean_args(__yices_globals.manager, n, a)) {
    return false; // Bad assumptions
  }
  return true;
}

static bool unsat_core_check_assumptions(uint32_t n, const term_t a[]) {
  MT_PROTECT(bool,  __yices_globals.lock, _o_unsat_core_check_assumptions(n, a));
}

/*
 * Check context with assumptions
 * - n = number of assumptions
 * - a[0] ... a[n-1] = n assumptions. All of them must be Boolean terms.
 */
EXPORTED smt_status_t yices_check_context_with_assumptions(context_t *ctx, const param_t *params, uint32_t n, const term_t a[]) {
  param_t default_params;
  ivector_t assumptions;
  smt_status_t stat;
  uint32_t i;
  literal_t l;

  if (!unsat_core_check_assumptions(n, a)) {
    return STATUS_ERROR; // Bad assumptions
  }

  // cleanup
  switch (context_status(ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    if (! context_supports_multichecks(ctx)) {
      set_error_code(CTX_OPERATION_NOT_SUPPORTED);
      return STATUS_ERROR;
    }
    context_clear(ctx);
    break;

  case STATUS_IDLE:
    break;

  case STATUS_UNSAT:
    if (! context_supports_multichecks(ctx)) {
      set_error_code(CTX_OPERATION_NOT_SUPPORTED);
      return STATUS_ERROR;
    }
    // try to remove the previous assumptions if any
    context_clear_unsat(ctx);
    if (context_status(ctx) == STATUS_UNSAT) {
      return STATUS_UNSAT;
    }
    break;

  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
    set_error_code(CTX_INVALID_OPERATION);
    return STATUS_ERROR;

  case STATUS_ERROR:
  default:
    set_error_code(INTERNAL_EXCEPTION);
    return STATUS_ERROR;
  }

  assert(context_status(ctx) == STATUS_IDLE);

  yices_obtain_mutex();

  // convert the assumptions to n literals
  init_ivector(&assumptions, n);
  for (i=0; i<n; i++) {
    l = context_add_assumption(ctx, a[i]);
    if (l < 0) {
      // error when converting a[i] to a literal
      convert_internalization_error(l);
      stat = STATUS_ERROR;
      yices_release_mutex();
      goto cleanup;
    }
    ivector_push(&assumptions, l);
  }
  assert(assumptions.size == n);

  yices_release_mutex();

  // set parameters
  if (params == NULL) {
    yices_default_params_for_context(ctx, &default_params);
    params = &default_params;
  }

  // call check
  stat = check_context_with_assumptions(ctx, params, n, assumptions.data);
  if (stat == STATUS_INTERRUPTED && context_supports_cleaninterrupt(ctx)) {
    context_cleanup(ctx);
  }

 cleanup:
  delete_ivector(&assumptions);

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



/****************
 *  UNSAT CORE  *
 ***************/

/*
 * Construct an unsat core: store the result in vector *v
 * - returns 0 if this works
 * - returns -1 if there's an error
 */
EXPORTED int32_t yices_get_unsat_core(context_t *ctx, term_vector_t *v) {
  if (context_status(ctx) != STATUS_UNSAT) {
    set_error_code(CTX_INVALID_OPERATION);
    return -1;
  }

  yices_reset_term_vector(v);
  context_build_unsat_core(ctx, (ivector_t *) v);
  return 0;
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
EXPORTED model_t *yices_get_model(context_t *ctx, int32_t keep_subst) {
  MT_PROTECT(model_t *,  __yices_globals.lock, _o_yices_get_model(ctx, keep_subst));
}

model_t *_o_yices_get_model(context_t *ctx, int32_t keep_subst) {
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
    set_error_code(CTX_INVALID_OPERATION);
    mdl = NULL;
    break;
  }

  return mdl;
}


/*
 * Return an empty model
 */
model_t *yices_new_model(bool keep_subst) {
  model_t *mdl;

  mdl = alloc_model();
  init_model(mdl, __yices_globals.terms, keep_subst);

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
EXPORTED void yices_print_model(FILE *f, model_t *mdl) {
  MT_PROTECT_VOID(__yices_globals.lock, _o_yices_print_model(f, mdl));
}

void _o_yices_print_model(FILE *f, model_t *mdl) {
  model_print_full(f, mdl);
}

EXPORTED int32_t yices_print_model_fd(int fd, model_t *mdl) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_print_model_fd(fd, mdl));
}

int32_t _o_yices_print_model_fd(int fd, model_t *mdl) {
  FILE *tmp_fp;

  tmp_fp = fd_2_tmp_fp(fd);
  if (tmp_fp == NULL) {
    file_output_error();
    return -1;
  }
  model_print_full(tmp_fp, mdl);
  fclose(tmp_fp);

  return 0;
}


/*
 * Pretty print mdl
 * - f = output file to use
 * - width, height, offset = print area
 */
EXPORTED int32_t yices_pp_model(FILE *f, model_t *mdl, uint32_t width, uint32_t height, uint32_t offset) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_pp_model(f, mdl, width, height, offset));
}

int32_t _o_yices_pp_model(FILE *f, model_t *mdl, uint32_t width, uint32_t height, uint32_t offset) {
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
    file_output_error();
  }
  delete_yices_pp(&printer, false);

  return code;
}

EXPORTED int32_t yices_pp_model_fd(int fd, model_t *mdl, uint32_t width, uint32_t height, uint32_t offset) {
  FILE *tmp_fp;
  int32_t retval;

  tmp_fp = fd_2_tmp_fp(fd);
  if (tmp_fp == NULL) {
    file_output_error();
    return -1;
  }
  retval = yices_pp_model(tmp_fp, mdl, width, height, offset);
  fclose(tmp_fp);

  return retval;
}

/*
 * Convert mdl to a string
 */
EXPORTED char *yices_model_to_string(model_t *mdl, uint32_t width, uint32_t height, uint32_t offset) {
  MT_PROTECT(char *,  __yices_globals.lock, _o_yices_model_to_string(mdl, width, height, offset));
}

char *_o_yices_model_to_string(model_t *mdl, uint32_t width, uint32_t height, uint32_t offset) {
  yices_pp_t printer;
  pp_area_t area;
  char *str;
  uint32_t len;

  if (width < 4) width = 4;
  if (height == 0) height = 1;

  area.width = width;
  area.height = height;
  area.offset = offset;
  area.stretch = false;
  area.truncate = true;

  init_default_yices_pp(&printer, NULL, &area);
  model_pp_full(&printer, mdl);
  flush_yices_pp(&printer);

  str = yices_pp_get_string(&printer, &len);
  delete_yices_pp(&printer, false);

  return str;
}


/*
 * Print the values of n terms in  a model
 * - f = output file
 * - mdl = model
 * - n = number of terms
 * - a - array of n terms
 *
 * The function returns -1 on error, 0 otherwise.
 *
 * Error report:
 * if a[i] is not a valid term:
 *   code = INVALID_TERM
 *   term1 = a[i]
 */
EXPORTED int32_t yices_print_term_values(FILE *f, model_t *mdl, uint32_t n, const term_t a[]) {
  MT_PROTECT(int32_t, __yices_globals.lock, _o_yices_print_term_values(f, mdl, n, a));
}

int32_t _o_yices_print_term_values(FILE *f, model_t *mdl, uint32_t n, const term_t a[]) {
  if (! check_good_terms(__yices_globals.manager, n, a)) {
    return -1;
  }
  model_print_eval_terms(f, mdl, a, n);

  return 0;
}

// Variant with a file descriptor
EXPORTED int32_t yices_print_term_values_fd(int fd, model_t *mdl, uint32_t n, const term_t a[]) {
  FILE *tmp_fp;
  int32_t code;

  tmp_fp = fd_2_tmp_fp(fd);
  if (tmp_fp == NULL) {
    file_output_error();
    return -1;
  }
  code = yices_print_term_values(tmp_fp, mdl, n, a);
  fclose(tmp_fp);

  return code;
}


/*
 * Pretty print the values of n terms in  a model
 * - f = output file
 * - mdl = model
 * - n = number of terms
 * - a - array of n terms
 * - width, height, offset define the print area.
 *
 * This function is like yices_print_term_values except that is uses pretty printing.
 *
 * Return code: -1 on error, 0 otherwise
 *
 *
 * Error report:
 * if a[i] is not a valid term:
 *   code = INVALID_TERM
 *   term1 = a[i]
 * if writing to f fails,
 *   code = OUTPUT_ERROR
 *   in this case, errno, perror, etc. can be used for diagnostic.
 */
EXPORTED int32_t yices_pp_term_values(FILE *f, model_t *mdl, uint32_t n, const term_t a[],
				      uint32_t width, uint32_t height, uint32_t offset) {
  MT_PROTECT(int32_t, __yices_globals.lock, _o_yices_pp_term_values(f, mdl, n, a, width, height, offset));
}

int32_t _o_yices_pp_term_values(FILE *f, model_t *mdl, uint32_t n, const term_t a[],
				uint32_t width, uint32_t height, uint32_t offset) {
  yices_pp_t printer;
  pp_area_t area;
  int32_t code;

  if (! check_good_terms(__yices_globals.manager, n, a)) {
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
  model_pp_eval_terms(&printer, mdl, a, n);
  flush_yices_pp(&printer);

  // check for error
  code = 0;
  if (yices_pp_print_failed(&printer)) {
    code = -1;
    errno = yices_pp_errno(&printer);
    file_output_error();
  }
  delete_yices_pp(&printer, false);

  return code;
}

// Variant with a file descriptor
EXPORTED int32_t yices_pp_term_values_fd(int fd, model_t *mdl, uint32_t n, const term_t a[],
					 uint32_t width, uint32_t height, uint32_t offset) {
  FILE *tmp_fp;
  int32_t code;

  tmp_fp = fd_2_tmp_fp(fd);
  if (tmp_fp == NULL) {
    file_output_error();
    return -1;
  }
  code = yices_pp_term_values(tmp_fp, mdl, n, a, width, height, offset);
  fclose(tmp_fp);

  return code;
}




/*
 * BUILD A MODEL FROM A MAP OF UNINTERPRETED TO CONSTANT TERMS
 */

/*
 * Build a model from a term-to-term mapping:
 * - the mapping is defined by two arrays var[] and map[]
 * - every element of var must be an uninterpreted term
 *   every element of map must be a constant of primitive or tuple type
 *   map[i]'s type must be a subtype of var[i]
 * - there must not be duplicates in array var
 *
 * The function returns NULL and set up the error report if something
 * goes wrong. It allocates and create a new model otherwise. This
 * model must be deleted when no longer used via yices_free_model.
 *
 * Error report:
 * - code = INVALID_TERM if var[i] or map[i] is not valid
 * - code = TYPE_MISMATCH if map[i] doesn't have a type compatible (subtype of)
 *          var[i]'s type
 * - code = MDL_UNINT_REQUIRED if var[i] is not an uninterpreted term
 * - code = MDL_CONSTANT_REQUIRED if map[i] is not a constant
 * - code = MDL_DUPLICATE_VAR if var contains duplicate elements
 * - code = MDL_FTYPE_NOT_ALLOWED if one of var[i] has a function type
 * - code = MDL_CONSTRUCTION_FAILED: something else went wrong
 */
EXPORTED model_t *yices_model_from_map(uint32_t n, const term_t var[], const term_t map[]) {
  MT_PROTECT(model_t *,  __yices_globals.lock, _o_yices_model_from_map(n, var, map));
}

model_t *_o_yices_model_from_map(uint32_t n, const term_t var[], const term_t map[]) {
  model_t *mdl;

  if (! check_good_model_map(__yices_globals.manager, n, var, map)) {
    return NULL;
  }

  mdl = yices_new_model(true);
  build_model_from_map(mdl, n, var, map);
  return mdl;
}


/*
 * Export the list of uninterpreted terms that have a value in mdl.
 * - the variables are stored in term_vector v
 */
EXPORTED void yices_model_collect_defined_terms(model_t *mdl, term_vector_t *v) {
  MT_PROTECT_VOID(__yices_globals.lock, model_get_relevant_vars(mdl, (ivector_t *) v));
}



/*
 * Collect the support of term t in mdl:
 * - the support is a set of uninterpreted returned in *v
 */
EXPORTED int32_t yices_model_term_support(model_t *mdl, term_t t, term_vector_t *v) {
  MT_PROTECT(int32_t, __yices_globals.lock, _o_yices_model_term_support(mdl, t, v));
}

int32_t _o_yices_model_term_support(model_t *mdl, term_t t, term_vector_t *v) {
  if (! check_good_term(__yices_globals.manager, t)) {
    return -1;
  }
  model_get_term_support(mdl, t, (ivector_t *) v);
  return 0;
}


/*
 * Collect the support of terms a[0 ... n-1] in mdl:
 * - the support is a set of uninterpreted returned in *v
 */
EXPORTED int32_t yices_model_term_array_support(model_t *mdl, uint32_t n, const term_t a[], term_vector_t *v) {
  MT_PROTECT(int32_t, __yices_globals.lock, _o_yices_model_term_array_support(mdl, n, a, v));
}

int32_t _o_yices_model_term_array_support(model_t *mdl, uint32_t n, const term_t a[], term_vector_t *v) {
  if (! check_good_terms(__yices_globals.manager, n, a)) {
    return -1;
  }
  model_get_terms_support(mdl, n, a, (ivector_t *) v);
  return 0;
}




/******************************
 *  CHECK FORMULAS/DELEGATES  *
 *****************************/

/*
 * Evaluate all terms in a[0 ... n-1] in a default model.
 * Return true if all terms evaluate to true in the model.
 * Return false otherwise.
 *
 * If model != NULL and the result is true, the default model is
 * returned in model.
 */
bool trivially_true_assertions(const term_t *a, uint32_t n, model_t **model) {
  model_t *mdl;
  evaluator_t evaluator;
  uint32_t i;
  bool result;

  yices_obtain_mutex();

  result = true;
  mdl = yices_new_model(true);
  init_evaluator(&evaluator, mdl);
  for (i=0; i<n; i++) {
    if (!eval_to_true_in_model(&evaluator, a[i])) {
      result = false;
      break;
    }
  }

  if (result && model != NULL) {
    eval_record_useful_terms(&evaluator);
    delete_evaluator(&evaluator);
    *model = mdl;
  } else {
    delete_evaluator(&evaluator);
    yices_free_model(mdl);
  }

  yices_release_mutex();

  return result;
}


/*
 * Check whether one of the terms a[0 .. n-1] is false.
 */
static bool trivially_false_assertions(const term_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i] == false_term) return true;
  }
  return false;
}


/*
 * Check whether the given delegate is supported
 * - return 0 if it's not supported.
 * - return 1 if delegate is NULL or it's the name of a supported delegate
 *
 * Which delegate is supported depends on how this version of Yices was compiled.
 */
EXPORTED int32_t yices_has_delegate(const char *delegate) {
  bool unknown;
  return delegate == NULL || supported_delegate(delegate, &unknown);
}


/*
 * Same thing but also set an error code.
 */
static bool check_delegate(const char *delegate) {
  bool unknown;

  assert(delegate != NULL);
  if (supported_delegate(delegate, &unknown)) {
    return true;
  }
  if (unknown) {
    set_error_code(CTX_UNKNOWN_DELEGATE);
  } else {
    set_error_code(CTX_DELEGATE_NOT_AVAILABLE);
  }
  return false;
}


/*
 * Check satisfiability of n formulas f[0 ... n-1]
 * - f[0 ... n-1] are known to be boolean terms
 */
static smt_status_t yices_do_check_formulas(const term_t f[], uint32_t n, const char *logic_name, model_t **result, const char *delegate) {
  context_t context;
  param_t default_params;
  model_t *model;
  smt_logic_t logic;
  context_arch_t arch;
  bool iflag, qflag;
  int32_t code;
  smt_status_t status;

  // check the logic first
  if (logic_name == NULL) {
    logic = SMT_UNKNOWN;
    arch = CTX_ARCH_EGFUNSPLXBV;
    iflag = true;
    qflag = false;
  } else {
    logic = smt_logic_code(logic_name);
    if (logic == SMT_UNKNOWN) {
      set_error_code(CTX_UNKNOWN_LOGIC);
      return STATUS_ERROR;
    }
    if (! logic_is_supported(logic) ||
	(! yices_has_mcsat() && logic_requires_mcsat(logic))) {
      set_error_code(CTX_LOGIC_NOT_SUPPORTED);
      return STATUS_ERROR;
    }

    arch = arch_for_logic(logic);
    iflag = iflag_for_logic(logic);
    qflag = qflag_for_logic(logic);
  }

  // validate the delegate if given
  if (logic == QF_BV && delegate != NULL && !check_delegate(delegate)) {
    return STATUS_ERROR;
  }

  // check for trivial unsat then trivial sat
  if (trivially_false_assertions(f, n)) {
    return STATUS_UNSAT;
  }

  if (trivially_true_assertions(f, n, result)) {
    return STATUS_SAT;
  }

  // initialize the context and assert the formulas
  yices_obtain_mutex();
  init_context(&context, __yices_globals.terms, logic, CTX_MODE_ONECHECK, arch, qflag);
  context_set_default_options(&context, logic, arch, iflag, qflag);
  code = assert_formulas(&context, n, f);
  yices_release_mutex();

  if (code < 0) {
    // error in assert_formulas
    convert_internalization_error(code);
    status = STATUS_ERROR;
    goto cleanup;
  }

  // check satisfiability
  if (logic == QF_BV && delegate != NULL) {
    status = check_with_delegate(&context, delegate, 0);
  } else {
    yices_default_params_for_context(&context, &default_params);
    status = check_context(&context, &default_params);
  }

  // get the model
  if (status == STATUS_SAT && result != NULL) {
    // yices_get_model takes the lock so we don't
    // need to do it ourselves.
    model = yices_get_model(&context, true);
    assert(model != NULL);
    *result = model;
  }

 cleanup:
  delete_context(&context);
  return status;
}



/*
 * Check whether a formula is satisfiable
 * - f = formula
 * - logic = SMT name for a logic (or NULL)
 * - model = resulting model (or NULL if no model is needed)
 * - delegate = external solver to use or NULL
 *
 * This function first check whether f is trivially sat or trivially unsat.
 * If not, it construct a context configured for the specified logic, then
 * assert f in this context and check whether the context is satisfiable.
 *
 * The return value is
 *   STATUS_SAT if f is satisfiable,
 *   STATUS_UNSAT if f is not satisifiable
 *   STATUS_ERROR if something goes wrong
 *
 * If the formula is satisfiable and model != NULL, then a model of f is returned in *model.
 * That model must be deleted when no-longer needed by calling yices_free_model.
 *
 * The logic must be either NULL or the name of an SMT logic supported by Yices.
 * If the logic is NULL, the function uses a default context configuration.
 * Ohterwise, the function uses a context specialized for the logic.
 *
 * The delegate is an optional argument used only when logic is "QF_BV".
 * If is ignored otherwise.   It must be the name of a third-party SAT solver
 * to use after bit-blasting. Currently, the delegate can be either "cadical",
 * "cryptominisat",  "y2sat", or NULL.
 * If delegate is NULL, the default SAT solver is used.
 *
 * Support for "cadical" and "cryptominisat" must be enabled at compilation
 * time. The "y2sat" solver is always available. The function will return STATUS_ERROR
 * and store an error code if the requested delegate is not available.
 *
 * Error codes:
 *
 * if f is invalid
 *   code = INVALID_TERM
 *   term1 = f
 *
 * if f is not Boolean
 *   code = TYPE_MISMATCH
 *   term1 = t
 *   type1 = bool
 *
 * if logic is not a known logic name
 *   code = CTX_UNKNOWN_LOGIC
 *
 * if the logic is known but not supported by Yices
 *   code = CTX_LOGIC_NOT_SUPPORTED
 *
 * if delegate is not one of "cadical", "cryptominisat", "y2sat"
 *   code = CTX_UNKNOWN_DELEGATE
 *
 * if delegate is "cadical" or "cryptominisat" but support for these SAT solvers
 * was not implemented at compile time,
 *   code = CTX_DELEGATE_NOT_AVAILABLE
 *
 * other error codes are possible if the formula is not in the specified logic (cf, yices_assert_formula)
 */
EXPORTED smt_status_t yices_check_formula(term_t f, const char *logic, model_t **model, const char *delegate) {
  if (! yices_assert_formula_checks(f)) {
    return STATUS_ERROR;
  }
  return yices_do_check_formulas(&f, 1, logic, model, delegate);
}

/*
 * Check whether n formulas are satisfiable.
 * - f = array of n Boolean terms
 * - n = number of elements in f
 *
 * This is similar to yices_check_formula except that it checks whether
 * the conjunction of f[0] ... f[n-1] is satisfiable.
 */
EXPORTED smt_status_t yices_check_formulas(const term_t f[], uint32_t n, const char *logic, model_t **model, const char *delegate) {
  if (! yices_assert_formulas_checks(n, f)) {
    return STATUS_ERROR;
  }
  return yices_do_check_formulas(f, n, logic, model, delegate);
}


/************************************
 *  BIT-BLAST AND EXPORT TO DIMACS  *
 ***********************************/

/*
 * Bit-blast f[0 ... n-1]
 * - filename = DIMACS file name
 * - simplify_cnf = whether to simplify after CNF conversion (using y2sat)
 * - status = returned status if the formulas are SAT or UNSAT
 */
static int32_t yices_do_export_to_dimacs(const term_t f[], uint32_t n, const char *filename, bool simplify_cnf, smt_status_t *status) {
  context_t context;
  context_arch_t arch;
  bool iflag, qflag;
  int32_t code;

  if (trivially_false_assertions(f, n)) {
    *status = STATUS_UNSAT;
    return 0;
  }

  if (trivially_true_assertions(f, n, NULL)) {
    *status = STATUS_SAT;
    return 0;
  }

  arch = arch_for_logic(QF_BV);
  iflag = iflag_for_logic(QF_BV);
  qflag = qflag_for_logic(QF_BV);

  yices_obtain_mutex();
  init_context(&context, __yices_globals.terms, QF_BV, CTX_MODE_ONECHECK, arch, qflag);
  context_set_default_options(&context, QF_BV, arch, iflag, qflag);
  code = assert_formulas(&context, n, f);
  yices_release_mutex();

  if (code < 0) {
    // error in assert_formulas
    convert_internalization_error(code);
    code = -1;
    goto done;
  }

  if (code == TRIVIALLY_UNSAT) {
    *status = STATUS_UNSAT;
    code = 0;
    goto done;
  }

  assert(code == CTX_NO_ERROR);

  if (simplify_cnf) {
    code = process_then_export_to_dimacs(&context, filename, status);
  } else {
    code = bitblast_then_export_to_dimacs(&context, filename, status);
  }
  if (code < 0) {
    // error in creating or writing to the file
    code = -1;
    file_output_error();
  }

 done:
  delete_context(&context);
  return code;
}

/*
 * Bit-blast then export the CNF to a file
 * - f = a Boolean formula (in the QF_BV theory)
 * - filename = name of the ouput file
 * - simplify_cnf = boolean flag
 * - stat = pointer to a variable that stores the formula's status
 *
 * Return code:
 *   1 if the DIMACS file was constructed
 *   0 if the formula is solved without CNF or after simplifying
 *  -1 if there's an error
 *
 * Error reports:
 */
EXPORTED int32_t yices_export_formula_to_dimacs(term_t f, const char *filename, int32_t simplify_cnf, smt_status_t *status) {
  if (! yices_assert_formula_checks(f)) {
    return -1;
  }
  return yices_do_export_to_dimacs(&f, 1, filename, simplify_cnf != 0, status);
}

/*
 * Bit-blast n formulas then export the CNF to a file
 * - f = array of n Boolean formula (in the QF_BV theory)
 * - n = number of formulas in f
 * - filename = name of the ouput file
 * - simplify_cnf = boolean flag
 * - stat = pointer to a variable that stores the formula's status
 *
 * Return code:
 *   1 if the DIMACS file was constructed
 *   0 if the formula is solved without CNF or after simplifying
 *  -1 if there's an error
 *
 * Error reports:
 */
EXPORTED int32_t yices_export_formulas_to_dimacs(const term_t f[], uint32_t n, const char *filename,
						 int32_t simplify_cnf, smt_status_t *status) {
  if (! yices_assert_formulas_checks(n, f)) {
    return -1;
  }
  return yices_do_export_to_dimacs(f, n, filename, simplify_cnf != 0, status);
}



/************************
 *  VALUES IN A MODEL   *
 ***********************/

/*
 * Convert a negative evaluation code v to
 * the corresponding yices error code.
 * - v is a code returned by eval_in_model or get_implicant
 */
#define NUM_EVAL_ERROR_CODES ((-MDL_EVAL_FORMULA_FALSE) + 1)

static const error_code_t eval_error2code[NUM_EVAL_ERROR_CODES] = {
  NO_ERROR,              // v = 0
  EVAL_FAILED,           // v = null_value (-1)
  INTERNAL_EXCEPTION,    // v = MDL_EVAL_INTERNAL_ERROR (-2)
  EVAL_UNKNOWN_TERM,     // v = MDL_EVAL_UNKNOWN_TERM (-3)
  EVAL_FREEVAR_IN_TERM,  // v = MDL_EVAL_FREEVAR_IN_TERM (4)
  EVAL_QUANTIFIER,       // v = MDL_EVAL_QUANTIFIER (-5)
  EVAL_LAMBDA,           // v = MDL_EVAL_LAMBDA (-6)
  EVAL_FAILED,           // v = MDL_EVAL_FAILED (-7)
  EVAL_NO_IMPLICANT,     // v = MDL_EVAL_FALSE (-8)
};

static inline error_code_t yices_eval_error(int32_t v) {
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
EXPORTED int32_t yices_get_bool_value(model_t *mdl, term_t t, int32_t *val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_get_bool_value(mdl, t, val));
}

int32_t _o_yices_get_bool_value(model_t *mdl, term_t t, int32_t *val) {
  value_table_t *vtbl;
  value_t v;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_boolean_term(__yices_globals.manager, t)) {
    return -1;
  }

  v = model_get_term_value(mdl, t);
  if (v < 0) {
    set_error_code(yices_eval_error(v));
    return -1;
  }

  vtbl = model_get_vtbl(mdl);
  if (! object_is_boolean(vtbl, v)) {
    set_error_code(INTERNAL_EXCEPTION);
    return -1;
  }

  *val = boolobj_value(vtbl, v);

  return 0;
}


/*
 * Value of arithmetic term t: it can be returned as an integer, a
 * rational (pair num/den), converted to a double, using the GMP
 * mpz_t and mpq_t representations, or as a libpoly algebraic number.
 *
 * Error codes:
 * If t is not an arithmetic term:
 *   code = ARITH_TERM_REQUIRED
 *   term1 = t
 * If t's value does not fit in the *val object
 *   code = EVAL_OVERFLOW
 */

typedef enum arithval_tag {
  ARITHVAL_ERROR,
  ARITHVAL_RATIONAL,
  ARITHVAL_ALGEBRAIC,
} arithval_tag_t;

/*
 * Tagged union to represent pointers to either rational or algebraic numbers.
 * The flag can ERROR/RATIONAL/ALGEBRAIC
 */
typedef struct arithval_struct_s {
  arithval_tag_t tag;
  union {
    rational_t *q;
    lp_algebraic_number_t *p;
  } val;
} arithval_struct_t;



/*
 * Auxiliary function: return the rational value of t
 * - store the result in *r
 * - if there's an error, set r->tag to ERROR and store an error report
 */
static void yices_get_arith_value(model_t *mdl, term_t t, arithval_struct_t *r) {
  value_table_t *vtbl;
  value_t v;

  r->tag = ARITHVAL_ERROR;
  r->val.q = NULL;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_arith_term(__yices_globals.manager, t)){
    return;
  }

  v = model_get_term_value(mdl, t);
  if (v < 0) {
    set_error_code(yices_eval_error(v));
    return;
  }

  vtbl = model_get_vtbl(mdl);
  if (object_is_rational(vtbl, v)) {
    r->tag = ARITHVAL_RATIONAL;
    r->val.q = vtbl_rational(vtbl, v);
  } else if (object_is_algebraic(vtbl, v)) {
    r->tag = ARITHVAL_ALGEBRAIC;
    r->val.p = vtbl_algebraic_number(vtbl, v);
  } else {
    // should not happen since t is an arithmetic term
    set_error_code(INTERNAL_EXCEPTION);
  }
}

/*
 * Check whether r->tag is RATIONAL, if not report an error: CONVERSION_FAILED
 */
static bool arithval_is_rational(const arithval_struct_t *r) {
  bool result;

  result = r->tag == ARITHVAL_RATIONAL;
  if (r->tag == ARITHVAL_ALGEBRAIC) {
    set_error_code(EVAL_CONVERSION_FAILED);
  }
  return result;
}

// return the value as a 32bit integer
EXPORTED int32_t yices_get_int32_value(model_t *mdl, term_t t, int32_t *val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_get_int32_value(mdl, t, val));
}

int32_t _o_yices_get_int32_value(model_t *mdl, term_t t, int32_t *val) {
  arithval_struct_t aux;

  yices_get_arith_value(mdl, t, &aux);
  if (! arithval_is_rational(&aux)) {
    return -1;
  }

  if (! q_get32(aux.val.q, val)) {
    set_error_code(EVAL_OVERFLOW);
    return -1;
  }

  return 0;
}

// return the value as a 64bit integer
EXPORTED int32_t yices_get_int64_value(model_t *mdl, term_t t, int64_t *val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_get_int64_value(mdl, t, val));
}

int32_t _o_yices_get_int64_value(model_t *mdl, term_t t, int64_t *val) {
  arithval_struct_t aux;

  yices_get_arith_value(mdl, t, &aux);
  if (! arithval_is_rational(&aux)) {
    return -1;
  }

  if (! q_get64(aux.val.q, val)) {
    set_error_code(EVAL_OVERFLOW);
    return -1;
  }

  return 0;
}

// return the value as a pair num/den (both 32bit integers)
EXPORTED int32_t yices_get_rational32_value(model_t *mdl, term_t t, int32_t *num, uint32_t *den) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_get_rational32_value(mdl, t, num, den));
}

int32_t _o_yices_get_rational32_value(model_t *mdl, term_t t, int32_t *num, uint32_t *den) {
  arithval_struct_t aux;

  yices_get_arith_value(mdl, t, &aux);
  if (! arithval_is_rational(&aux)) {
    return -1;
  }

  if (! q_get_int32(aux.val.q, num, den)) {
    set_error_code(EVAL_OVERFLOW);
    return -1;
  }

  return 0;
}

// pair num/den (64bit integers)
EXPORTED int32_t yices_get_rational64_value(model_t *mdl, term_t t, int64_t *num, uint64_t *den) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_get_rational64_value(mdl, t, num, den));
}

int32_t _o_yices_get_rational64_value(model_t *mdl, term_t t, int64_t *num, uint64_t *den) {
  arithval_struct_t aux;

  yices_get_arith_value(mdl, t, &aux);
  if (! arithval_is_rational(&aux)) {
    return -1;
  }

  if (! q_get_int64(aux.val.q, num, den)) {
    set_error_code(EVAL_OVERFLOW);
    return -1;
  }

  return 0;
}

// convert to a floating point number
EXPORTED int32_t yices_get_double_value(model_t *mdl, term_t t, double *val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_get_double_value(mdl, t, val));
}

int32_t _o_yices_get_double_value(model_t *mdl, term_t t, double *val) {
  arithval_struct_t aux;

  yices_get_arith_value(mdl, t, &aux);
  if (aux.tag == ARITHVAL_RATIONAL) {
    *val = q_get_double(aux.val.q);
    return 0;
  }

#if HAVE_MCSAT
  if (aux.tag == ARITHVAL_ALGEBRAIC) {
    *val = lp_algebraic_number_to_double(aux.val.p);
    return 0;
  }
#endif

  return -1;
}


// convert to a GMP integer
EXPORTED int32_t yices_get_mpz_value(model_t *mdl, term_t t, mpz_t val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_get_mpz_value(mdl, t, val));
}

int32_t _o_yices_get_mpz_value(model_t *mdl, term_t t, mpz_t val) {
  arithval_struct_t aux;

  yices_get_arith_value(mdl, t, &aux);
  if (! arithval_is_rational(&aux)) {
    return -1;
  }

  if (!q_get_mpz(aux.val.q, val)) {
    // the value is not an integer (maybe we should use a better error code
    // in this case?)
    set_error_code(EVAL_OVERFLOW);
    return -1;
  }

  return 0;
}

// convert to a GMP rational
EXPORTED int32_t yices_get_mpq_value(model_t *mdl, term_t t, mpq_t val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_get_mpq_value(mdl, t, val));
}

int32_t _o_yices_get_mpq_value(model_t *mdl, term_t t, mpq_t val) {
  arithval_struct_t aux;

  yices_get_arith_value(mdl, t, &aux);
  if (! arithval_is_rational(&aux)) {
    return -1;
  }

  q_get_mpq(aux.val.q, val);

  return 0;
}


/*
 * Algebraic number
 */
EXPORTED int32_t yices_get_algebraic_number_value(model_t *mdl, term_t t, lp_algebraic_number_t *a) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_get_algebraic_number_value(mdl, t, a));
}

int32_t _o_yices_get_algebraic_number_value(model_t *mdl, term_t t, lp_algebraic_number_t *a) {
#if HAVE_MCSAT
  arithval_struct_t aux;

  yices_get_arith_value(mdl, t, &aux);
  if (aux.tag == ARITHVAL_ALGEBRAIC) {
    lp_algebraic_number_construct_copy(a, aux.val.p);
    return 0;
  }

  // TODO: convert rational to algebraic (no direct way to do this in libpoly)
  if (aux.tag == ARITHVAL_RATIONAL) {
    set_error_code(EVAL_CONVERSION_FAILED);
    return -1;
  }

  return -1;

#else
  // NO SUPPORT FOT MCSAT
  set_error_code(EVAL_NOT_SUPPORTED);
  return -1;
#endif
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
EXPORTED int32_t yices_get_bv_value(model_t *mdl, term_t t, int32_t val[]) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_get_bv_value(mdl, t, val));
}

int32_t _o_yices_get_bv_value(model_t *mdl, term_t t, int32_t val[]) {
  value_table_t *vtbl;
  value_bv_t *bv;
  value_t v;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_bitvector_term(__yices_globals.manager, t)) {
    return -1;
  }

  v = model_get_term_value(mdl, t);
  if (v < 0) {
    set_error_code(yices_eval_error(v));
    return -1;
  }

  vtbl = model_get_vtbl(mdl);
  if (! object_is_bitvector(vtbl, v)) {
    set_error_code(INTERNAL_EXCEPTION);
    return -1;
  }

  bv = vtbl_bitvector(vtbl, v);
  bvconst_get_array(bv->data, val, bv->nbits);

  return 0;
}



/*
 * Value of term t of uninterpreted or scalar type
 * - the value is returned as a constant index in *val
 *   (with the same meaning as in function yices_constant):
 * - if t has type tau and tau is a scalar type of size n then
 *   the function returns an index k between 0 and n-1
 * - if tau is an uninterpreted type, then the function returns an
 *   integer index k
 *
 * Error codes:
 * - if t does not have a scalar or uninterpreted type:
 *   code = SCALAR_TERM_REQUIRED
 *   term1 = t
 */
EXPORTED int32_t yices_get_scalar_value(model_t *mdl, term_t t, int32_t *val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_get_scalar_value(mdl, t, val));
}

int32_t _o_yices_get_scalar_value(model_t *mdl, term_t t, int32_t *val) {
  value_table_t *vtbl;
  value_unint_t *uv;
  value_t v;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_scalar_term(__yices_globals.manager, t)) {
    return -1;
  }

  v = model_get_term_value(mdl, t);
  if (v < 0) {
    set_error_code(yices_eval_error(v));
    return -1;
  }

  vtbl = model_get_vtbl(mdl);
  if (! object_is_unint(vtbl, v)) {
    set_error_code(INTERNAL_EXCEPTION);
    return -1;
  }

  uv = vtbl_unint(vtbl, v);
  *val = uv->index;

  return 0;
}


/*
 * FULL MODEL: NODES AND VALUE DESCRIPTORS
 */

/*
 * Vectors of node descriptors
 */
EXPORTED void yices_init_yval_vector(yval_vector_t *v) {
  init_yval_vector(v);
}

EXPORTED void yices_reset_yval_vector(yval_vector_t *v) {
  reset_yval_vector(v);
}

EXPORTED void yices_delete_yval_vector(yval_vector_t *v) {
  delete_yval_vector(v);
}

/*
 * Value of term t stored as a node descriptor in *val.
 *
 * The function returns 0 it t's value can be computed, -1 otherwise.
 *
 * Error codes are as in all evaluation functions.
 * If t is not valid:
 *   code = INVALID_TERM
 *   term1 = t
 * If t contains a subterm whose value is not known
 *   code = EVAL_UNKNOWN_TERM
 * If t contains free variables
 *   code = EVAL_FREEVAR_IN_TERM
 * If t contains quantifier(s)
 *   code = EVAL_QUANTIFIER
 * If t contains lambda terms
 *   code = EVAL_LAMBDA
 * If the evaluation fails for other reasons:
 *   code = EVAL_FAILED
 */
EXPORTED int32_t yices_get_value(model_t *mdl, term_t t, yval_t *val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_get_value(mdl, t, val));
}

int32_t _o_yices_get_value(model_t *mdl, term_t t, yval_t *val) {
  value_table_t *vtbl;
  value_t v;

  if (! check_good_term(__yices_globals.manager, t)) {
    return -1;
  }

  v = model_get_term_value(mdl, t);
  if (v < 0) {
    set_error_code(yices_eval_error(v));
    return -1;
  }

  vtbl = model_get_vtbl(mdl);
  get_yval(vtbl, v, val);

  return 0;
}


/*
 * Queries on the value of a rational node
 */
EXPORTED int32_t yices_val_is_int32(model_t *mdl, const yval_t *v) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_is_int32(mdl, v));
}

int32_t _o_yices_val_is_int32(model_t *mdl, const yval_t *v) {
  value_table_t *vtbl;
  rational_t *q;
  value_t id;
  int32_t code;

  code = false;
  if (v->node_tag == YVAL_RATIONAL) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_rational(vtbl, id)) {
      q = vtbl_rational(vtbl, id);
      code = q_is_int32(q);
    }
  }

  return code;
}

EXPORTED int32_t yices_val_is_int64(model_t *mdl, const yval_t *v) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_is_int64(mdl, v));
}

int32_t _o_yices_val_is_int64(model_t *mdl, const yval_t *v) {
  value_table_t *vtbl;
  rational_t *q;
  value_t id;
  int32_t code;

  code = false;
  if (v->node_tag == YVAL_RATIONAL) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_rational(vtbl, id)) {
      q = vtbl_rational(vtbl, id);
      code = q_is_int64(q);
    }
  }

  return code;
}

EXPORTED int32_t yices_val_is_rational32(model_t *mdl, const yval_t *v) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_is_rational32(mdl, v));
}

int32_t _o_yices_val_is_rational32(model_t *mdl, const yval_t *v) {
  value_table_t *vtbl;
  rational_t *q;
  value_t id;
  int32_t code;

  code = false;
  if (v->node_tag == YVAL_RATIONAL) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_rational(vtbl, id)) {
      q = vtbl_rational(vtbl, id);
      code = q_fits_int32(q);
    }
  }

  return code;
}

EXPORTED int32_t yices_val_is_rational64(model_t *mdl, const yval_t *v) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_is_rational64(mdl, v));
}

int32_t _o_yices_val_is_rational64(model_t *mdl, const yval_t *v) {
  value_table_t *vtbl;
  rational_t *q;
  value_t id;
  int32_t code;

  code = false;
  if (v->node_tag == YVAL_RATIONAL) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_rational(vtbl, id)) {
      q = vtbl_rational(vtbl, id);
      code = q_fits_int64(q);
    }
  }

  return code;
}

EXPORTED int32_t yices_val_is_integer(model_t *mdl, const yval_t *v) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_is_integer(mdl, v));
}

int32_t _o_yices_val_is_integer(model_t *mdl, const yval_t *v) {
  value_table_t *vtbl;
  rational_t *q;
  value_t id;
  int32_t code;

  code = false;
  if (v->node_tag == YVAL_RATIONAL) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_rational(vtbl, id)) {
      q = vtbl_rational(vtbl, id);
      code = q_is_integer(q);
    }
  }

  return code;
}

/*
 * Number of bits in a bitvector constant
 */
EXPORTED uint32_t yices_val_bitsize(model_t *mdl, const yval_t *v) {
  MT_PROTECT(uint32_t,  __yices_globals.lock, _o_yices_val_bitsize(mdl, v));
}

uint32_t _o_yices_val_bitsize(model_t *mdl, const yval_t *v) {
  value_table_t *vtbl;
  value_bv_t *bv;
  value_t id;
  uint32_t n;

  n = 0;
  if (v->node_tag == YVAL_BV) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_bitvector(vtbl, id)) {
      bv = vtbl_bitvector(vtbl, id);
      n = bv->nbits;
    }
  }

  return n;
}


/*
 * Number of components in a tuple
 */
EXPORTED uint32_t yices_val_tuple_arity(model_t *mdl, const yval_t *v) {
  MT_PROTECT(uint32_t,  __yices_globals.lock, _o_yices_val_tuple_arity(mdl, v));
}

uint32_t _o_yices_val_tuple_arity(model_t *mdl, const yval_t *v) {
  value_table_t *vtbl;
  value_tuple_t *tuple;
  value_t id;
  uint32_t n;

  n = 0;
  if (v->node_tag == YVAL_TUPLE) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_tuple(vtbl, id)) {
      tuple = vtbl_tuple(vtbl, id);
      n = tuple->nelems;
    }
  }

  return n;
}


/*
 * Arity of a mapping object
 */
EXPORTED uint32_t yices_val_mapping_arity(model_t *mdl, const yval_t *v) {
  MT_PROTECT(uint32_t,  __yices_globals.lock, _o_yices_val_mapping_arity(mdl, v));
}

uint32_t _o_yices_val_mapping_arity(model_t *mdl, const yval_t *v) {
  value_table_t *vtbl;
  value_map_t *map;
  value_t id;
  uint32_t n;

  n = 0;
  if (v->node_tag == YVAL_MAPPING) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_map(vtbl, id)) {
      map = vtbl_map(vtbl, id);
      n = map->arity;
    }
  }

  return n;
}

/*
 * Arity of a function node
 */
EXPORTED uint32_t yices_val_function_arity(model_t *mdl, const yval_t *v) {
  MT_PROTECT(uint32_t,  __yices_globals.lock, _o_yices_val_function_arity(mdl, v));
}

uint32_t _o_yices_val_function_arity(model_t *mdl, const yval_t *v) {
  value_table_t *vtbl;
  value_t id;
  uint32_t n;

  n = 0;
  if (v->node_tag == YVAL_FUNCTION) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id)) {
      if (object_is_function(vtbl, id)) {
	n = vtbl_function(vtbl, id)->arity;
      } else if (object_is_update(vtbl, id)) {
	n = vtbl_update(vtbl, id)->arity;
      }
    }
  }

  return n;
}

/*
 * Type of a function node
 */
EXPORTED type_t yices_val_function_type(model_t *mdl, const yval_t *v) {
  MT_PROTECT(type_t,  __yices_globals.lock, _o_yices_val_function_type(mdl, v));
}

type_t _o_yices_val_function_type(model_t *mdl, const yval_t *v) {
  value_table_t *vtbl;
  value_t id;

  if (v->node_tag == YVAL_FUNCTION) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) &&
	(object_is_function(vtbl, id) || object_is_update(vtbl, id))) {
      return vtbl_function_type(vtbl, id);
    }
  } else {
    set_error_code(YVAL_INVALID_OP);
  }
  return NULL_TYPE;
}

/*
 * Extract value of a leaf node
 */
EXPORTED int32_t yices_val_get_bool(model_t *mdl, const yval_t *v, int32_t *val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_get_bool(mdl, v, val));
}

int32_t _o_yices_val_get_bool(model_t *mdl, const yval_t *v, int32_t *val) {
  value_table_t *vtbl;
  value_t id;

  if (v->node_tag == YVAL_BOOL) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_boolean(vtbl, id)) {
      *val = boolobj_value(vtbl, id);
      return 0;
    }
  } else {
    set_error_code(YVAL_INVALID_OP);
  }
  return -1;
}


/*
 * Auxiliary function: return the rational value of v
 * - return NULL and set error code to YVAL_INVALID_OP if v does not refer to a rational object
 */
static rational_t *yices_val_get_rational(model_t *mdl, const yval_t *v) {
  value_table_t *vtbl;
  value_t id;

  if (v->node_tag == YVAL_RATIONAL) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_rational(vtbl, id)) {
      return vtbl_rational(vtbl, id);
    }
  } else {
    set_error_code(YVAL_INVALID_OP);
  }
  return NULL;
}

EXPORTED int32_t yices_val_get_int32(model_t *mdl, const yval_t *v, int32_t *val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_get_int32(mdl, v, val));
}

int32_t _o_yices_val_get_int32(model_t *mdl, const yval_t *v, int32_t *val) {
  rational_t *q;

  q = yices_val_get_rational(mdl, v);
  if (q == NULL) {
    return -1;
  }

  if (! q_get32(q, val)) {
    set_error_code(YVAL_OVERFLOW);
    return -1;
  }

  return 0;
}

EXPORTED int32_t yices_val_get_int64(model_t *mdl, const yval_t *v, int64_t *val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_get_int64(mdl, v, val));
}

int32_t _o_yices_val_get_int64(model_t *mdl, const yval_t *v, int64_t *val) {
  rational_t *q;

  q = yices_val_get_rational(mdl, v);
  if (q == NULL) {
    return -1;
  }

  if (! q_get64(q, val)) {
    set_error_code(YVAL_OVERFLOW);
    return -1;
  }

  return 0;
}

EXPORTED int32_t yices_val_get_rational32(model_t *mdl, const yval_t *v, int32_t *num, uint32_t *den) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_get_rational32(mdl, v, num, den));
}

int32_t _o_yices_val_get_rational32(model_t *mdl, const yval_t *v, int32_t *num, uint32_t *den) {
  rational_t *q;

  q = yices_val_get_rational(mdl, v);
  if (q == NULL) {
    return -1;
  }

  if (! q_get_int32(q, num, den)) {
    set_error_code(YVAL_OVERFLOW);
    return -1;
  }

  return 0;
}

EXPORTED int32_t yices_val_get_rational64(model_t *mdl, const yval_t *v, int64_t *num, uint64_t *den) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_get_rational64(mdl, v, num, den));
}

int32_t _o_yices_val_get_rational64(model_t *mdl, const yval_t *v, int64_t *num, uint64_t *den) {
  rational_t *q;

  q = yices_val_get_rational(mdl, v);
  if (q == NULL) {
    return -1;
  }

  if (! q_get_int64(q, num, den)) {
    set_error_code(YVAL_OVERFLOW);
    return -1;
  }

  return 0;
}

EXPORTED int32_t yices_val_get_mpz(model_t *mdl, const yval_t *v, mpz_t val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_get_mpz(mdl, v, val));
}

int32_t _o_yices_val_get_mpz(model_t *mdl, const yval_t *v, mpz_t val) {
  rational_t *q;

  q = yices_val_get_rational(mdl, v);
  if (q == NULL) {
    return -1;
  }

  if (!q_get_mpz(q, val)) {
    set_error_code(EVAL_OVERFLOW);
    return -1;
  }

  return 0;
}

EXPORTED int32_t yices_val_get_mpq(model_t *mdl, const yval_t *v, mpq_t val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_get_mpq(mdl, v, val));
}

int32_t _o_yices_val_get_mpq(model_t *mdl, const yval_t *v, mpq_t val) {
  rational_t *q;

  q = yices_val_get_rational(mdl, v);
  if (q == NULL) {
    return -1;
  }
  q_get_mpq(q, val);

  return 0;
}


// Conversion to double
EXPORTED int32_t yices_val_get_double(model_t *mdl, const yval_t *v, double *val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_get_double(mdl, v, val));
}

int32_t _o_yices_val_get_double(model_t *mdl, const yval_t *v, double *val) {
  value_table_t *vtbl;
  value_t id;

  vtbl = model_get_vtbl(mdl);
  id = v->node_id;

  if (v->node_tag == YVAL_RATIONAL) {
    if (good_object(vtbl, id) && object_is_rational(vtbl, id)) {
      *val = q_get_double(vtbl_rational(vtbl, id));
      return 0;
    }
  }

#if HAVE_MCSAT
  if (v->node_tag == YVAL_ALGEBRAIC) {
    if (good_object(vtbl, id) && object_is_algebraic(vtbl, id)) {
      *val = lp_algebraic_number_to_double(vtbl_algebraic_number(vtbl, id));
      return 0;
    }
  }
#endif

  set_error_code(YVAL_INVALID_OP);
  return -1;
}

/*
 * Value of a bitvector node
 */
EXPORTED int32_t yices_val_get_bv(model_t *mdl, const yval_t *v, int32_t val[]) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_get_bv(mdl, v, val));
}

int32_t _o_yices_val_get_bv(model_t *mdl, const yval_t *v, int32_t val[]) {
  value_table_t *vtbl;
  value_bv_t *bv;
  value_t id;

  if (v->node_tag == YVAL_BV) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_bitvector(vtbl, id)) {
      bv = vtbl_bitvector(vtbl, id);
      bvconst_get_array(bv->data, val, bv->nbits);
      return 0;
    }
  } else {
    set_error_code(YVAL_INVALID_OP);
  }
  return -1;
}

/*
 * Algebraic number
 */
EXPORTED int32_t yices_val_get_algebraic_number(model_t *mdl, const yval_t *v, lp_algebraic_number_t *a) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_get_algebraic_number(mdl, v, a));
}

int32_t _o_yices_val_get_algebraic_number(model_t *mdl, const yval_t *v, lp_algebraic_number_t *a) {
#if HAVE_MCSAT
  value_table_t *vtbl;
  value_t id;

  if (v->node_tag == YVAL_ALGEBRAIC) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_algebraic(vtbl, id)) {
      lp_algebraic_number_construct_copy(a, vtbl_algebraic_number(vtbl, id));
      return 0;
    }
  } else {
    set_error_code(YVAL_INVALID_OP);
  }

#else
  set_error_code(YVAL_NOT_SUPPORTED);
#endif

  return -1;
}



/*
 * Value of a scalar/uninterpreted constant
 */
EXPORTED int32_t yices_val_get_scalar(model_t *mdl, const yval_t *v, int32_t *val, type_t *tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_get_scalar(mdl, v, val, tau));
}

int32_t _o_yices_val_get_scalar(model_t *mdl, const yval_t *v, int32_t *val, type_t *tau) {
  value_table_t *vtbl;
  value_unint_t *u;
  value_t id;

  if (v->node_tag == YVAL_SCALAR) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_unint(vtbl, id)) {
      u = vtbl_unint(vtbl, id);
      *tau = u->type;
      *val = u->index;
      return 0;
    }
  } else {
    set_error_code(YVAL_INVALID_OP);
  }
  return -1;
}


/*
 * Expand a tuple node
 */
EXPORTED int32_t yices_val_expand_tuple(model_t *mdl, const yval_t *v, yval_t child[]) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_expand_tuple(mdl, v, child));
}


int32_t _o_yices_val_expand_tuple(model_t *mdl, const yval_t *v, yval_t child[]) {
  value_table_t *vtbl;
  value_t id;

  if (v->node_tag == YVAL_TUPLE) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_tuple(vtbl, id)) {
      yval_expand_tuple(vtbl, id, child);
      return 0;
    }
  } else {
    set_error_code(YVAL_INVALID_OP);
  }
  return -1;
}


/*
 * Expand a mapping node
 */
EXPORTED int32_t yices_val_expand_mapping(model_t *mdl, const yval_t *v, yval_t tup[], yval_t *val) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_expand_mapping(mdl, v, tup, val));
}

int32_t _o_yices_val_expand_mapping(model_t *mdl, const yval_t *v, yval_t tup[], yval_t *val) {
  value_table_t *vtbl;
  value_t id;

  if (v->node_tag == YVAL_MAPPING) {
    vtbl = model_get_vtbl(mdl);
    id = v->node_id;
    if (good_object(vtbl, id) && object_is_map(vtbl, id)) {
      yval_expand_mapping(vtbl, id, tup, val);
      return 0;
    }
  } else {
    set_error_code(YVAL_INVALID_OP);
  }
  return -1;
}


/*
 * Expand a function node
 */
EXPORTED int32_t yices_val_expand_function(model_t *mdl, const yval_t *f, yval_t *def, yval_vector_t *v) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_val_expand_function(mdl, f, def, v));
}

int32_t _o_yices_val_expand_function(model_t *mdl, const yval_t *f, yval_t *def, yval_vector_t *v) {
  value_table_t *vtbl;
  value_t id;

  if (f->node_tag == YVAL_FUNCTION) {
    vtbl = model_get_vtbl(mdl);
    id = f->node_id;
    if (good_object(vtbl, id)) {
      if (object_is_function(vtbl, id)) {
	yval_expand_function(vtbl, id, v, def);
	return 0;
      }
      if (object_is_update(vtbl, id)) {
	yval_expand_update(vtbl, id, v, def);
	return 0;
      }
    }
  } else {
    set_error_code(YVAL_INVALID_OP);
  }
  return -1;
}


/*
 * VALUES AS CONSTANT TERMS
 */

/*
 * Value of term t converted to a constant term val.
 */
EXPORTED term_t yices_get_value_as_term(model_t *mdl, term_t t) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_get_value_as_term(mdl, t));
}

term_t _o_yices_get_value_as_term(model_t *mdl, term_t t) {
  value_table_t *vtbl;
  value_t v;
  term_t a;

  if (! check_good_term(__yices_globals.manager, t)) {
    return NULL_TERM;
  }

  v = model_get_term_value(mdl, t);
  if (v < 0) {
    set_error_code(yices_eval_error(v));
    return NULL_TERM;
  }

  vtbl = model_get_vtbl(mdl);
  a = convert_value_to_term(__yices_globals.terms, vtbl, v);
  if (a < 0) {
    set_error_code(EVAL_CONVERSION_FAILED);
    return NULL_TERM;
  }

  return a;
}



/*
 * TEST TRUTH-VALUE OF BOOLEAN TERMS
 */

/*
 * Check whether f is true in mdl
 * - the returned value is
 *     1 if f is true in mdl,
 *     0 if f is false in mdl,
 *    -1 if f's value can't be evaluated
 *
 * Error codes:
 * - same as get_bool_val
 */
EXPORTED int32_t yices_formula_true_in_model(model_t *mdl, term_t f) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_formula_true_in_model(mdl, f));
}

int32_t _o_yices_formula_true_in_model(model_t *mdl, term_t f) {
  int32_t code;

  if (! check_good_term(__yices_globals.manager, f) ||
      ! check_boolean_term(__yices_globals.manager, f)) {
    return -1;
  }

  if (formula_holds_in_model(mdl, f, &code)) {
    assert(code >= 0);
    return 1; // true
  } else if (code >= 0) {
    return 0; // false
  } else {
    // code < 0: contains the evaluation error
    set_error_code(yices_eval_error(code));
    return -1;
  }
}


/*
 * Check whether formulas f[0 ... n-1] are all true in mdl
 * - the returned value is as in the previous function:
 *     1 if all f[i] are true
 *     0 if one f[i] is false (and f[0 ... i-1] are all true)
 *    -1 if one f[i] can't be evaluated
 * Error code:
 * - same as yices_get_bool_val
 */
EXPORTED int32_t yices_formulas_true_in_model(model_t *mdl, uint32_t n, const term_t f[]) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_formulas_true_in_model(mdl, n, f));
}

int32_t _o_yices_formulas_true_in_model(model_t *mdl, uint32_t n, const term_t f[]) {
  int32_t code;

  if (! check_good_terms(__yices_globals.manager, n, f) ||
      ! check_boolean_args(__yices_globals.manager, n, f)) {
    return -1;
  }

  if (formulas_hold_in_model(mdl, n, f, &code)) {
    assert(code >= 0);
    return 1; // all true
  } else if (code >= 0) {
    return 0; // at least one false
  } else {
    // error in evaluation: code contains the eval code
    set_error_code(yices_eval_error(code));
    return -1;
  }
}




/*
 * ARRAYS
 */

/*
 * Values of terms a[0 ... n-1] all converted to terms
 */
EXPORTED int32_t yices_term_array_value(model_t *mdl, uint32_t n, const term_t a[], term_t b[]) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_term_array_value(mdl, n, a, b));
}

int32_t _o_yices_term_array_value(model_t *mdl, uint32_t n, const term_t a[], term_t b[]) {
  int32_t eval_code;
  uint32_t count;

  if (! check_good_terms(__yices_globals.manager, n, a)) {
    return -1;
  }

  eval_code = evaluate_term_array(mdl, n, a, b);
  if (eval_code < 0) {
    set_error_code(yices_eval_error(eval_code));
    return -1;
  }

  count = convert_value_array(__yices_globals.terms, model_get_vtbl(mdl), n, b);
  if (count < n) {
    set_error_code(EVAL_CONVERSION_FAILED);
    return -1;
  }

  return 0;
}





/*
 * IMPLICANTS
 */

/*
 * Given a model mdl and a Boolean term t that is true in mdl, return an implicant for t
 * - the implicant is a list of literals a[0 ... n-1] such that
 *   every a[i] is true in mdl
 *   the conjunction a[0] /\ a[1] /\ ... /\ a[n-1] implies t
 *
 * The function returns a[0 ... n-1] in a term_vector v that must be initialized (by
 * yices_init_term_vector).
 *
 * The function returns 0 if all goes well or -1 if there's an error
 *
 * Error codes:
 * - INVALID_TERM         if t is not valid
 * - TYPE_MISMATCH        if t is not a Boolean term
 * - EVAL_FREEVAR_IN_TERM if t contains free variables
 * - EVAL_QUANTIFIER     if t contains quantifiers
 * - EVAL_LAMBDA          if t contains a lambda
 * - EVAL_NO_IMPLICANT    if t is false in  mdl
 * - EVAL_FAILED          if the function fails for some other reason
 */
EXPORTED int32_t yices_implicant_for_formula(model_t *mdl, term_t t, term_vector_t *v) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_implicant_for_formula(mdl, t, v));
}

int32_t _o_yices_implicant_for_formula(model_t *mdl, term_t t, term_vector_t *v) {
  int32_t code;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_boolean_term(__yices_globals.manager, t)) {
    return -1;
  }

  v->size = 0;
  code = get_implicant(mdl, __yices_globals.manager, LIT_COLLECTOR_ALL_OPTIONS, 1, &t, (ivector_t *) v);
  if (code < 0) {
    set_error_code(yices_eval_error(code));
    return -1;
  }

  return 0;
}


/*
 * Same thing for an array of formulas a[0 ... n-1]
 */
EXPORTED int32_t yices_implicant_for_formulas(model_t *mdl, uint32_t n, const term_t a[], term_vector_t *v) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_implicant_for_formulas(mdl, n, a, v));
}

int32_t _o_yices_implicant_for_formulas(model_t *mdl, uint32_t n, const term_t a[], term_vector_t *v) {
  int32_t code;

  if (! check_good_terms(__yices_globals.manager, n, a) ||
      ! check_boolean_args(__yices_globals.manager, n, a)) {
    return -1;
  }

  v->size = 0;
  code = get_implicant(mdl, __yices_globals.manager, LIT_COLLECTOR_ALL_OPTIONS, n, a, (ivector_t *) v);
  if (code < 0) {
    set_error_code(yices_eval_error(code));
    return -1;
  }

  return 0;
}



/*
 * MODEL GENERALIZATION
 */

/*
 * Convert a negative error code v from generalization.h into the
 * corresponding yices error code.
 */
#define NUM_GEN_ERROR_CODES ((-GEN_PROJ_ERROR_BAD_ARITH_LITERAL)+1)

static const error_code_t gen_error2code[NUM_GEN_ERROR_CODES] = {
  NO_ERROR,                  // 0
  MDL_GEN_FAILED,            // NULL_TERM,
  INTERNAL_EXCEPTION,        // GEN_EVAL_INTERNAL_ERROR
  EVAL_UNKNOWN_TERM,         // GEN_EVAL_UNKNOWN_TERM
  EVAL_FREEVAR_IN_TERM,      // GEN_EVAL_FREEVAR_IN_TERM
  EVAL_QUANTIFIER,           // GEN_EVAL_QUANTIFIER
  EVAL_LAMBDA,               // GEN_EVAL_LAMBDA
  MDL_GEN_FAILED,            // GEN_EVAL_FAILED
  EVAL_NO_IMPLICANT,         // GEN_EVAL_FORMULA_FALSE
  MDL_GEN_FAILED,            // GEN_CONV_INTERNAL_ERROR
  EVAL_CONVERSION_FAILED,    // GEN_CONV_UNKNOWN_VALUE
  EVAL_CONVERSION_FAILED,    // GEN_CONV_NOT_PRIMITIVE
  EVAL_CONVERSION_FAILED,    // GEN_CONV_FUNCTION
  EVAL_CONVERSION_FAILED,    // GEN_CONV_FAILED
  MDL_GEN_NONLINEAR,         // GEN_PROJ_ERROR_NON_LINEAR
  MDL_GEN_FAILED,            // GEN_PROJ_ERROR_IN_EVAL
  MDL_GEN_FAILED,            // GEN_PROJ_ERROR_IN_CONVERT
  MDL_GEN_FAILED,            // GEN_PROJ_ERROR_IN_SUBST
  MDL_GEN_FAILED,            // GEN_PROJ_ERROR_BAD_ARITH_LITERAL
};

static inline error_code_t yices_gen_error(int32_t v) {
  assert(0 <= -v && v < NUM_GEN_ERROR_CODES);
  return gen_error2code[-v];
}


/*
 * Given a model mdl for a formula F(X, Y). The following generalization functions
 * eliminate variables Y from F(X, Y) in a way that is guided by the model.
 *
 * - nelims = number of variables to eliminate
 * - elim = variables to eliminate
 * - each term in elim[i] must be an uninterpreted term (as returned by yices_new_uninterpreted_term)
 *   of one of the following types: Boolean, (bitvector k), or Real
 * - mode defines the generalization algorithm
 * - v: term_vector to return the result
 *
 */
EXPORTED int32_t yices_generalize_model(model_t *mdl, term_t t, uint32_t nelims, const term_t elim[],
					yices_gen_mode_t mode, term_vector_t *v) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_generalize_model(mdl, t, nelims, elim, mode, v));
}

int32_t _o_yices_generalize_model(model_t *mdl, term_t t, uint32_t nelims, const term_t elim[],
					yices_gen_mode_t mode, term_vector_t *v) {
  int32_t code;

  if (! check_good_term(__yices_globals.manager, t) ||
      ! check_boolean_term(__yices_globals.manager, t) ||
      ! check_elim_vars(__yices_globals.manager, nelims, elim)) {
    return -1;
  }

  v->size = 0;
  switch (mode) {
  case YICES_GEN_BY_SUBST:
    code = gen_model_by_substitution(mdl, __yices_globals.manager, 1, &t, nelims, elim, (ivector_t *) v);
    break;

  case YICES_GEN_BY_PROJ:
    code = gen_model_by_projection(mdl, __yices_globals.manager, 1, &t, nelims, elim, (ivector_t *) v);
    break;

  default:
    code = generalize_model(mdl, __yices_globals.manager, 1, &t, nelims, elim, (ivector_t *) v);
    break;
  }

  if (code < 0) {
    set_error_code(yices_gen_error(code));
    return -1;
  }

  return 0;
}


/*
 * Same thing for a conjunction of formulas a[0 ... n-1]
 */
EXPORTED term_t yices_generalize_model_array(model_t *mdl, uint32_t n, const term_t a[], uint32_t nelims, const term_t elim[],
					     yices_gen_mode_t mode, term_vector_t *v) {
  MT_PROTECT(term_t,  __yices_globals.lock, _o_yices_generalize_model_array(mdl, n, a, nelims, elim, mode, v));
}

term_t _o_yices_generalize_model_array(model_t *mdl, uint32_t n, const term_t a[], uint32_t nelims, const term_t elim[],
					     yices_gen_mode_t mode, term_vector_t *v) {
  int32_t code;

  if (! check_good_terms(__yices_globals.manager, n, a) ||
      ! check_boolean_args(__yices_globals.manager, n, a) ||
      ! check_elim_vars(__yices_globals.manager, nelims, elim)) {
    return NULL_TERM;
  }

  v->size = 0;
  switch (mode) {
  case YICES_GEN_BY_SUBST:
    code = gen_model_by_substitution(mdl, __yices_globals.manager, n, a, nelims, elim, (ivector_t *) v);
    break;

  case YICES_GEN_BY_PROJ:
    code = gen_model_by_projection(mdl, __yices_globals.manager, n, a, nelims, elim, (ivector_t *) v);
    break;

  default:
    code = generalize_model(mdl, __yices_globals.manager, n, a, nelims, elim, (ivector_t *) v);
    break;
  }

  if (code < 0) {
    set_error_code(yices_gen_error(code));
    return -1;
  }

  return 0;
}





/*************************
 *  GARBAGE COLLECTION   *
 ************************/

/*
 * Allocate and initialize the registry tables
 */
static sparse_array_t *get_root_terms(void) {
  if (root_terms == NULL) {
    init_sparse_array(&the_root_terms, 0);
    root_terms = &the_root_terms;
  }
  return root_terms;
}

static sparse_array_t *get_root_types(void) {
  if (root_types == NULL) {
    init_sparse_array(&the_root_types, 0);
    root_types = &the_root_types;
  }
  return root_types;
}


/*
 * Increment/decrement the reference counters
 */
EXPORTED int32_t yices_incref_term(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_incref_term(t));
}

int32_t _o_yices_incref_term(term_t t) {
  sparse_array_t *roots;

  if (!check_good_term(__yices_globals.manager, t)) {
    return -1;
  }

  // we keep the ref count on the term index
  // (i.e., we ignore t's polarity)
  roots = get_root_terms();
  sparse_array_incr(roots, index_of(t));

  return 0;
}

EXPORTED int32_t yices_incref_type(type_t tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_incref_type(tau));
}

int32_t _o_yices_incref_type(type_t tau) {
  sparse_array_t *roots;

  if (!check_good_type(__yices_globals.types, tau)) {
    return -1;
  }

  roots = get_root_types();
  sparse_array_incr(roots, tau);

  return 0;
}

EXPORTED int32_t yices_decref_term(term_t t) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_decref_term(t));
}

int32_t _o_yices_decref_term(term_t t) {
  if (!check_good_term(__yices_globals.manager, t)) {
    return -1;
  }

  if (root_terms == NULL || sparse_array_read(root_terms, index_of(t)) == 0) {
    error_report_t *error = get_yices_error();
    error->code = BAD_TERM_DECREF;
    error->term1 = t;
    return -1;
  }

  sparse_array_decr(root_terms, index_of(t));

  return 0;
}

EXPORTED int32_t yices_decref_type(type_t tau) {
  MT_PROTECT(int32_t,  __yices_globals.lock, _o_yices_decref_type(tau));
}

int32_t _o_yices_decref_type(type_t tau) {
  if (! check_good_type(__yices_globals.types, tau)) {
    return -1;
  }

  if (root_types == NULL || sparse_array_read(root_types, tau) == 0) {
    error_report_t *error = get_yices_error();
    error->code = BAD_TYPE_DECREF;
    error->type1 = tau;
    return -1;
  }

  sparse_array_decr(root_types, tau);

  return 0;
}


/*
 * Number of live terms and types
 */
EXPORTED uint32_t yices_num_terms(void) {
  MT_PROTECT(uint32_t,  __yices_globals.lock, _o_yices_num_terms());
}

uint32_t _o_yices_num_terms(void) {
  return __yices_globals.terms->live_terms;
}

EXPORTED uint32_t yices_num_types(void) {
  MT_PROTECT(uint32_t,  __yices_globals.lock, _o_yices_num_types());
}

uint32_t _o_yices_num_types(void) {
  return __yices_globals.types->live_types;
}


/*
 * Number of terms/types with a positive reference count
 */
EXPORTED uint32_t yices_num_posref_terms(void) {
  MT_PROTECT(uint32_t,  __yices_globals.lock, _o_yices_num_posref_terms());
}

uint32_t _o_yices_num_posref_terms(void) {
  uint32_t n;

  n = 0;
  if (root_terms != NULL) {
    n = root_terms->nelems;
  }
  return n;
}

EXPORTED uint32_t yices_num_posref_types(void) {
  MT_PROTECT(uint32_t,  __yices_globals.lock, _o_yices_num_posref_types());
}

uint32_t _o_yices_num_posref_types(void) {
  uint32_t n;

  n = 0;
  if (root_types != NULL) {
    n = root_types->nelems;
  }
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

  elem = context_list.next;
  while (elem != &context_list) {
    context_gc_mark(context_of_header(elem));
    elem = elem->next;
  }
}

// scan the list of models and call the mark procedure
static void model_list_gc_mark(void) {
  dl_list_t *elem;

  elem = model_list.next;
  while (elem != &model_list) {
    model_gc_mark(model_of_header(elem));
    elem = elem->next;
  }
}

// mark all terms in array a, n = size of a
static void mark_term_array(term_table_t *tbl, const term_t *a, uint32_t n) {
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
static void mark_type_array(type_table_t *tbl, const type_t *a, uint32_t n) {
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
 *   all be preserved
 */
EXPORTED void yices_garbage_collect(const term_t t[], uint32_t nt,
				    const type_t tau[], uint32_t ntau,
				    int32_t keep_named) {
  MT_PROTECT_VOID(__yices_globals.lock, _o_yices_garbage_collect(t, nt, tau, ntau, keep_named));
}

void _o_yices_garbage_collect(const term_t t[], uint32_t nt,
                              const type_t tau[], uint32_t ntau,
                              int32_t keep_named) {
  bool keep;


  get_list_locks();

  /*
   * Default roots: all terms and types in all live models and context
   */
  context_list_gc_mark();
  model_list_gc_mark();

  /*
   * Add roots from t and tau
   */
  if (t != NULL) mark_term_array(__yices_globals.terms, t, nt);
  if (tau != NULL) mark_type_array(__yices_globals.types, tau, ntau);

  /*
   * Roots from the reference counting
   */
  if (root_terms != NULL) {
    sparse_array_iterate(root_terms, __yices_globals.terms, term_idx_marker);
  }
  if (root_types != NULL) {
    sparse_array_iterate(root_types, __yices_globals.types, type_marker);
  }

  /*
   * Call the garbage collector
   */
  keep = (keep_named != 0);
  term_table_gc(__yices_globals.terms, keep);

  /*
   * Cleanup the fvars structure if it exists
   */
  if (__yices_globals.fvars != NULL) {
    cleanup_fvar_collector(__yices_globals.fvars);
  }

  release_list_locks();

}
