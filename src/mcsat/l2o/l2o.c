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

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "mcsat/l2o/l2o.h"
#include "mcsat/tracing.h"

#include "terms/term_explorer.h"
#include "terms/bvarith64_buffer_terms.h"
#include "terms/bvarith_buffer_terms.h"
#include "terms/free_var_collector.h"

#include "model/models.h"

#include "context/context_types.h"

#include "yices.h"
#include "api/yices_api_lock_free.h"
#include "api/yices_extensions.h"
#include <math.h>

//#define EPSILON yices_rational32(1, 1000000)
#define EPSILON "0.0000001"


void l2o_construct(l2o_t* l2o, l2o_mode_t mode, term_table_t* terms, jmp_buf* handler) {
  l2o->mode = mode;
  l2o->terms = terms;
  l2o->n_runs = 0;
  l2o->n_terms = 0;
  init_term_manager(&l2o->tm, terms);
  init_ivector(&l2o->assertions, 0);
  init_int_hmap(&l2o->l2o_map, 0);
  init_int_hmap(&l2o->l2o_var_map, 0);

  init_varset_table(&l2o->varset_table, 0 );
  init_int_hmap(&l2o->freevars_map, 0);
  init_pmap2(&l2o->varset_members_cache);

  init_double_hmap(&l2o->eval_cache, 0);
  l2o->tracer = NULL;
  l2o->exception = handler;
  scope_holder_construct(&l2o->scope);
}

void l2o_set_tracer(l2o_t* l2o, tracer_t* tracer) {
  l2o->tracer = tracer;
}

void l2o_destruct(l2o_t* l2o) {
  delete_int_hmap(&l2o->l2o_map);
  delete_int_hmap(&l2o->l2o_var_map);
  delete_ivector(&l2o->assertions);
  delete_term_manager(&l2o->tm);

  delete_varset_table(&l2o->varset_table);
  delete_int_hmap(&l2o->freevars_map);
  delete_pmap2(&l2o->varset_members_cache);

  delete_double_hmap(&l2o->eval_cache);
  scope_holder_destruct(&l2o->scope);
}

void l2o_store_assertion(l2o_t* l2o, term_t assertion) {
  ivector_push(&l2o->assertions, assertion);
}

term_t l2o_get(l2o_t* l2o, term_t t) {
  int_hmap_pair_t* find = int_hmap_find(&l2o->l2o_map, t);
  if (find == NULL) {
    return NULL_TERM;
  } else {
    return find->val;
  }
}

/** Set t_l2o as the L2O value of t */
static inline
void l2o_set(l2o_t* l2o, term_t t, term_t t_l2o) {
  assert(l2o_get(l2o, t) == NULL_TERM);
  int_hmap_add(&l2o->l2o_map, t, t_l2o);
  l2o->n_terms++;
}

int32_t get_freevars_index(const l2o_t* l2o, term_t t) {
  term_t t_unsigned = unsigned_term(t);
  int_hmap_pair_t* find = int_hmap_find(&l2o->freevars_map, t_unsigned);
  if (find == NULL) {
    return -1;
  } else {
    return find->val;
  }
}

const int_hset_t* get_freevars(const l2o_t* l2o, term_t t){
  term_t t_unsigned = unsigned_term(t);
  int32_t index = get_freevars_index(l2o,  t_unsigned);
  if(index == -1){
    return NULL;
  }
  return get_varset(&l2o->varset_table, index);
}

const int_hset_t* get_freevars_from_index(const l2o_t* l2o, int32_t index){
  assert(index != -1);
  return get_varset(&l2o->varset_table, index);
}

// Set the set of free variables for t
static inline
void set_freevars_new(l2o_t* l2o, term_t t, int_hset_t* vars_set) {
  term_t t_unsigned = unsigned_term(t);
  assert(get_freevars_index(l2o, t_unsigned) == -1);
  int32_t index = add_varset(&l2o->varset_table, vars_set);
  int_hmap_add(&l2o->freevars_map, t_unsigned, index);
}

// Set the set of free variables of t to be equal to the set of free variables of t2
static
void set_freevars_dependent(l2o_t* l2o, term_t t, term_t t2) {
  term_t t_unsigned = unsigned_term(t);
  term_t t2_unsigned = unsigned_term(t2);
  assert(get_freevars_index(l2o, t_unsigned) == -1);
  int32_t index = get_freevars_index(l2o, t2_unsigned);
  assert(get_freevars_index(l2o, t2_unsigned) != -1);
  int_hmap_add(&l2o->freevars_map, t_unsigned, index);
}

/** Get as input an array of varset_table indices of length n. Fills the variables in out. */
static
void construct_union_set_from_indices(const l2o_t* l2o, const int32_t* indices, uint32_t n, int_hset_t *out) {
  for (uint32_t i = 0; i < n; ++ i) {
    int32_t index = indices[i];
    assert(index != -1);
    const int_hset_t* var_set_i = get_freevars_from_index(l2o, index);
    uint32_t nelems = var_set_i->nelems;
    for (uint32_t j = 0; j < nelems; ++ j) {
      term_t var = var_set_i->data[j];
      int_hset_add(out, var);
    }
  }
}

/** Get L2O variable translation of t */
static
term_t l2o_var_get(l2o_t* l2o, term_t t) {
  int_hmap_pair_t* find = int_hmap_find(&l2o->l2o_var_map, t);
  if (find == NULL) {
    return NULL_TERM;
  } else {
    return find->val;
  }
}

static inline
void l2o_var_set(l2o_t* l2o, term_t t, term_t t_l2o) {
  assert(l2o_var_get(l2o, t) == NULL_TERM);
  int_hmap_add(&l2o->l2o_var_map, t, t_l2o);
}


typedef struct composite_term1_s {
  uint32_t arity;  // number of subterms
  term_t arg[1];  // real size = arity
} composite_term1_t;

static
composite_term1_t composite_for_noncomposite;

// TODO use the function of preprocessor (extract it to term.h?)
composite_term_t* get_composite(term_table_t* terms, term_kind_t kind, term_t t) {
  if(!term_is_composite(terms, t)){
    assert(false);
  }
  assert(term_kind(terms, t) == kind);
  assert(is_pos_term(t)); 

  switch (kind) {
  case ITE_TERM:           // if-then-else
  case ITE_SPECIAL:        // special if-then-else term (NEW: EXPERIMENTAL)
    return ite_term_desc(terms, t);
  case EQ_TERM:            // equality
    return eq_term_desc(terms, t);
  case OR_TERM:            // n-ary OR
    return or_term_desc(terms, t);
  case XOR_TERM:           // n-ary XOR
    return xor_term_desc(terms, t);
  case ARITH_BINEQ_ATOM:   // equality: (t1 == t2)  (between two arithmetic terms)
    return arith_bineq_atom_desc(terms, t);
  case ARITH_EQ_ATOM: {
    composite_for_noncomposite.arity = 1;
    composite_for_noncomposite.arg[0] = arith_eq_arg(terms, t);
    return (composite_term_t*)&composite_for_noncomposite;
  }
  case ARITH_GE_ATOM: {
    composite_for_noncomposite.arity = 1;
    composite_for_noncomposite.arg[0] = arith_ge_arg(terms, t);
    return (composite_term_t*)&composite_for_noncomposite;
  }
  case APP_TERM:           // application of an uninterpreted function
    return app_term_desc(terms, t);
  case ARITH_RDIV:          // division: (/ x y)
    return arith_rdiv_term_desc(terms, t);
  case ARITH_IDIV:          // division: (div x y) as defined in SMT-LIB 2
    return arith_idiv_term_desc(terms, t);
  case ARITH_MOD:          // remainder: (mod x y) is y - x * (div x y)
    return arith_mod_term_desc(terms, t);
  case UPDATE_TERM:
    return update_term_desc(terms, t);
  case DISTINCT_TERM:
    return distinct_term_desc(terms, t);
  case BV_ARRAY:
    return bvarray_term_desc(terms, t);
  case BV_DIV:
    return bvdiv_term_desc(terms, t);
  case BV_REM:
    return bvrem_term_desc(terms, t);
  case BV_SDIV:
    return bvsdiv_term_desc(terms, t);
  case BV_SREM:
    return bvsrem_term_desc(terms, t);
  case BV_SMOD:
    return bvsmod_term_desc(terms, t);
  case BV_SHL:
    return bvshl_term_desc(terms, t);
  case BV_LSHR:
    return bvlshr_term_desc(terms, t);
  case BV_ASHR:
    return bvashr_term_desc(terms, t);
  case BV_EQ_ATOM:
    return bveq_atom_desc(terms, t);
  case BV_GE_ATOM:
    return bvge_atom_desc(terms, t);
  case BV_SGE_ATOM:
    return bvsge_atom_desc(terms, t);
  default:
    assert(false);
    return NULL;
  }
}

static
term_t mk_product(l2o_t* l2o, uint32_t n, term_t* args){
  pp_buffer_t* b = NULL;
  b = (pp_buffer_t *) safe_malloc(sizeof(pp_buffer_t));
  init_pp_buffer(b, n);
  pp_buffer_set_vars(b, n, args);
  term_t prod = pprod_term_from_buffer(l2o->terms, b);
  return prod;
}


static
term_t mk_sum(l2o_t* l2o, uint32_t n, term_t* args){
  rba_buffer_t b;
  init_rba_buffer(&b, l2o->terms->pprods);
  for (uint32_t i = 0; i < n; ++ i) {
    rba_buffer_add_var(&b, args[i]);
  }
  term_t paulinomial = mk_arith_term(&l2o->tm, &b);
  return paulinomial;
}

static
term_t l2o_apply(l2o_t* l2o, term_t t) {
  bool use_classic = l2o->mode == L2O_CLASSIC;
  if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
    printf("l2o_apply start\n");
  }
  term_table_t* terms = l2o->terms;

  // Check if we already have L2O(t)
  term_t t_l2o = l2o_get(l2o, t);
  if (t_l2o != NULL_TERM) {
    return t_l2o;
  }

  // Initialize the stack
  ivector_t l2o_stack;
  init_ivector(&l2o_stack, 0);
  ivector_push(&l2o_stack, t);

  // L2O main loop
  while (l2o_stack.size > 0) {
    // Current term
    term_t current = ivector_last(&l2o_stack);
    type_kind_t current_type = term_type_kind(terms, current);
    term_kind_t current_kind = term_kind(terms, current);

    if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
      mcsat_trace_printf(l2o->tracer, "\n\n* current = ");
      trace_term_ln(l2o->tracer, terms, current);
      mcsat_trace_printf(l2o->tracer, "\tid = %d", current);    
      mcsat_trace_printf(l2o->tracer, "\tcurrent type: \t %d",current_type);
      mcsat_trace_printf(l2o->tracer, "\tcurrent kind: \t %d",current_kind);
    }

    // If we already have L2O(current), continue
    term_t current_l2o = l2o_get(l2o, current);
    if (current_l2o != NULL_TERM) {
      ivector_pop(&l2o_stack);
      continue;
    }

    if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
      switch (current_type) {
      case BOOL_TYPE:
        printf("\nType is BOOL\n");
        break;
      case INT_TYPE:
        printf("\nType is INT\n");
        break;
      case REAL_TYPE:
        printf("\nType is REAL\n");
        break;
      case UNINTERPRETED_TYPE:
        printf("\nType is UNINTERPRETED\n");
        break;
      case SCALAR_TYPE:             // TODO What is SCALAR_TYPE?
        printf("\nType is SCALAR");
        break;
      default:
        printf("\nType is other");
        break;
      }
    }

    switch(current_kind) {
    case CONSTANT_TERM:    // constant of uninterpreted/scalar/boolean types
      if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
        printf("\ncurrent kind is CONSTANT_TERM");
        printf("\ncurrent kind is UNSUPPORTED\n");
      }
      // UNSUPPORTED TERM/THEORY
      current_l2o = zero_term;
      break;
    case ARITH_CONSTANT:   // rational constant
      if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
        printf("\ncurrent kind is ARITH_CONSTANT");
      }
      current_l2o = current;
      break;
    case UNINTERPRETED_TERM:  // (i.e., global variables, can't be bound).
      if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
        printf("\ncurrent kind is UNINTERPRETED_TERM");
      }
      if (current_type == BOOL_TYPE) 
      {
        bool translate_bool2real = false;

        // If translate_bool2real is False then, given a boolean proposition b
        // L2O(b) is ITE(b, 0 ,1)
        if(use_classic || !translate_bool2real){
          current_l2o = yices_ite(current, yices_zero(), yices_int32(1));
        }

        // If translate_bool2real is True then, given a boolean variable b:
        // - a real variable b_r is created
        // - the atoms b and (not b) are translated in terms of b_r (two possible translations, see below)
        else{
          // Translation a: 
          //    b -> b_r >= 1
          //    not b -> b_r <= -1
          // Translation b: 
          //    b -> ITE(b_r >= 0, 0, 1)
          //    not b -> ITE(b_r < 0, 0, 1)
          bool translation_a = false;   // if translation_a = false, then it is Translation b

          term_t cond = NULL_TERM;
          term_t then_term = NULL_TERM;
          term_t else_term = NULL_TERM;
          term_t b2r_lit = NULL_TERM;
          term_t b2r_term = NULL_TERM;
          if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
            printf("\ncurrent type is BOOL_TYPE");
          }
          // Check if b2r variable already exists
          term_t bool_var_unsigned = unsigned_term(current);
          term_t b2r_var = l2o_var_get(l2o, bool_var_unsigned);       
          if (b2r_var == NULL_TERM) {
            // Create b2r variable
            if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
              printf("\nCreting b2r variable\n");
            }
            b2r_var = yices_new_uninterpreted_term(yices_real_type());
            l2o_var_set(l2o, bool_var_unsigned, b2r_var);
          }
          if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
            mcsat_trace_printf(l2o->tracer, "b2r_var = ");
            trace_term_ln(l2o->tracer, terms, b2r_var);
          }
          term_t one = yices_int32(1);

          if(is_pos_term(current)){      
            if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
              printf("\nhas positive polarity\n");  
            }
            if(translation_a){
              b2r_term = yices_sub(b2r_var, one);    
            }else{
              b2r_term = b2r_var;                  
            }
            
            if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
              mcsat_trace_printf(l2o->tracer, "b2r_term = ");
              trace_term_ln(l2o->tracer, terms, b2r_term);
            }
            b2r_lit = yices_arith_geq0_atom(b2r_term);
            if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
              mcsat_trace_printf(l2o->tracer, "b2r_lit = ");
              trace_term_ln(l2o->tracer, terms, b2r_lit);
            }
            cond = b2r_lit;
            then_term = yices_zero();
            if(translation_a){
              else_term = yices_abs(b2r_term); 
            }else{
              else_term = one;
            }
            current_l2o = yices_ite(cond, then_term, else_term);
            if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
              mcsat_trace_printf(l2o->tracer, "current_l2o = ");
              trace_term_ln(l2o->tracer, terms, current_l2o);
            }
          }else{
            if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
              printf("\nhas negative polarity\n");  
            }
            term_t minusone = yices_int32(-1);

            if(translation_a){
              b2r_term = yices_sub(b2r_var, minusone);
              b2r_lit = yices_arith_leq0_atom(b2r_term);
              else_term = yices_abs(b2r_term); // Translation a
            }else{
              b2r_lit = yices_arith_lt0_atom(b2r_var);
              else_term = one;                   // Translation b
            }
            cond = b2r_lit;
            then_term = yices_zero();    
            current_l2o = yices_ite(cond, then_term, else_term);
          }
        }
      }
      else if (current_type == INT_TYPE || current_type == REAL_TYPE){
        current_l2o = current;
      } 
      else{
        if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
          printf("\ncurrent_kind: %d\n",current_kind);
          printf("\ncurrent kind is UNSUPPORTED\n");
        }
        // UNSUPPORTED TERM/THEORY
        current_l2o = zero_term;  // zero_term default for terms for which we do not have a translation
        //longjmp(*l2o->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      }
      break;
    case OR_TERM:        
    {
      if(is_pos_term(current)){    
        if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
          printf("\ncurrent kind is OR_TERM (positive polarity)\n");
        }
        composite_term_t* desc = get_composite(terms, current_kind, current);
        uint32_t n = desc->arity;
        if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
          printf("\n n: %d\n",n);
        }
        term_t* args = desc->arg;
        term_t args_l2o[n];
        bool args_already_visited = true;
        for (uint32_t i = 0; i < n; ++ i) {
          term_t arg_i = args[i];
          term_t arg_i_l2o = l2o_get(l2o, arg_i);      
          if (arg_i_l2o == NULL_TERM) {
            ivector_push(&l2o_stack, arg_i);
            args_already_visited = false;
          } 
          else if( arg_i_l2o == zero_term){
            args_l2o[i] = yices_int32(1);   // neutral element for product
          } 
          else{
            args_l2o[i] = arg_i_l2o;
          }
        }
        if (args_already_visited){
          current_l2o = mk_product(l2o, n, args_l2o);
        }else{
          continue;
        }
      }else{
        if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
          printf("\ncurrent kind is AND_TERM (i.e. OR with negative polarity)\n");
        }
        term_t current_unsigned = unsigned_term(current);
        composite_term_t* desc = get_composite(terms, current_kind, current_unsigned);
        uint32_t n = desc->arity;
        if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
          printf("\n n: %d\n",n);
        }
        term_t* args = desc->arg;
        term_t args_l2o[n];
        bool args_already_visited = true;
        for (uint32_t i = 0; i < n; ++ i) {
          term_t arg_i = args[i];
          term_t arg_i_neg = yices_not(arg_i);
          term_t arg_i_neg_l2o = l2o_get(l2o, arg_i_neg);      
          if (arg_i_neg_l2o == NULL_TERM) {
            ivector_push(&l2o_stack, arg_i_neg);
            args_already_visited = false;
          } 
          else if( arg_i_neg_l2o == zero_term){
            args_l2o[i] = yices_zero();   // neutral element for sum
          } 
          else{
            args_l2o[i] = arg_i_neg_l2o;
          }
        }
        if (args_already_visited){
          current_l2o = mk_sum(l2o, n, args_l2o);
          //current_l2o = yices_sum(n, args_l2o); // Slower (e.g. QF_NIA/20210219-Dartagnan/ReachSafety-Loops/matrix-1-O0.smt2)
        }else{
          continue;
        }
      }
    }
    break;

    case ITE_TERM:        
    case ITE_SPECIAL:        
    {      
      if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
        printf("\ncurrent kind is ITE_TERM or ITE_SPECIAL\n");
      }
      if(is_pos_term(current)){
        composite_term_t* desc = get_composite(terms, current_kind, current);
        assert( desc->arity == 3);
        term_t* args = desc->arg;
        term_t cond = args[0];
        term_t args_l2o[3];
        bool args_already_visited = true;
        for (uint32_t i = 1; i < 3; ++ i) {
          term_t arg_i = args[i];
          term_t arg_i_l2o = l2o_get(l2o, arg_i);      
          if (arg_i_l2o == NULL_TERM) {
            ivector_push(&l2o_stack, arg_i);
            args_already_visited = false;
          } else{
            args_l2o[i] = arg_i_l2o;
          }
        };
        if (args_already_visited){
          current_l2o = yices_ite(cond, args_l2o[1], args_l2o[2]);
        }else{
          continue;
        }
      } else {
        term_t current_unsigned = unsigned_term(current);
        composite_term_t* desc = get_composite(terms, current_kind, current_unsigned);
        assert( desc->arity == 3);
        term_t* args = desc->arg;
        term_t cond = args[0];
        term_t t1 = args[1];
        term_t t2 = args[2];
        term_t t1neg = yices_not(t1);
        term_t t2neg = yices_not(t2);
        term_t args_l2o[3];
        bool args_already_visited = true;
        term_t t1neg_l2o = l2o_get(l2o, t1neg);      
        if (t1neg_l2o == NULL_TERM) {
          ivector_push(&l2o_stack, t1neg);
          args_already_visited = false;
        } else{
          args_l2o[1] = t1neg_l2o;
        }
        term_t t2neg_l2o = l2o_get(l2o, t2neg);      
        if (t2neg_l2o == NULL_TERM) {
          ivector_push(&l2o_stack, t2neg);
          args_already_visited = false;
        } else{
          args_l2o[2] = t2neg_l2o;
        }
        if (args_already_visited){
          current_l2o = yices_ite(cond, args_l2o[1], args_l2o[2]);
        }else{
          continue;
        }
      }
    }
    break;

    case ARITH_EQ_ATOM:      // equality (t == 0)
    {
      if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
        printf("\ncurrent kind is ARITH_EQ_ATOM\n");
      }
      if (use_classic) {
        current_l2o = yices_ite(current, yices_zero(), yices_int32(1));
      } else {
        if (is_pos_term(current)) {     // t == 0
          if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
            printf("\n is positive (t == 0)\n");
          }
          composite_term_t *desc = get_composite(terms, current_kind, current);
          assert(desc->arity == 1);
          term_t *args = desc->arg;
          term_t t = args[0];
          current_l2o = yices_abs(t);
        } else {                          // t != 0
          if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
            printf("\n is negative (t != 0)\n");
          }
          term_t current_unsigned = unsigned_term(current);
          composite_term_t *desc = get_composite(terms, current_kind, current_unsigned);
          if (desc->arity != 1) assert(false);
          term_t cond = current;
          term_t then_term = yices_zero();
          term_t else_term = yices_int32(1);
          current_l2o = _o_yices_ite(cond, then_term, else_term);
        }
      }
    }
    break;

    case ARITH_BINEQ_ATOM:      // equality: (t1 == t2)  (between two arithmetic terms)
    {
      if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
        printf("\ncurrent kind is ARITH_BINEQ_ATOM\n");
      }
      if (use_classic) {
        current_l2o = yices_ite(current, yices_zero(), yices_int32(1));
      } else {
        if (is_pos_term(current)) {   // t1 == t2
          if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
            printf("\n is positive (t1==t2)\n");
          }
          composite_term_t *desc = get_composite(terms, current_kind, current);
          assert(desc->arity == 2);
          term_t *args = desc->arg;
          term_t t1 = args[0];
          term_t t2 = args[1];
          term_t t = _o_yices_sub(t1, t2);
          current_l2o = yices_abs(t);
        } else {                        // t1 != t2
          if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
            printf("\n is negative (t!=t2)\n");
          }
          term_t current_unsigned = unsigned_term(current);
          composite_term_t *desc = get_composite(terms, current_kind, current_unsigned);
          assert(desc->arity == 2);
          term_t *args = desc->arg;
          term_t t1 = args[0];
          term_t t2 = args[1];
          term_t t = _o_yices_sub(t1, t2);
          term_t cond = _o_yices_arith_neq0_atom(t);  // t1 - t2 != 0
          term_t then_term = yices_zero();
          term_t else_term = yices_int32(1);
          current_l2o = _o_yices_ite(cond, then_term, else_term);
        }
      }
    }
    break;

    case ARITH_GE_ATOM:      // atom t >= 0
    {     
      if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
        printf("\ncurrent kind is ARITH_GE_ATOM\n");
      }
      if (use_classic) {
        current_l2o = yices_ite(current, yices_zero(), yices_int32(1));
      } else {
        if (is_pos_term(current)) {   // t >= 0
          if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
            printf("\n is positive (t>=0)\n");
          }
          composite_term_t *desc = get_composite(terms, current_kind, current);
          assert(desc->arity == 1);
          term_t *args = desc->arg;
          term_t t = args[0];
          term_t cond = current;
          term_t then_term = yices_zero();
          term_t else_term = yices_abs(t);
          current_l2o = _o_yices_ite(cond, then_term, else_term);
        } else {                         // t < 0
          if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
            printf("\n is negative  (t<0)\n");
          }
          term_t current_unsigned = unsigned_term(current);
          composite_term_t *desc = get_composite(terms, current_kind, current_unsigned);
          assert(desc->arity == 1);
          term_t *args = desc->arg;
          term_t t = args[0];
          term_t cond = current;
          term_t then_term = yices_zero();
          term_t epsilon = yices_parse_float(EPSILON);
          term_t args_sum[] = {yices_abs(t), epsilon};
          term_t else_term = yices_sum(2, args_sum); // |t|+EPSILON
          current_l2o = yices_ite(cond, then_term, else_term);
        }
      }
    }
    break;

    case ARITH_FLOOR:
    case ARITH_CEIL:
    case ARITH_ABS:
    case POWER_PRODUCT:
    case ARITH_POLY:
    case ARITH_RDIV:
    case ARITH_IDIV:
    case ARITH_MOD:
    {
      current_l2o = current;
      break;
    }
    case EQ_TERM:     // equality
    { 
      if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
        printf("\ncurrent kind is EQ_TERM\n");
      }

      if (is_pos_term(current)) {     // t1 == t2
        if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
          printf("\n is positive (t1 == t2)\n");
        }
        composite_term_t* desc = get_composite(terms, current_kind, current);
        uint32_t n = desc->arity;
        assert(n == 2);
        term_t* args = desc->arg;
        term_t args_l2o[n];
        bool args_already_visited = true;
        for (uint32_t i  = 0; i < n; ++ i) {
          term_t arg_i = args[i];
          term_t arg_i_l2o = l2o_get(l2o, arg_i);      
          if (arg_i_l2o == NULL_TERM) {
            ivector_push(&l2o_stack, arg_i);
            args_already_visited = false;
          } 
          else{
            args_l2o[i] = arg_i_l2o;
          }
        }
        if (args_already_visited){
          term_t t = yices_sub(args_l2o[0], args_l2o[1]);
          current_l2o = yices_abs(t);
        }else{
          continue;
        }
      }
      else {                          // t != 0
        if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
          printf("\n is negative (t != 0)\n");
        }
        
        term_t current_unsigned = unsigned_term(current);
        term_t cond = current_unsigned;
        term_t then_term = yices_zero();
        term_t else_term = yices_int32(1);
        current_l2o = _o_yices_ite(cond, then_term, else_term);
      }
    }
    break;

    default:    // TODO consider for example also  EQ_TERM, DISTINCT_TERM, ...
      if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
        printf("\ncurrent_kind: %d\n",current_kind);
        printf("\ncurrent kind is UNSUPPORTED\n");
      }
      // UNSUPPORTED TERM/THEORY
      current_l2o = zero_term;    
      //longjmp(*l2o->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      break;
    }

    if (current_l2o != NULL_TERM) {
      l2o_set(l2o, current, current_l2o);
      ivector_pop(&l2o_stack);
      if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
        printf("\ncurrent_l2o != NULL_TERM\n");
        mcsat_trace_printf(l2o->tracer, "\ncurrent_l2o = ");
        trace_term_ln(l2o->tracer, terms, current_l2o);
      }
    }
  }

  delete_ivector(&l2o_stack);

  // Return the result
  t_l2o = l2o_get(l2o, t);
  if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
    mcsat_trace_printf(l2o->tracer, "t_l2o = ");
    trace_term_ln(l2o->tracer, terms, t_l2o);
  }
  assert(t_l2o != NULL_TERM);
  return t_l2o;
}


// Find all the free variables in t and in each subterm of t, and store them in l2o freevars_map
static
void collect_freevars(l2o_t* l2o, term_t t) {
  if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
    printf("\nget_free_arith_vars\n");
  }

  term_table_t* terms = l2o->terms;

  // Start
  ivector_t stack;
  init_ivector(&stack, 0);
  ivector_reset(&stack);
  ivector_push(&stack, t);

  int_hset_t current_vars_set;
  init_int_hset(&current_vars_set, 0);

  while (stack.size > 0) {
    int_hset_reset(&current_vars_set);

    // Current term (unsigned)
    term_t current = unsigned_term(ivector_last(&stack));

    // If already visited, continue
    if(get_freevars(l2o, current) != NULL) {
      ivector_pop(&stack);
      continue;
    }

    if(current == RESERVED_TERM || current == UNUSED_TERM){
      // Create empty set
      assert(int_hset_is_empty(&current_vars_set));
      set_freevars_new(l2o, current, &current_vars_set);
      continue;
    }

    type_kind_t current_type = term_type_kind(terms, current);
    term_kind_t current_kind = term_kind(terms, current);

    bool finished = false;
    bool dependent = false; // true if the current term has exactly one subterm

    if (trace_enabled(l2o->tracer, "mcsat::get_vars")) {
      mcsat_trace_printf(l2o->tracer, "\n\n *  current = ");
      trace_term_ln(l2o->tracer, terms, current);
      printf(" --current id: %d",current);
      printf("\n --current_type: %d",current_type);
      printf("\n --current_kind: %d",current_kind);
    }

    switch (current_kind)
    {
    case CONSTANT_TERM:
    case ARITH_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
    case VARIABLE:
      finished = true;
      break;
      
    case UNINTERPRETED_TERM:
    {
      term_t current_unsigned = unsigned_term(current);
      int_hset_add(&current_vars_set, current_unsigned);

      term_t current_unsigned_l2o = l2o_var_get(l2o, current_unsigned);
      if (current_unsigned_l2o == NULL_TERM) {
        l2o_var_set(l2o, current_unsigned, current_unsigned);
      }
      finished = true;
      break;
    }
    case ARITH_EQ_ATOM:
    case ARITH_GE_ATOM:
    case ARITH_IS_INT_ATOM:
    {
      term_t current_unsigned = unsigned_term(current);
      composite_term_t* desc = get_composite(terms, current_kind, current_unsigned);
      assert(desc->arity == 1);
      term_t subt = desc->arg[0];
      if(get_freevars_index(l2o, subt) == -1){
        ivector_push(&stack, subt);
      }
      else{
        set_freevars_dependent(l2o, current, subt);
        finished = true;
        dependent = true;
      }
      break;
    }
    case ARITH_ABS:
    {
      term_t subt = arith_abs_arg(terms, current);
      if(get_freevars_index(l2o, subt) == -1){
        ivector_push(&stack, subt);
      }
      else{
        set_freevars_dependent(l2o, current, subt);
        finished = true;
        dependent = true;
      }
      break;
    }
    case ARITH_FLOOR:
    {
      term_t subt = arith_floor_arg(terms, current);
      if(get_freevars_index(l2o, subt) == -1){
        ivector_push(&stack, subt);
      }
      else{
        set_freevars_dependent(l2o, current, subt);
        finished = true;
        dependent = true;
      }
      break;
    }
    case ARITH_CEIL:
    {
      term_t subt = arith_ceil_arg(terms, current);
      if(get_freevars_index(l2o, subt) == -1){
        ivector_push(&stack, subt);
      }
      else{
        set_freevars_dependent(l2o, current, subt);
        finished = true;
        dependent = true;
      }
      break;
    }
    case ARITH_ROOT_ATOM:
      // not supported, as it does not occur in a root level constraint
      assert(false);
      break;

    // TODO check the term kinds below
    // assuming that the boolean terms are CNF'd at when calling l2o TODO check this assumption
    case ITE_TERM:
    case ITE_SPECIAL:
    case APP_TERM:
    case UPDATE_TERM:
    case TUPLE_TERM:
    case EQ_TERM:
    case DISTINCT_TERM:
    case OR_TERM:
    case XOR_TERM:
    case ARITH_BINEQ_ATOM:
    case ARITH_RDIV:
    case ARITH_IDIV:
    case ARITH_MOD:
    case ARITH_DIVIDES_ATOM:
    case BV_ARRAY:           // array of boolean terms
    case BV_DIV:             // unsigned division
    case BV_REM:             // unsigned remainder
    case BV_SDIV:            // signed division
    case BV_SREM:            // remainder in signed division (rounding to 0)
    case BV_SMOD:            // remainder in signed division (rounding to -infinity)
    case BV_SHL:             // shift left (padding with 0)
    case BV_LSHR:            // logical shift right (padding with 0)
    case BV_ASHR:            // arithmetic shift right (padding with sign bit)
    case BV_EQ_ATOM:         // equality: (t1 == t2)
    case BV_GE_ATOM:         // unsigned comparison: (t1 >= t2)
    case BV_SGE_ATOM:        // signed comparison (t1 >= t2)
    {
      term_t current_unsigned = unsigned_term(current);
      composite_term_t* desc = get_composite(terms, current_kind, current_unsigned);
      bool args_already_visited = true;
      term_t *args = desc->arg;
      uint32_t n_args = desc->arity;
      int32_t args_varset_index[n_args];
      for (uint32_t i = 0; i < n_args; ++ i) {
        args_varset_index[i] = get_freevars_index(l2o, args[i]);
        if (args_varset_index[i] == -1){          
          ivector_push(&stack, args[i]);
          args_already_visited = false;
        }
      }
      if(args_already_visited){
        construct_union_set_from_indices(l2o, args_varset_index, n_args, &current_vars_set);
        finished = true;
      }
      break;
    }
    case SELECT_TERM:      // tuple projection
    {
      term_t subt = select_term_arg(terms, current);
      if(get_freevars_index(l2o, subt) == -1){
        ivector_push(&stack, subt);
      }
      else{
        set_freevars_dependent(l2o, current, subt);
        finished = true;
        dependent = true;
      }
      break;
    }
    case BIT_TERM:         // bit-select
    {
      term_t subt = bit_term_arg(terms, current);
      if(get_freevars_index(l2o, subt) == -1){
        ivector_push(&stack, subt);
      }
      else{
        set_freevars_dependent(l2o, current, subt);
        finished = true;
        dependent = true;
      }
      break;
    }
    case POWER_PRODUCT:
    {
      bool args_already_visited = true;
      pprod_t* ppdesc = pprod_term_desc(terms, current);
      uint32_t n_pp = ppdesc->len;
      varexp_t* pow = ppdesc->prod;
      int32_t args_varset_index[n_pp];
      
      uint32_t n_terms_with_vars = 0;
      for (uint32_t i = 0; i < n_pp; ++ i) {

        term_t var = pow[i].var;
        if(var!= RESERVED_TERM && good_term(l2o->terms, var)){
          args_varset_index[n_terms_with_vars] = get_freevars_index(l2o, var);
          if (args_varset_index[n_terms_with_vars] == -1){          
            ivector_push(&stack, var);
            args_already_visited = false;
          }
          n_terms_with_vars++;
        }
      }
      if(args_already_visited){
        construct_union_set_from_indices(l2o, args_varset_index, n_terms_with_vars, &current_vars_set);
        finished = true;
      }
      break;
    }
    case ARITH_POLY:
    {
      bool args_already_visited = true;
      polynomial_t* polydesc = poly_term_desc(terms, current);
      uint32_t n_poly = polydesc->nterms;

      int32_t args_varset_index[n_poly];
      for (uint32_t i = 0; i < n_poly; ++ i) {
        term_t var = polydesc->mono[i].var;
        args_varset_index[i] = get_freevars_index(l2o, var);
        if (args_varset_index[i] == -1){          
          ivector_push(&stack, var);
          args_already_visited = false;
        }
      }
      if(args_already_visited){
        construct_union_set_from_indices(l2o, args_varset_index, n_poly, &current_vars_set);
        finished = true;
      }
      break;
    }
    case BV_POLY:
    {
      bool args_already_visited = true;
      bvpoly_t* polydesc = bvpoly_term_desc(terms, current);
      uint32_t n_poly = polydesc->nterms;

      int32_t args_varset_index[n_poly];
      for (uint32_t i = 0; i < n_poly; ++ i) {
        term_t var = polydesc->mono[i].var;
        args_varset_index[i] = get_freevars_index(l2o, var);
        if (args_varset_index[i] == -1){          
          ivector_push(&stack, var);
          args_already_visited = false;
        }
      }
      if(args_already_visited){
        construct_union_set_from_indices(l2o, args_varset_index, n_poly, &current_vars_set);
        finished = true;
      }
      break;
    }
    case BV64_POLY:
    {
      bool args_already_visited = true;
      bvpoly64_t* polydesc = bvpoly64_term_desc(terms, current);
      uint32_t n_poly = polydesc->nterms;

      int32_t args_varset_index[n_poly];
      for (uint32_t i = 0; i < n_poly; ++ i) {
        term_t var = polydesc->mono[i].var;
        args_varset_index[i] = get_freevars_index(l2o, var);
        if (args_varset_index[i] == -1){          
          ivector_push(&stack, var);
          args_already_visited = false;
        }
      }
      if(args_already_visited){
        construct_union_set_from_indices(l2o, args_varset_index, n_poly, &current_vars_set);
        finished = true;
      }
      break;
    }
    default:
      assert(false);
      break;
    }

    if(finished) {
      if(!dependent){
        int_hset_close_and_sort(&current_vars_set);
        set_freevars_new(l2o, current, &current_vars_set);

        if (trace_enabled(l2o->tracer, "mcsat::get_vars")) {
          mcsat_trace_printf(l2o->tracer, "\n\n - current_vars_set = \n");
          if(current_vars_set.nelems == 0){
            printf("\t empty");
          }
          for (uint32_t i = 0; i < current_vars_set.nelems; ++ i) {
            trace_term_ln(l2o->tracer, terms, current_vars_set.data[i]);
          }
        }
      }
      else{
        if (trace_enabled(l2o->tracer, "mcsat::get_vars")) {
          printf("\n\n - current_vars_set = dependent on its subterm \n");
        }
      }
      ivector_pop(&stack);
    }
  }

  delete_int_hset(&current_vars_set);
}

void l2o_set_exception_handler(l2o_t* l2o, jmp_buf* handler) {
  l2o->exception = handler;
}

#if 0
static
void set_l2o_vars(l2o_t* l2o, int_hset_t* var_set){

  uint32_t n = var_set->nelems;

  for (uint32_t i = 0; i < n; ++ i) {
    term_t var = var_set->data[i];
    type_kind_t var_type = term_type_kind(l2o->terms, var);
    if(l2o_var_get(l2o, var) != NULL_TERM){
      continue;
    }
    switch (var_type) {
    case BOOL_TYPE:
    {
      l2o_var_set(l2o, var, var);
      break;
    }
    case REAL_TYPE:
    case INT_TYPE:
      l2o_var_set(l2o, var, var);
      break;
    default:
      assert(false);
    }
  }
}
#endif

/*
 * Provide hint to the trail cache 
 */
static
void hint_value_to_trail(mcsat_trail_t* trail, variable_t v, const mcsat_value_t* val) {
  //mcsat_plugin_context_t* mctx;
  //mctx = (mcsat_plugin_context_t*) self;
  variable_t var = variable_db_get_variable_if_exists(trail->var_db, v);
  assert (var != variable_null);

  // update only if var has no value in the trail
  if(! trail_has_value(trail, var) ){
    mcsat_model_set_value(&trail->model, var, val);
  }
}

static
double mcsat_value_to_double(const mcsat_value_t* val){
  mcsat_value_type_t type = val->type;
  switch (type) {
  case VALUE_BOOLEAN:
    return val->b;

  case VALUE_RATIONAL: {
    rational_t r = val->q;
    return q_get_double(&r);
  }

  case VALUE_LIBPOLY: {
    const lp_value_t lp_v = val->lp_value;
    return lp_value_to_double(&lp_v);
  }

  default:
    assert(false);
    return 0.0;
  }
}

static
void double_to_mcsat_value(mcsat_value_t* val, mcsat_value_type_t type, double d) {
  switch (type) {
    case VALUE_BOOLEAN:
      mcsat_value_construct_bool(val, d != 0.0);
      break;
    case VALUE_RATIONAL: {
      rational_t r;
      q_init(&r);
      q_set_double(&r, d);
      mcsat_value_construct_rational(val, &r);
      q_clear(&r);
      break;
    }
    case VALUE_LIBPOLY: {
      lp_rational_t lp_r;
      lp_rational_construct_from_double(&lp_r, d);
      mcsat_value_construct_lp_value_direct(val, LP_VALUE_RATIONAL, &lp_r);
      lp_rational_destruct(&lp_r);
      break;
    }
    default:
      // not implemented
      assert(false);
      break;
  }
}

void l2o_search_state_construct_empty(l2o_search_state_t *state) {
  state->var = NULL;
  state->val = NULL;
  state->n_var = 0;
  state->n_var_fixed = 0;
}

void l2o_search_state_destruct(l2o_search_state_t *state) {
  free(state->var);
  free(state->val);
}

#if 0
bool l2o_search_state_diff(const l2o_search_state_t *a, const l2o_search_state_t *b, ivector_t *vars) {
  if (a->n_var != b->n_var || a->n_var_fixed != b->n_var_fixed) {
    return false;
  }

  uint32_t i;
  for (i = 0; i < a->n_var; ++i) {
    if (a->var[i] != b->var[i]) {
      return false;
    }
  }
  for (i = 0; i < a->n_var; ++i) {
    if (a->val[i] != b->val[i]) {
      ivector_push(vars, a->var[i]);
    }
  }
  return true;
}

void l2o_search_state_copy(l2o_search_state_t *dst, const l2o_search_state_t *src) {
  dst->n_var = src->n_var;
  dst->n_var_fixed = src->n_var_fixed;
  size_t size_var = src->n_var * sizeof(term_t); // in byte
  size_t size_val = src->n_var * sizeof(double); // in byte
  dst->var = (term_t *) safe_realloc(dst->var, size_var);
  dst->val = (double *) safe_realloc(dst->val, size_val);
  memcpy(dst->var, src->var, size_var);
  memcpy(dst->val, src->val, size_val);
}
#endif

static
bool l2o_is_valid_term(l2o_t *l2o, term_t t) {
  if (t == -1) {
    return false;
  }

  const int_hset_t* var_set = get_freevars(l2o, t);
  assert(var_set != NULL);
  assert(var_set->is_closed);

  // Check if there are non-arith and non-bool vars; if yes, return without doing anything
  uint32_t n_var = var_set->nelems;
  for (uint32_t i = 0; i < n_var; ++ i) {
    term_t t_i = var_set->data[i];
    type_kind_t type_vi = term_type_kind(l2o->terms, t_i);
    if(type_vi != INT_TYPE && type_vi != REAL_TYPE && type_vi != BOOL_TYPE){
      return false;
    }
  }

  return true;
}

static
void l2o_search_state_create(l2o_t *l2o, term_t t, mcsat_trail_t *trail, bool use_cached_values, l2o_search_state_t *state) {
  const int_hset_t* var_set = get_freevars(l2o, t);
  assert(var_set != NULL);
  assert(var_set->is_closed);
  uint32_t n_var = var_set->nelems;

  l2o_search_state_construct_empty(state);

  if (n_var == 0) {
    return;
  }

  state->n_var = n_var;
  state->val = safe_malloc(sizeof(double) * n_var);
  state->var = safe_malloc(sizeof(term_t) * n_var);

  double *val = state->val;
  term_t *v = state->var;

  ivector_t vars, vars_fixed;
  init_ivector(&vars, 0);
  init_ivector(&vars_fixed, 0);

  for (uint32_t i = 0; i < n_var; ++ i) {
    term_t t_i = var_set->data[i];
    variable_t var_i = variable_db_get_variable_if_exists(trail->var_db, t_i);
    assert (var_i != variable_null);
    ivector_push(trail_has_value(trail, var_i) ? &vars_fixed : &vars, var_i);
  }
  state->n_var_fixed = vars_fixed.size;

  // TODO sort non-fixed here by VSIDS

  // join vectors
  assert(vars_fixed.size + vars.size == n_var);
  uint32_t pos = 0;
  for (uint32_t i = 0; i < vars_fixed.size; ++ i) {
    variable_t var = vars_fixed.data[i];
    v[pos] = variable_db_get_term(trail->var_db, var);
    val[pos] = mcsat_value_to_double(trail_get_value(trail, var));
    pos++;
  }
  for (uint32_t i = 0; i < vars.size; ++ i) {
    variable_t var = vars.data[i];
    v[pos] = variable_db_get_term(trail->var_db, var);
    if (use_cached_values && trail_has_cached_value(trail, var)) {
      val[pos] = mcsat_value_to_double(trail_get_cached_value(trail, var));
    } else {
      val[pos] = variable_db_get_term(trail->var_db, var) == BOOL_TYPE ? 1.0 : 0.0;
    }
    pos++;
  }
  assert(pos == n_var);

  if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
    printf("\nn_var = %d", n_var);
    printf("\nn_var_fixed = %d", vars_fixed.size);
  }

  delete_ivector(&vars);
  delete_ivector(&vars_fixed);
}

// Given variables v and values s_mpq, set hint to the trail
static
void l2o_set_hint(l2o_t *l2o, mcsat_trail_t *trail, const l2o_search_state_t *state) {
  term_table_t* terms = l2o->terms;

  double val_d;
  mcsat_value_t val_mcsat;

  assert(state->n_var_fixed <= state->n_var);
  for (uint32_t i = state->n_var_fixed; i < state->n_var; ++ i) {
    type_kind_t vi_type = term_type_kind(terms, state->var[i]);
    val_d = state->val[i];

    if (vi_type == INT_TYPE) {
      // round the value to the nearest integer
      val_d = round(val_d);
    }

    assert(vi_type != BOOL_TYPE || val_d == 1.0 || val_d == 0.0);

    double_to_mcsat_value(&val_mcsat, vi_type == BOOL_TYPE ? VALUE_BOOLEAN : VALUE_LIBPOLY, val_d);
    hint_value_to_trail(trail, state->var[i], &val_mcsat);

    assert(vi_type != INT_TYPE || (val_mcsat.type == VALUE_LIBPOLY && lp_value_is_integer(&val_mcsat.lp_value)));
  }
}

/** Minimize L2O cost function and set hint to trail */
static
void l2o_minimize_and_set_hint(l2o_t* l2o, term_t t, mcsat_trail_t* trail, bool use_cached_values) {
  if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
    printf("\n\n  init l2o_minimize_and_set_hint\n");
  }

  if(t == -1){   // TODO why does this happens? E.g. /QF_NIA/non-incremental/QF_NIA/leipzig/term-AvoWGH.smt2
    if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
      mcsat_trace_printf(l2o->tracer, "\nt is RESERVED_TERM\n");
    }
    return;
  }

  // ensure that the term has freevares are collected
  collect_freevars(l2o, t);
  if(!l2o_is_valid_term(l2o, t)) {
    return;
  }

  l2o_search_state_t state;

  // create search state
  l2o_search_state_create(l2o, t, trail, use_cached_values, &state);

  if (!l2o_search_state_is_empty(&state)) {
    // Improve val using hill_climbing
    hill_climbing(l2o, t, &state);

    // Set hints
    l2o_set_hint(l2o, trail, &state);
  }

  // destroy state
  l2o_search_state_destruct(&state);
}

term_t l2o_make_cost_fx(l2o_t* l2o) {
  ivector_t* assertions = &l2o->assertions;
  int32_t n_assertions = assertions->size;
  term_t f_l2o[n_assertions];
  for (uint32_t i = 0; i < n_assertions; ++ i) {
    term_t f_i = assertions->data[i];
    f_l2o[i] = l2o_apply(l2o, f_i);
  }
  // TODO change to list to enable incremental solving
  l2o->cost_fx = yices_sum(n_assertions, f_l2o);
  return l2o->cost_fx;
}

void l2o_run(l2o_t* l2o, mcsat_trail_t* trail, bool use_cached_values) {
  term_t cost_fx = l2o_make_cost_fx(l2o);

  if (trace_enabled(l2o->tracer, "mcsat::l2o")){
    mcsat_trace_printf(l2o->tracer, "\tfinal cost_fx id = %d", cost_fx);   
    mcsat_trace_printf(l2o->tracer, " value = ");
    term_table_t* terms = l2o->terms;
    trace_term_ln(l2o->tracer, terms, cost_fx);
  }

  // TODO: Check if cost is zero
  l2o_minimize_and_set_hint(l2o, cost_fx, trail, use_cached_values);
  l2o->n_runs++;
}
