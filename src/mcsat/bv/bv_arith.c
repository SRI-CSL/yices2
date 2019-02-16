/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "mcsat/tracing.h"
#include "mcsat/value.h"
#include "terms/term_manager.h"
#include "utils/ptr_heap.h"

#include "bv_evaluator.h"
#include "bv_arith.h"


bool bv_arith_has_conflict_var(plugin_context_t* ctx, term_t t, term_t conflict_var) {
  switch (term_kind(ctx->terms, t)) {
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(ctx->terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == conflict_var) return true; //TODO: check that t_poly->mono[i].var is really a term (thought it was index for pproduct)
    }
    return false;
  }
  default:
    assert(false);
  }
}

// Local context
typedef struct {
  plugin_context_t* ctx;
  bv_evaluator_t* eval;
  term_t conflict_var;
  ivector_t* conflict;
  uint32_t glb;
  uint32_t lub;
  ptr_heap_t heap;

} local_ctx_t;


void bv_arith_le(local_ctx_t* lctx, term_t lhs, term_t rhs) {
  // Standard abbreviations
  term_manager_t* tm = &lctx->ctx->var_db->tm;

  bool left_has  = bv_arith_has_conflict_var(lctx->ctx, lhs, lctx->conflict_var);
  bool right_has = bv_arith_has_conflict_var(lctx->ctx, rhs, lctx->conflict_var);

  term_t c1 = left_has?lhs:lhs; //TODO 1st case should be lhs - conflict_var. Use bvarith_buffer_sub_term(bvarith_buffer_t *b, term_table_t *table, term_t t);
  term_t c2 = right_has?rhs:rhs; //TODO 1st case should be rhs - conflict_var.

  uint32_t eval_level = 0; // What is this level ?!? Let's say it's 0 :-)
  const mcsat_value_t* c1_v = bv_evaluator_evaluate_term(lctx->eval, c1, &eval_level);
  /* (void) c1_v; */
  eval_level = 0;
  const mcsat_value_t* c2_v = bv_evaluator_evaluate_term(lctx->eval, c2, &eval_level);
  /* (void) c2_v; */

  assert(c1_v->type == VALUE_BV);
  assert(c2_v->type == VALUE_BV);
  bvconstant_t cc1 = c1_v->bv_value;
  bvconstant_t cc2 = c2_v->bv_value;
  
  term_t t; // Term to add to the conflict

  if (left_has) {
    t = (bvconstant_le(&cc1,&cc2)) ? mk_bvle(tm, c1, c2): mk_bvgt(tm, c1, c2);
  } else {
    assert(right_has); // otherwise !left_has && !right_has - conflict variable appears on neither side - not sure that could happen
    t = (bvconstant_le(&cc2,&cc1))?mk_bvle(tm, c2, c1):mk_bvgt(tm, c2, c1);
  }
  ivector_push(lctx->conflict, t);
}

// Type for bvconstant intervals
typedef struct {
  bvconstant_t lo;
  bvconstant_t hi;
} bvconst_interval_t;


bool cmp(void *x, void *y){
  bvconst_interval_t* i1 = (bvconst_interval_t*) x;
  bvconst_interval_t* i2 = (bvconst_interval_t*) y;
  return bvconstant_le(&i1->lo,&i2->lo);
}


void bv_arith_get_conflict(plugin_context_t* ctx, bv_evaluator_t* eval, const ivector_t* conflict_core, term_t conflict_var, ivector_t* conflict){

  // Standard abbreviations
  term_table_t* terms  = ctx->terms;
  const mcsat_trail_t* trail = ctx->trail;

  local_ctx_t lctx;
  lctx.ctx  = ctx;
  lctx.eval = eval;
  lctx.conflict = conflict;
  lctx.conflict_var = conflict_var;
  init_ptr_heap(&lctx.heap, 0, &cmp);
  
  // Variables that are going to be re-used for every item in the conflict core
  variable_t atom_i_var;
  bool       atom_i_value;
  term_t     atom_i_term;
  term_kind_t atom_i_kind;

  // We go through the conflict core
  
  for (uint32_t i = 0; i < conflict_core->size; i++) {
    
    atom_i_var   = conflict_core->data[i];
    atom_i_value = trail_get_boolean_value(trail, atom_i_var);
    atom_i_term  = variable_db_get_term(ctx->var_db, atom_i_var);

    assert(is_pos_term(atom_i_term));

    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "bv_arith treats core constraint ");
      ctx_trace_term(ctx, atom_i_term);
    }

    // The output conflict always contains the conflict core:
    ivector_push(conflict, atom_i_value?atom_i_term:opposite_term(atom_i_term));
    
    atom_i_kind  = term_kind(terms, atom_i_term);

    switch (atom_i_kind) {
    case BV_GE_ATOM: {  // Constraint is (t0 >= t1) -> True (with atom_i_term = (t0 >= t1)),
      composite_term_t* atom_i_comp = bvge_atom_desc(terms, atom_i_term);
      assert(atom_i_comp->arity == 2);
      term_t t0 = atom_i_comp->arg[0];
      term_t t1 = atom_i_comp->arg[1];
      assert(is_pos_term(t0));
      assert(is_pos_term(t1));
      if (atom_i_value) {
        bv_arith_le(&lctx, t1, t0);
      }
      else {
        // Constraint is (t0 >= t1) -> False (with atom_i_term = (t0 >= t1)),
        // It looks like we need to convert into 2 constraints (t1 >= t0+1) AND (t0+1 >= 1)
        // Create the term t0+1 using this?:
        // bvarith_buffer_add_term(bvarith_buffer_t *b, term_table_t *table, term_t t);
        assert(false);
      }
      break;
    }
    case EQ_TERM :     
    case BV_EQ_ATOM: { // equality
      composite_term_t* atom_i_comp = (atom_i_kind == EQ_TERM)?eq_term_desc(terms, atom_i_term): bveq_atom_desc(terms, atom_i_term);
      assert(atom_i_comp->arity == 2);
      term_t t0 = atom_i_comp->arg[0];
      term_t t1 = atom_i_comp->arg[1];
      assert(is_pos_term(t0));
      assert(is_pos_term(t1));
      if (atom_i_value) {
        // Constraint is (t0 == t1) -> True (with atom_i_term = (t0 == t1)),
        // Turn into 2 constraints (t0 >= t1) AND (t1 >= t0)
        // Careful there: one of the two may not be "in the core". Not problematic ?
        bv_arith_le(&lctx, t0, t1);
        bv_arith_le(&lctx, t1, t0);
      }
      else {
        // Constraint is (t0 == t1) -> False (with atom_i_term = (t0 == t1)),
        // The 2 constraints (t0 >= t1) -> False , (t1 >= t0) -> False are in a DISJUNCTION
        // Think about what to do then (check LRA or NRA plugins)
        assert(false);
      }
      break;
    }
    default:
      assert(false);
    }
  }
  delete_ptr_heap(&lctx.heap);
}


