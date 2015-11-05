/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef MCSAT_GC_H_
#define MCSAT_GC_H_

#include "utils/int_vectors.h"
#include "utils/int_hash_map.h"


/** Structure containing all he garbage collection data */
typedef struct {

  /** Is this an ID collector (keeping same object ids on collection) */
  bool is_id;

  /** Lock for the relocation data */
  bool is_relocated;

  /** The null value */
  int32_t null_value;

  /**
   * Mapping from marked objects to the objects they are being relocated to.
   * This means that during collection all marked objects map to the null
   * value. And during the relocation phase, all objects map to the non-null
   * value.
   */
  int_hmap_t old2new_map;

  /** List of all marked objects. */
  ivector_t marked;

  /** Count of relocated objects. */
  uint32_t relocated;

  /** Level of marking */
  uint32_t level;

  /** Count of relocated objects at this level */
  uint32_t marked_first;

} gc_info_t;

/** Construct the gc information */
void gc_info_construct(gc_info_t* gc, int32_t null_value, bool is_id);

/** Destruct the gc information */
void gc_info_destruct(gc_info_t* gc);

/** Add the object to the marked set (to keep) */
void gc_info_mark(gc_info_t* gc, int32_t obj);

/** Increase the marking level */
void gc_info_new_level(gc_info_t* gc);

/** Return the number of objects marked at current level */
uint32_t gc_info_get_level_size(const gc_info_t* gc);

/** Get marked objects */
ivector_t* gc_info_get_level_marked(void);

/** Check if the object is marked */
bool gc_info_is_marked(const gc_info_t* gc, int32_t obj);

/** Mark the object as to be replaced with the given new object */
void gc_info_set_reloc(gc_info_t* gc, int32_t obj, int32_t obj_new);

/** Set the lock on relocation */
void gc_info_set_relocated(gc_info_t* gc);

/** Check whether all the objects have been relocated */
bool gc_info_is_relocated(const gc_info_t* gc);

/** Get the relocated object (returns null value if collected) */
int32_t gc_info_get_reloc(const gc_info_t* gc, int32_t obj);

/** Collect the objects in the given vector */
void gc_info_sweep_ivector(const gc_info_t* gc, ivector_t* objs);

/** Collect the keys in the given map */
void gc_info_sweep_int_hmap_keys(const gc_info_t* gc, int_hmap_t* objs);

#endif /* MCSAT_GC_H_ */
