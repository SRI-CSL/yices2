/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * THREAD MACROS
 */

#ifndef _THREAD_MACROS_H
#define _THREAD_MACROS_H




#ifdef THREAD_SAFE
/*
 *
 * API entry point synchronization macros
 *
 */
#define MT_PROTECT_VOID(LOCK,EXPRESSION)\
  do { yices_lock_t *lock = &(LOCK);\
       get_yices_lock(lock);\
       (EXPRESSION);\
       release_yices_lock(lock);\
  } while(0)

#define MT_PROTECT(TYPE,LOCK,EXPRESSION)\
  do { yices_lock_t *lock = &(LOCK);\
       TYPE retval;\
       get_yices_lock(lock);\
       retval = (EXPRESSION);\
       release_yices_lock(lock);\
       return retval;\
  } while(0)


#else

#define MT_PROTECT_VOID(LOCK,EXPRESSION)  EXPRESSION

#define MT_PROTECT(TYPE,LOCK,EXPRESSION)  return EXPRESSION

#endif


#endif /* _THREAD_MACROS_H */
