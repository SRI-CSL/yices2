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
 * THREAD MACROS
 */

#ifndef _THREAD_MACROS_H
#define _THREAD_MACROS_H


/*
 * Thread Local Errors
 *
 * iam says: if we don't HAVE_TLS then we need to work harder with errors.
 * have to discuss this with BD. For the time being we protect it with the 
 * yices_global lock, but move it out of __yices_globals, since it we do have TLS
 * then it doesn't belong there.
 *
 */
#ifdef HAVE_TLS
#define YICES_THREAD_LOCAL __thread
#else
#define YICES_THREAD_LOCAL
#endif

/*
 *
 * API entry point synchronization macros
 *
 */
#define MT_PROTECT_VOID(LOCK,EXPRESSION) \
  do { yices_lock_t *lock = &(LOCK);\
       get_yices_lock(lock);\
       (EXPRESSION);\
       release_yices_lock(lock);\
  } while(0)

#define MT_PROTECT(TYPE,LOCK,EXPRESSION)	\
  do { yices_lock_t *lock = &(LOCK);\
       TYPE retval;\
       get_yices_lock(lock);\
       retval = (EXPRESSION);\
       release_yices_lock(lock);\
       return retval;\
  } while(0)


#define MT_PROTECT2(TYPE,LOCK0,LOCK1,EXPRESSION) \
  do { yices_lock_t *lock0 = &(LOCK0);\
       yices_lock_t *lock1 = &(LOCK1);\
       TYPE retval;\
       get_yices_lock(lock0);\
       get_yices_lock(lock1);\
       retval = (EXPRESSION);\
       release_yices_lock(lock1);\
       release_yices_lock(lock0);\
       return retval;\
  } while(0)



#endif /* _THREAD_MACROS_H */
