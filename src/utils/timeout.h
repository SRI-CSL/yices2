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
 * SUPPORT FOR A SINGLE TIMEOUT
 */

/*
 * This provides a uniform interface to start a timeout,
 * and cancel it. There are four functions:
 *
 * 1) init_timeout(void): initialize internal structures.
 *    This must be called first.
 *
 * 2) start_timeout(delay, handler, param): start a timeout.
 *    This should not be called if the timer is already active.
 *    - delay = timeout in seconds
 *    - handler = callback function to call when the timeout expires
 *    - param = a generic pointer that's passed as unique argument to
 *              handler
 *
 * 3) clear_timeout(void): cancel the timeout and do some cleanup.
 *    If the timeout has fired already, this just does the cleanup
 *
 * 4) delete_timeout(void): final cleanup. Delete the internal
 *    data structures allocated by init_timeout.
 *
 * The handler should not call any of these functions itself.
 *
 * On Unix relatives, the implementation uses signal
 * and the alarm function.
 *
 * On mingw (Windows), the implementation relies on TimerQueues.
 */

#ifndef __TIMEOUT_H
#define __TIMEOUT_H

#include <stdint.h>

/*
 * Handler: a function with a single (void*) parameter
 * - should do something cheap and fast.
 */
typedef void (*timeout_handler_t)(void *data);


/*
 * Internal structure used to manage the timeout
 */
typedef struct timeout_s timeout_t;



/*
 * API
 */

/*
 * Initialize internal structures
 */
extern timeout_t *init_timeout(void);


/*
 * Start the timeout:
 * - delay = timeout in seconds (must be positive)
 * - handler = the handler to call
 * - param = data passed to the handler
 */
extern void start_timeout(timeout_t *timeout, uint32_t delay, timeout_handler_t handler, void *param);


/*
 * Cancel the timeout if it's not fired.
 * Cleanup any structure allocated by start timeout.
 */
extern void clear_timeout(timeout_t *timeout);


/*
 * Final cleanup
 */
extern void delete_timeout(timeout_t *timeout);



#endif /* __TIMEOUT_H */
