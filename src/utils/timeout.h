/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
 * Timeout state:
 * - NOT_READY: initial state and after call to delete_timeout
 * - READY: ready to be started (state after init_timeout
 *          and after clear_timeout)
 * - ACTIVE: after a call to start_timeout, before the timer fires
 *           or the timeout is canceled
 * - CANCELED: used by clear_timeout
 * - FIRED: after the handler has been called
 */
typedef enum timeout_state {
  TIMEOUT_NOT_READY, // 0
  TIMEOUT_READY,
  TIMEOUT_ACTIVE,
  TIMEOUT_CANCELED,
  TIMEOUT_FIRED,
} timeout_state_t;


/*
 * Handler: a function with a single (void*) parameter
 * - should do something cheap and fast.
 */
typedef void (*timeout_handler_t)(void *data);


/*
 * Internal structure used to manage the timeout
 */
typedef struct timeout_s {
  timeout_state_t state;
  timeout_handler_t handler;
  void *param;
} timeout_t;



/*
 * API
 */

/*
 * Initialize internal structures
 */
extern void init_timeout(void);


/*
 * Start the timeout:
 * - delay = timeout in seconds (must be positive)
 * - handler = the handler to call
 * - param = data passed to the handler
 */
extern void start_timeout(uint32_t delay, timeout_handler_t handler, void *param);


/*
 * Cancel the timeout if it's not fired.
 * Cleanup any structure allocated by start timeout.
 */
extern void clear_timeout(void);


/*
 * Final cleanup
 */
extern void delete_timeout(void);



#endif /* __TIMEOUT_H */
