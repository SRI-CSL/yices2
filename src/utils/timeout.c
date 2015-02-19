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
 * Two implementations:
 * one for UNIX (Linux/Darwin/Cygwin)
 * one for Windows (MinGW).
 *
 * NOTES:
 * signal has different behavior on different Unix versions.
 * Here's what the manpage says (on Linux).
 *
 * The original Unix signal() would  reset the handler to SIG_DFL, and
 * System V (and the Linux kernel  and libc4,5) does the same.  On the
 * other  hand,  BSD  does  not  reset the  handler,  but  blocks  new
 * instances  of this  signal  from  occurring during  a  call of  the
 * handler.  The glibc2 library follows the BSD behavior.
 *
 * Testing results:
 * - on solaris 5.10, the signal handler is reset to SIG_DFL before
 *   the handler is called. So we must restore the handler every time.
 * - on Linux/Darwin/Cygwin: the signal handler is not changed.
 *
 */

#include <assert.h>

#include "utils/timeout.h"
#include "yices_exit_codes.h"


/*
 * Global structure common to both implementation.
 */
static timeout_t the_timeout;


#ifndef MINGW


/*****************************
 *  UNIX/C99 IMPLEMENTATION  *
 ****************************/

#include <unistd.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>


/*
 * To save the original SIG_ALRM handler
 */
static void (*saved_handler)(int);


/*
 * SIG_ALRM handler:
 * - do nothing if the timeout is not active
 * - otherwise, change the state to fired
 *   then call the handler
 */
static void alarm_handler(int signum) {
  if (the_timeout.state == TIMEOUT_ACTIVE) {
    the_timeout.state = TIMEOUT_FIRED;
    the_timeout.handler(the_timeout.param);
  }
}


/*
 * Initialization:
 * - install the alarm_handler (except on Solaris)
 * - initialize state to READY
 */
void init_timeout(void) {
#ifndef SOLARIS
  saved_handler = signal(SIGALRM, alarm_handler);
  if (saved_handler == SIG_ERR) {
    perror("Yices: failed to install SIG_ALRM handler: ");
    exit(YICES_EXIT_INTERNAL_ERROR);
  }
#endif

  the_timeout.state = TIMEOUT_READY;;
  the_timeout.handler = NULL;
  the_timeout.param = NULL;
}



/*
 * Activate the timer
 * - delay = timeout in seconds (must be positive)
 * - handler = the handler to call
 * - param = data passed to the handler
 *
 * On Solaris: set the signal handler here.
 */
void start_timeout(uint32_t delay, timeout_handler_t handler, void *param) {
  assert(delay > 0 && the_timeout.state == TIMEOUT_READY && handler != NULL);
  the_timeout.state = TIMEOUT_ACTIVE;
  the_timeout.handler = handler;
  the_timeout.param = param;

#ifdef SOLARIS
  saved_handler = signal(SIGALRM, alarm_handler);
  if (saved_handler == SIG_ERR) {
    perror("Yices: failed to install SIG_ALRM handler: ");
    exit(YICES_EXIT_INTERNAL_ERROR);
  }
#endif

  (void) alarm(delay);
}



/*
 * Clear timeout:
 * - cancel the timeout if it's not fired
 * - set state to READY
 */
void clear_timeout(void) {
  // TODO: Check whether we should block the signals here?
  if (the_timeout.state == TIMEOUT_ACTIVE) {
    // not fired;
    the_timeout.state = TIMEOUT_CANCELED;
    (void) alarm(0); // cancel the alarm
  }
  the_timeout.state = TIMEOUT_READY;
}


/*
 * Final cleanup:
 * - cancel the timeout if it's active
 * - restore the original handler
 */
void delete_timeout(void) {
  if (the_timeout.state == TIMEOUT_ACTIVE) {
    (void) alarm(0);
  }
  (void) signal(SIGALRM, saved_handler);
  the_timeout.state = TIMEOUT_NOT_READY;
}


#else


/************************************
 *   WINDOWS/MINGW IMPLEMENTATION   *
 ***********************************/

// BD: don't know what this is for.
#ifndef _WIN32_WINNT
#define _WIN32_WINNT 0x0500
#endif

#include <windows.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>


/*
 * Global variable:
 * - handler for a timer queue
 * - handler for a timer
 */
static HANDLE timer_queue;
static HANDLE timer;


/*
 * Callback function for the timer
 * - do nothing if the timeout is not active
 * - otherwise change the state to fired and
 *   call the handler.
 */
static VOID CALLBACK timer_callback(PVOID param, BOOLEAN timer_or_wait_fired) {
  if (the_timeout.state == TIMEOUT_ACTIVE) {
    the_timeout.state = TIMEOUT_FIRED;
    the_timeout.handler(the_timeout.param);
  }
}


/*
 * Initialization:
 * - create the timer queue
 */
void init_timeout(void) {
  timer_queue = CreateTimerQueue();
  if (timer_queue == NULL) {
    fprintf(stderr, "Yices: CreateTimerQueue failed with error code %"PRIu32"\n", (uint32_t) GetLastError());
    fflush(stderr);
    exit(YICES_EXIT_INTERNAL_ERROR);
  }

  the_timeout.state = TIMEOUT_READY;
  the_timeout.handler = NULL;
  the_timeout.param = NULL;
}



/*
 * Activate:
 * - delay = timeout in seconds (must be positive)
 * - handler = handler to call if fired
 * - param = parameter for the handler
 */
void start_timeout(uint32_t delay, timeout_handler_t handler, void *param) {
  DWORD duetime;

  assert(delay > 0 && the_timeout.state == TIMEOUT_READY && handler != NULL);

  duetime = delay * 1000; // delay in milliseconds
  if (CreateTimerQueueTimer(&timer, timer_queue, (WAITORTIMERCALLBACK) timer_callback,
                            NULL, duetime, 0, 0)) {
    // timer created
    the_timeout.state = TIMEOUT_ACTIVE;
    the_timeout.handler = handler;
    the_timeout.param = param;
  } else {
    fprintf(stderr, "Yices: CreateTimerQueueTimer failed with error code %"PRIu32"\n", (uint32_t) GetLastError());
    fflush(stderr);
    exit(YICES_EXIT_INTERNAL_ERROR);
  }
}



/*
 * Delete the timer
 */
void clear_timeout(void) {
  // GetLastError returns DWORD, which is an unsigned 32bit integer
  uint32_t error_code;

  if (the_timeout.state == TIMEOUT_ACTIVE || the_timeout.state == TIMEOUT_FIRED) {
    if (the_timeout.state == TIMEOUT_ACTIVE) {
      // active and not fired yet
      the_timeout.state = TIMEOUT_CANCELED; // will prevent call to handle
    }

    /*
     * We give NULL as CompletionEvent so timer_callback will complete
     * if the timer has fired. That's fine as the timeout state is not
     * active anymore so the timer_callback does nothing.
     *
     * Second try: give INVALID_HANDLE_VALUE?
     * This causes SEG FAULT in ntdll.dll
     */
    if (! DeleteTimerQueueTimer(timer_queue, timer, INVALID_HANDLE_VALUE)) {
      error_code = (uint32_t) GetLastError();
      // The Microsoft doc says we should try again
      // unless error code is ERROR_IO_PENDING??
      fprintf(stderr, "Yices: DeleteTimerQueueTimer failed with error code %"PRIu32"\n", error_code);
      fflush(stderr);
      exit(YICES_EXIT_INTERNAL_ERROR);
    }
  }

  the_timeout.state = TIMEOUT_READY;
}



/*
 * Final cleanup:
 * - delete the timer_queue
 */
void delete_timeout(void) {
  if (! DeleteTimerQueueEx(timer_queue, INVALID_HANDLE_VALUE)) {
    fprintf(stderr, "Yices: DeleteTimerQueueEx failed with error code %"PRIu32"\n", (uint32_t) GetLastError());
    fflush(stderr);
    exit(YICES_EXIT_INTERNAL_ERROR);
  }
}




#endif /* MINGW */
