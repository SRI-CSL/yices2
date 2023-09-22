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

#include "utils/error.h"
#include "utils/memalloc.h"
#include "utils/timeout.h"
#include "yices_exit_codes.h"

#if !defined(MINGW) && defined(THREAD_SAFE)
#include <pthread.h>
#endif

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


typedef struct timeout_s {
  timeout_state_t state;
  timeout_handler_t handler;
  void *param;
#ifdef THREAD_SAFE
  struct timeval tv;
  pthread_t thread;
  int pipe[2];
#endif
} timeout_t;

#ifndef THREAD_SAFE

/*
 * Global structure common to both implementation.
 */
static timeout_t the_timeout;

#endif

#ifndef MINGW


/*****************************
 *  UNIX/C99 IMPLEMENTATION  *
 ****************************/

#include <unistd.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/errno.h>

#ifdef THREAD_SAFE

timeout_t *init_timeout(void) {
  timeout_t *timeout;

  timeout = (timeout_t *) safe_malloc(sizeof(timeout_t));

  timeout->state = TIMEOUT_READY;
  timeout->handler = NULL;
  timeout->param = NULL;
  timeout->tv.tv_sec = 0;
  timeout->tv.tv_usec = 0;
  timeout->pipe[0] = timeout->pipe[1] = -1;

  return timeout;
}

void delete_timeout(timeout_t *timeout) {
  /* The read end of the pipe should have been closed by the timer
     thread. */
  assert(timeout->pipe[0] == -1);
  /* The write end of the pipe should have been closed by
     clear_timer. */
  assert(timeout->pipe[1] == -1);
  
  safe_free(timeout);
}

static void *timer_thread(void *arg) {
  timeout_t *timeout;
  int fd;
  fd_set readfds;
  
  timeout = (timeout_t *) arg;

  fd = timeout->pipe[0];
  FD_ZERO(&readfds);
  FD_SET(fd, &readfds);

  /* Watch the read end of the pipe until the timeout occurs. */
  switch (select(fd + 1, &readfds,
		 /*writefds=*/NULL, /*errorfds=*/NULL,
		 &timeout->tv)) {
  case -1:
    /* Error. */
    perror_fatal("timer_thread: select");
    break;

  case 0:
    /* Timeout. */
    timeout->state = TIMEOUT_FIRED;
    timeout->handler(timeout->param);
    break;

  case 1:
    /* Canceled. */
    assert(FD_ISSET(fd, &readfds));
    timeout->state = TIMEOUT_CANCELED;
    break;

  default:
    assert(0);
  }

  /* Close the read end of the pipe. */
  if (close(timeout->pipe[0]) == -1)
    perror_fatal("timer_thread: close");
  timeout->pipe[0] = -1;
  
  return NULL;
}

void start_timeout(timeout_t *timeout, uint32_t delay, timeout_handler_t handler, void *param) {
  int ret;
  
  assert(delay > 0 && timeout->state == TIMEOUT_READY && handler != NULL);

  timeout->state = TIMEOUT_ACTIVE;
  timeout->tv.tv_sec = delay;
  timeout->tv.tv_usec = 0;
  timeout->handler = handler;
  timeout->param = param;

  if (pipe(timeout->pipe) == -1)
    perror_fatal("start_timeout: pipe");

  ret = pthread_create(&timeout->thread, /*attr=*/NULL, timer_thread, timeout);
  if (ret)
    perror_fatal_code("start_timeout: pthread_create", ret);
}

void clear_timeout(timeout_t *timeout) {
  void *value;
  
  /* Tell the thread to exit. */
  if (close(timeout->pipe[1]) == -1)
    perror_fatal("clear_timeout: close");
  timeout->pipe[1] = -1;

  /* Wait for the thread to exit. */
  if (pthread_join(timeout->thread, &value) == -1)
    perror_fatal("clear_timeout: pthread_join");

  timeout->state = TIMEOUT_READY;
}

#else /* !defined(THREAD_SAFE) */

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
timeout_t *init_timeout(void) {
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

  return &the_timeout;
}



/*
 * Activate the timer
 * - delay = timeout in seconds (must be positive)
 * - handler = the handler to call
 * - param = data passed to the handler
 *
 * On Solaris: set the signal handler here.
 */
void start_timeout(timeout_t *timeout, uint32_t delay, timeout_handler_t handler, void *param) {
  assert(timeout == &the_timeout);
  assert(delay > 0 && timeout->state == TIMEOUT_READY && handler != NULL);
  timeout->state = TIMEOUT_ACTIVE;
  timeout->handler = handler;
  timeout->param = param;

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
void clear_timeout(timeout_t *timeout) {
  assert(timeout == &the_timeout);
  
  // TODO: Check whether we should block the signals here?
  if (the_timeout->state == TIMEOUT_ACTIVE) {
    // not fired;
    the_timeout->state = TIMEOUT_CANCELED;
    (void) alarm(0); // cancel the alarm
  }
  the_timeout->state = TIMEOUT_READY;
}


/*
 * Final cleanup:
 * - cancel the timeout if it's active
 * - restore the original handler
 */
void delete_timeout(timeout_t *timeout) {
  assert(timeout == &the_timeout);
  
  if (timeout->state == TIMEOUT_ACTIVE) {
    (void) alarm(0);
  }
  (void) signal(SIGALRM, saved_handler);
  timeout->state = TIMEOUT_NOT_READY;
}

#endif /* defined(THREAD_SAFE) */

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
timeout_t *init_timeout(void) {
  timer_queue = CreateTimerQueue();
  if (timer_queue == NULL) {
    fprintf(stderr, "Yices: CreateTimerQueue failed with error code %"PRIu32"\n", (uint32_t) GetLastError());
    fflush(stderr);
    exit(YICES_EXIT_INTERNAL_ERROR);
  }

  the_timeout.state = TIMEOUT_READY;
  the_timeout.handler = NULL;
  the_timeout.param = NULL;

  return &the_timeout;
}



/*
 * Activate:
 * - delay = timeout in seconds (must be positive)
 * - handler = handler to call if fired
 * - param = parameter for the handler
 */
void start_timeout(timeout_t *timeout, uint32_t delay, timeout_handler_t handler, void *param) {
  DWORD duetime;

  assert(timeout == &the_timeout);
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
void clear_timeout(timeout_t *timeout) {
  // GetLastError returns DWORD, which is an unsigned 32bit integer
  uint32_t error_code;

  assert(timeout == &the_timeout);

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
void delete_timeout(timeout_t *timeout) {
  assert(timeout == &the_timeout);
  
  if (! DeleteTimerQueueEx(timer_queue, INVALID_HANDLE_VALUE)) {
    fprintf(stderr, "Yices: DeleteTimerQueueEx failed with error code %"PRIu32"\n", (uint32_t) GetLastError());
    fflush(stderr);
    exit(YICES_EXIT_INTERNAL_ERROR);
  }
}




#endif /* MINGW */
