/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef __ERROR_H
#define __ERROR_H

/* Like perror, but exit after printing the message. */
extern void perror_fatal(const char *s);
			 
/* Like perror, but use ERR as the error code and exit after printing
   the message. */
extern void perror_fatal_code(const char *s, int err);

#endif
