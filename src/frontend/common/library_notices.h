/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef __FRONTEND_COMMON_LIBRARY_NOTICES_H
#define __FRONTEND_COMMON_LIBRARY_NOTICES_H

/* Preserve the distinct notices in the canonical LibPoly C/C++ source files,
 * not an invented project-wide date range. The u_memstream component is MIT;
 * the other LibPoly sources use LGPL-3.0-or-later. NOTICES carries the grants.
 * Frontends without MCSAT support do not incorporate LibPoly.
 */
#ifdef HAVE_MCSAT
#define YICES_LIBPOLY_NOTICES \
  "LibPoly source-file notices (MCSAT support):\n" \
  "Copyright 2015, SRI International.\n" \
  "Copyright 2024, SRI International.\n" \
  "LibPoly u_memstream: Copyright 2020 Lag Free Games, LLC\n"
#else
#define YICES_LIBPOLY_NOTICES ""
#endif

#endif
