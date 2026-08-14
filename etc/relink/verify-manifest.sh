#!/bin/sh
#
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
#
# Verify every file in the Yices relink kit against MANIFEST.sha256.
#
# Run this before relinking. The relink scripts call it automatically, but it
# is safe and useful to run on its own after downloading and extracting.
#
# Usage:  ./verify-manifest.sh [kit-directory]
#
# The kit directory defaults to the directory holding this script.

set -eu

kit=${1:-$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)}

if [ ! -f "$kit/MANIFEST.sha256" ]; then
    echo "verify-manifest: no MANIFEST.sha256 in $kit" >&2
    exit 1
fi

# Pick a checksum tool. sha256sum on Linux, shasum -a 256 on systems that
# lack it. Both accept the same check format.
if command -v sha256sum >/dev/null 2>&1; then
    check() { sha256sum -c MANIFEST.sha256; }
elif command -v shasum >/dev/null 2>&1; then
    check() { shasum -a 256 -c MANIFEST.sha256; }
else
    echo "verify-manifest: need sha256sum or shasum on PATH" >&2
    exit 1
fi

echo "verify-manifest: checking $kit/MANIFEST.sha256"

# The manifest paths are relative to the kit root, so check from there.
( cd "$kit" && check )

echo "verify-manifest: all files match"
