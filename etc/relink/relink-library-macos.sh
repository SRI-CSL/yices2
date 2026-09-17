#!/bin/sh
#
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
#
# Relink the Yices macOS dynamic library from an extracted release kit.

set -eu

kit=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
outdir=${1:-./relinked}

CC=${CC:-cc}
SKIP_VERIFY=${SKIP_VERIFY:-0}
CFLAGS=${CFLAGS:--fvisibility=hidden -O3 -fomit-frame-pointer -fno-stack-protector}
export MACOSX_DEPLOYMENT_TARGET=11.0

depsdir=$kit/deps
LIBNAME=${LIBNAME:-libyices.2.dylib}
INSTALL_NAME=${INSTALL_NAME:-@rpath/libyices.2.dylib}

LIBYICES_A=${LIBYICES_A:-$depsdir/libyices-dylib.a}
CUDD_A=${CUDD_A:-$depsdir/libcudd.a}
CMS_A=${CMS_A:-$depsdir/libcryptominisat5.a}
CADICAL_A=${CADICAL_A:-$depsdir/libcadical.a}
KISSAT_A=${KISSAT_A:-$depsdir/libkissat_yices.a}
LIBPOLY_A=${LIBPOLY_A:-$depsdir/libpicpoly.a}

if [ -f "$depsdir/libgmp-pic.a" ]; then
    default_gmp=$depsdir/libgmp-pic.a
else
    default_gmp=$depsdir/libgmp-static.a
fi
GMP_A=${GMP_A:-$default_gmp}

# Archive order is load-bearing. GMP must be the final archive. Keep paths as
# distinct arguments so the shell does not split a valid archive path that
# contains whitespace.
set -- "$CUDD_A" -lm "$CMS_A" "$CADICAL_A" "$KISSAT_A" \
    -lc++ -lm "$LIBPOLY_A" "$GMP_A"

# Test hook for the required negative test. It changes no normal invocation.
if [ "${RELINK_TEST_GMP_NOT_LAST:-0}" = 1 ]; then
    set -- "$@" -lm
fi

assert_last() {
    _expected=$1
    shift
    _last=
    for _item do
        _last=$_item
    done
    if [ "$_last" != "$_expected" ]; then
        echo "relink: internal error, GMP is not last in the archive list" >&2
        echo "relink: expected final item: $_expected" >&2
        echo "relink: actual final item: ${_last:-NONE}" >&2
        exit 1
    fi
}

assert_last "$GMP_A" "$@"

if [ "$SKIP_VERIFY" != 1 ]; then
    "$kit/verify-manifest.sh" "$kit"
else
    echo "relink: SKIP_VERIFY=1, manifest check bypassed"
fi

missing=0
for file in "$LIBYICES_A" "$CUDD_A" "$CMS_A" "$CADICAL_A" \
    "$KISSAT_A" "$LIBPOLY_A" "$GMP_A"; do
    if [ ! -f "$file" ]; then
        echo "relink: missing required input: $file" >&2
        missing=1
    fi
done
[ "$missing" -eq 0 ] || exit 1

command -v "$CC" >/dev/null 2>&1 || {
    echo "relink: compiler driver '$CC' not found; set CC" >&2
    exit 1
}
command -v codesign >/dev/null 2>&1 || {
    echo "relink: codesign not found" >&2
    exit 1
}

mkdir -p "$outdir"

echo "relink: CC=$CC"
"$CC" --version 2>/dev/null | head -1 | sed 's/^/relink:   /' || true
echo "relink: MACOSX_DEPLOYMENT_TARGET=$MACOSX_DEPLOYMENT_TARGET"
echo "relink: output $outdir/$LIBNAME"
echo

echo "relink: building $LIBNAME"
echo "  $CC $CFLAGS -dynamiclib -current_version 2.8.0 -compatibility_version 2.8.0 -Wl,-install_name,$INSTALL_NAME -Wl,-headerpad_max_install_names -Wl,-dead_strip -Wl,-force_load,$LIBYICES_A -o $outdir/$LIBNAME $*"

# shellcheck disable=SC2086
"$CC" $CFLAGS -dynamiclib \
    -current_version 2.8.0 \
    -compatibility_version 2.8.0 \
    -Wl,-install_name,"$INSTALL_NAME" \
    -Wl,-headerpad_max_install_names \
    -Wl,-dead_strip \
    -Wl,-force_load,"$LIBYICES_A" \
    -o "$outdir/$LIBNAME" "$@"

codesign -s - "$outdir/$LIBNAME"

echo "  ok"
echo
echo "relink: verify with:"
echo "  otool -D $outdir/$LIBNAME"
echo "  otool -L $outdir/$LIBNAME"
echo "  lipo -info $outdir/$LIBNAME"
echo "  otool -l $outdir/$LIBNAME | grep -A3 LC_BUILD_VERSION"
