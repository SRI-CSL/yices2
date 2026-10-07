#!/bin/sh
#
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
#
# Relink the four Yices macOS executables from an extracted release kit.

set -eu

kit=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)
outdir=${1:-./relinked}

# Resolve before creating anything: only the reserved kit/relinked directory
# may receive output inside the kit. Custom destinations need an existing
# parent outside the kit so a later manifest check cannot reject our output.
output_error() {
    echo "relink: $*" >&2
    exit 1
}
output_parent=$(CDPATH= cd -P -- "$(dirname -- "$outdir")" && pwd -P) ||
    output_error "output parent must already exist: $outdir"
if [ -e "$outdir" ] || [ -L "$outdir" ]; then
    [ -d "$outdir" ] && [ ! -L "$outdir" ] ||
        output_error "output is not a real directory: $outdir"
    outdir=$(CDPATH= cd -P -- "$outdir" && pwd -P) || exit 1
else
    outdir=$output_parent/$(basename -- "$outdir")
fi
case "$outdir" in
    "$kit/relinked") ;;
    "$kit"|"$kit/"*)
        output_error "custom output must be outside the kit; use ./relinked or an external directory"
        ;;
esac

CC=${CC:-cc}
SKIP_VERIFY=${SKIP_VERIFY:-0}
CFLAGS=${CFLAGS:--fvisibility=hidden -O3 -fomit-frame-pointer -fno-stack-protector}
export MACOSX_DEPLOYMENT_TARGET=11.0

objdir=$kit/executables
depsdir=$kit/deps

LIBYICES_A=${LIBYICES_A:-$depsdir/libyices.a}
CUDD_A=${CUDD_A:-$depsdir/libcudd.a}
CMS_A=${CMS_A:-$depsdir/libcryptominisat5.a}
CADICAL_A=${CADICAL_A:-$depsdir/libcadical.a}
KISSAT_A=${KISSAT_A:-$depsdir/libkissat_yices.a}
LIBPOLY_A=${LIBPOLY_A:-$depsdir/libpoly.a}
GMP_A=${GMP_A:-$depsdir/libgmp-static.a}

# Archive order is load-bearing. yices-sat deliberately has neither LibPoly
# nor GMP. The other three put GMP last so circular GMP references resolve the
# same way as in the production link. Keep paths as distinct arguments so the
# shell does not split a valid archive path that contains whitespace.
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
for file in \
    "$objdir/yices.o" "$objdir/yices_sat.o" \
    "$objdir/yices_smtcomp.o" "$objdir/yices_smt2.o" \
    "$LIBYICES_A" "$CUDD_A" "$CMS_A" "$CADICAL_A" "$KISSAT_A" \
    "$LIBPOLY_A" "$GMP_A"; do
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
echo "relink: output directory $outdir"
echo

link() {
    _out=$1
    _obj=$2
    shift 2

    echo "relink: building $_out"
    echo "  $CC $CFLAGS -o $outdir/$_out $_obj $LIBYICES_A $*"
    # shellcheck disable=SC2086
    "$CC" $CFLAGS -o "$outdir/$_out" "$_obj" "$LIBYICES_A" "$@"
    codesign -s - "$outdir/$_out"
    echo "  ok"
    echo
}

link yices      "$objdir/yices.o"         "$@"
link yices-smt  "$objdir/yices_smtcomp.o" "$@"
link yices-smt2 "$objdir/yices_smt2.o"    "$@"
link yices-sat "$objdir/yices_sat.o" \
    "$CUDD_A" -lm "$CMS_A" "$CADICAL_A" "$KISSAT_A" -lc++ -lm

echo "relink: all four executables written to $outdir"
echo "relink: verify with:"
echo "  for f in $outdir/yices $outdir/yices-sat $outdir/yices-smt $outdir/yices-smt2; do"
echo "    lipo -info \"\$f\""
echo "    otool -L \"\$f\""
echo "    otool -l \"\$f\" | grep -A3 LC_BUILD_VERSION"
echo "    \"\$f\" --version"
echo "  done"
