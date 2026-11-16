#!/bin/sh
#
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
#
# Relink the Yices command-line executables from the published relink kit.
#
# You do not need this to install or run Yices. See README.
#
# Usage:
#   ./relink-executables.sh [output-directory]
#
# Output directory defaults to ./relinked.
#
# To relink against your own build of a library, replace the archive in deps/
# before running, or point the matching variable at your file:
#
#   GMP_A=/path/to/your/libgmp.a       ./relink-executables.sh
#   LIBPOLY_A=/path/to/your/libpoly.a  ./relink-executables.sh
#
# Replacing an archive makes MANIFEST.sha256 fail, which is expected. Set
# SKIP_VERIFY=1 to proceed. Verify first with the unmodified kit so that you
# know the kit itself is intact before you introduce a change.

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

# ---------------------------------------------------------------------------
# Flags. These are this script's own defaults, not the values the production
# link used. BUILDINFO records the values that produced the published
# binaries, and the README lists where the two differ. Set CC and CFLAGS to
# the BUILDINFO values for the closest match to those binaries.
#
# No compiler version is hardcoded. The objects in this kit were produced by
# the compiler named in BUILDINFO. See the README on toolchain differences.
# ---------------------------------------------------------------------------

CFLAGS=${CFLAGS:--fvisibility=hidden -O3 -fomit-frame-pointer -fno-stack-protector}
STATIC_FLAG=${STATIC_FLAG:--static}
BIN_LDFLAGS=${BIN_LDFLAGS:-}

# ---------------------------------------------------------------------------
# Inputs.
# ---------------------------------------------------------------------------

objdir=$kit/executables
depsdir=$kit/deps

LIBYICES_A=${LIBYICES_A:-$objdir/libyices.a}

# Two distinct GMP archives ship in this kit and they are NOT interchangeable.
# The executables use the optimized static build. The shared library uses the
# no-assembly position-independent build. Using the wrong one here produces a
# binary that differs from the published one, and may fail to link.
GMP_A=${GMP_A:-$depsdir/libgmp-static.a}

# The executable build uses LibPoly's optimized normal archive.  The PIC
# archive is reserved for relink-library.sh.
LIBPOLY_A=${LIBPOLY_A:-$depsdir/libpoly.a}
CUDD_A=${CUDD_A:-$depsdir/libcudd.a}
CADICAL_A=${CADICAL_A:-$depsdir/libcadical.a}
CMS_A=${CMS_A:-$depsdir/libcryptominisat5.a}
KISSAT_A=${KISSAT_A:-$depsdir/libkissat_yices.a}

# ---------------------------------------------------------------------------
# Library arguments.
#
# ORDER IS LOAD-BEARING. GMP must come last: the other archives depend on it,
# and a static linker resolves left to right. This is checked below rather
# than merely documented, because reordering it produces link errors that look
# like missing symbols in unrelated code.
#
# yices-sat is deliberately different. It contains neither GMP nor LibPoly.
# Its production rule (src/Makefile) links STATIC_NOGMP_LIBS, not STATIC_LIBS.
# Do not merge these two lists.
# ---------------------------------------------------------------------------

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

# Keep paths as distinct arguments. Serializing them into a scalar would make
# the shell split a valid archive path that contains whitespace.
set -- "$CUDD_A" -lm "$CMS_A" "$CADICAL_A" "$KISSAT_A" \
    -lstdc++ -lm -lpthread "$LIBPOLY_A" "$GMP_A"
assert_last "$GMP_A" "$@"

# ---------------------------------------------------------------------------
# Preflight.
# ---------------------------------------------------------------------------

if [ "$SKIP_VERIFY" != "1" ]; then
    "$kit/verify-manifest.sh" "$kit"
else
    echo "relink: SKIP_VERIFY=1, manifest check bypassed"
fi

missing=0
for f in "$objdir/yices.o" "$objdir/yices_sat.o" "$objdir/yices_smtcomp.o" \
         "$objdir/yices_smt2.o" "$LIBYICES_A" "$GMP_A" "$LIBPOLY_A" \
         "$CUDD_A" "$CADICAL_A" "$CMS_A" "$KISSAT_A"; do
    if [ ! -f "$f" ]; then
        echo "relink: missing required input: $f" >&2
        missing=1
    fi
done
[ "$missing" -eq 0 ] || exit 1

command -v "$CC" >/dev/null 2>&1 || {
    echo "relink: compiler driver '$CC' not found; set CC" >&2
    exit 1
}

mkdir -p "$outdir"

echo "relink: CC=$CC"
"$CC" --version 2>/dev/null | head -1 | sed 's/^/relink:   /' || true
echo "relink: output directory $outdir"
echo

# ---------------------------------------------------------------------------
# Link.
#
# link <output-name> <front-end-object> <library-list>
# ---------------------------------------------------------------------------

link() {
    _out=$1
    _obj=$2
    shift 2

    echo "relink: building $_out"
    # Print the command before running it, so it can be compared with the
    # corresponding link-* field in BUILDINFO. The invocation below preserves
    # each fixed input as a distinct argument even when its path has whitespace.
    echo "  $CC $CFLAGS $BIN_LDFLAGS $STATIC_FLAG -o $outdir/$_out $_obj $LIBYICES_A $*"

    # shellcheck disable=SC2086
    "$CC" $CFLAGS $BIN_LDFLAGS $STATIC_FLAG \
        -o "$outdir/$_out" "$_obj" "$LIBYICES_A" "$@"

    echo "  ok"
    echo
}

# The three front ends that use GMP and LibPoly.
link yices      "$objdir/yices.o"          "$@"
link yices-smt  "$objdir/yices_smtcomp.o"  "$@"
link yices-smt2 "$objdir/yices_smt2.o"     "$@"

# yices-sat: no GMP, no LibPoly. See the comment on the library lists.
# If you modified only GMP or LibPoly, this binary is unaffected and you do
# not need to replace the published one. The C library it links comes from
# this machine rather than from the kit. See the README on yices-sat.
link yices-sat "$objdir/yices_sat.o" \
    "$CUDD_A" -lm "$CMS_A" "$CADICAL_A" "$KISSAT_A" \
    -lstdc++ -lm -lpthread

echo "relink: all four executables written to $outdir"
echo "relink: smoke-test with:  $outdir/yices --version"
