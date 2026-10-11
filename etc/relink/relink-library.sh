#!/bin/sh
#
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
#
# Relink the Yices shared library from the published relink kit.
#
# You do not need this to install or run Yices. See README.
#
# Usage:
#   ./relink-library.sh [output-directory]
#
# Output directory defaults to ./relinked.
#
# To relink against your own build of a library:
#
#   GMP_A=/path/to/your/libgmp.a       ./relink-library.sh
#   LIBPOLY_A=/path/to/your/libpoly.a  ./relink-library.sh
#
# Your GMP must be built as position-independent code. See the note below.

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

SONAME=${SONAME:-libyices.so.2.8}
LIBNAME=${LIBNAME:-libyices.so.2.8.0}

libdir=$kit/library
depsdir=$kit/deps

# ---------------------------------------------------------------------------
# The Yices side of the shared library.
#
# This is NOT executables/libyices.a. The shared library is built from a
# separate set of objects compiled with -fPIC. The static archive contains
# additional objects, and many common-named objects differ byte for byte.
# Using executables/libyices.a here will not reproduce the published library.
# ---------------------------------------------------------------------------

LIBYICES_PIC_A=${LIBYICES_PIC_A:-$libdir/libyices-pic.a}

# ---------------------------------------------------------------------------
# The shared library uses the no-assembly position-independent GMP, not the
# non-PIC archive the executables use. Disabling assembly is the release's
# PIC build policy, not a general limitation of GMP's x86-64 assembly. A
# replacement must be a compatible PIC build; verify both link and execution.
# ---------------------------------------------------------------------------

GMP_A=${GMP_A:-$depsdir/libgmp-pic.a}

LIBPOLY_A=${LIBPOLY_A:-$depsdir/libpicpoly.a}
CUDD_A=${CUDD_A:-$depsdir/libcudd.a}
CADICAL_A=${CADICAL_A:-$depsdir/libcadical.a}
CMS_A=${CMS_A:-$depsdir/libcryptominisat5.a}
KISSAT_A=${KISSAT_A:-$depsdir/libkissat_yices.a}

# The release build deliberately supplies CUDD's PIC static archive directly.
# This prevents -lcudd from selecting a shared object and keeps CUDD out of
# the shared library's DT_NEEDED list.

# Order is load-bearing here too: GMP last. Keep paths as distinct arguments
# so the shell does not split a valid archive path that contains whitespace.
set -- "$CUDD_A" -lm "$CMS_A" "$CADICAL_A" "$KISSAT_A" \
    -lstdc++ -lm -lpthread "$LIBPOLY_A" "$GMP_A"

_last=
for _item do
    _last=$_item
done
if [ "$_last" != "$GMP_A" ]; then
    echo "relink: internal error, GMP is not last in the archive list" >&2
    echo "relink: expected final item: $GMP_A" >&2
    echo "relink: actual final item: ${_last:-NONE}" >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# Preflight.
# ---------------------------------------------------------------------------

if [ "$SKIP_VERIFY" != "1" ]; then
    "$kit/verify-manifest.sh" "$kit"
else
    echo "relink: SKIP_VERIFY=1, manifest check bypassed"
fi

missing=0
for f in "$LIBYICES_PIC_A" "$GMP_A" "$LIBPOLY_A" "$CUDD_A" "$CADICAL_A" \
         "$CMS_A" "$KISSAT_A"; do
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
echo "relink: output $outdir/$LIBNAME, soname $SONAME"
echo

# ---------------------------------------------------------------------------
# Link.
#
# --whole-archive is required and must not be removed. Without it the linker
# pulls only the archive members that resolve an already-undefined symbol,
# which silently produces a shared library missing most of the Yices API. The
# production rule links loose object files, where this does not arise; the kit
# ships an archive, where it does.
#
# --no-undefined makes an incomplete link fail here rather than at load time.
# The explicit -lc matches the production rule.
# ---------------------------------------------------------------------------

echo "relink: building $LIBNAME"
echo "  $CC $CFLAGS -shared -o $outdir/$LIBNAME -Wl,-soname,$SONAME -Wl,--no-undefined -Wl,--whole-archive $LIBYICES_PIC_A -Wl,--no-whole-archive $* -lc"

# shellcheck disable=SC2086
"$CC" $CFLAGS -shared -o "$outdir/$LIBNAME" \
    -Wl,-soname,"$SONAME" -Wl,--no-undefined \
    -Wl,--whole-archive "$LIBYICES_PIC_A" -Wl,--no-whole-archive \
    "$@" -lc

echo "  ok"
echo

# A successful shared-object link is not enough.  In particular, a C++
# runtime older than the one recorded in BUILDINFO can leave references from
# the GCC-14-built archives unresolved while still letting this command exit
# zero.  Force the new DSO into a trivial executable link so the script does
# not report success for a library that an ordinary C API client cannot use.
probe_dir=$(mktemp -d "${TMPDIR:-/tmp}/yices-relink-probe.XXXXXX") || {
    echo "relink: could not create the post-link probe directory" >&2
    exit 1
}
cleanup_probe() {
    rm -rf -- "$probe_dir"
}
trap cleanup_probe 0 1 2 15
cat > "$probe_dir/probe.c" <<'EOF'
extern void yices_init(void);
int main(void) { yices_init(); return 0; }
EOF
if ! "$CC" "$probe_dir/probe.c" -Wl,--no-as-needed \
        "$outdir/$LIBNAME" -o "$probe_dir/probe"; then
    echo "relink: the selected C++ runtime cannot link a client against $LIBNAME" >&2
    echo "relink: use a toolchain compatible with BUILDINFO; see README" >&2
    exit 1
fi
echo "relink: post-link client usability check passed"
cleanup_probe
trap - 0 1 2 15
echo

# ---------------------------------------------------------------------------
# Symlinks, matching what install-yices creates in a normal installation.
# ---------------------------------------------------------------------------

( cd "$outdir" && ln -sf "$LIBNAME" "$SONAME" && ln -sf "$SONAME" libyices.so )

echo "relink: created symlinks $SONAME -> $LIBNAME and libyices.so -> $SONAME"
echo
echo "relink: check the result with:"
echo "  readelf -dW $outdir/$LIBNAME | grep -E 'SONAME|NEEDED'"
