#!/bin/sh
#
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
#
# Capture, at build time, the source packages and metadata that the release
# must publish alongside the binary artifacts.
#
# This has to run ON THE PRODUCTION BUILDER, DURING THE BUILD. Distribution
# archives rotate. A glibc point release available today may be gone from the
# primary mirror in weeks, and the exact patch level is what matters. Do not
# defer this step and do not reconstruct it afterward from memory.
#
# Usage:
#   scripts/capture-release-provenance.sh <output-directory>
#
# Build-artifact inputs:
#   YICES_BIN_DIR   directory containing the four release executables
#   YICES_LIB_DIR   directory containing the versioned shared library;
#                   optional for compatibility with direct invocations
#
# Produces, under <output-directory>:
#
#   PROVENANCE                 key/value metadata, feeds BUILDINFO
#   SHA256SUMS                 checksums of everything captured
#   glibc/                     glibc source package, distribution patches included
#   gmp/                       GMP source tarball
#   libpoly/                   LibPoly source tarball made from the locked commit
#
# Exit status is nonzero if any required capture fails. A partial capture is
# worse than an obvious failure, because it looks complete.

set -eu

if [ $# -lt 1 ]; then
    echo "usage: $0 <output-directory>" >&2
    exit 2
fi

out=$1
mkdir -p "$out"
out=$(CDPATH= cd -- "$out" && pwd)

prov=$out/PROVENANCE
: > "$prov"

emit() { printf '%s: %s\n' "$1" "$2" >> "$prov"; }

note() { echo "capture: $*"; }
fail() { echo "capture: ERROR: $*" >&2; exit 1; }
sha256_file() {
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" | cut -d' ' -f1
    elif command -v shasum >/dev/null 2>&1; then
        shasum -a 256 "$1" | awk '{print $1}'
    else
        fail "need sha256sum or shasum on PATH"
    fi
}
find_yices_shared_library() {
    _libdir=$1
    [ -d "$_libdir" ] || fail "YICES_LIB_DIR is not a directory: $_libdir"
    case "$platform" in
        Darwin) _pattern=$_libdir/libyices.*.dylib ;;
        *)      _pattern=$_libdir/libyices.so.* ;;
    esac

    _found=
    for _candidate in $_pattern; do
        [ -f "$_candidate" ] || continue
        [ -z "$_found" ] || fail "multiple Yices shared libraries match YICES_LIB_DIR=$_libdir: $_found and $_candidate"
        _found=$_candidate
    done
    [ -n "$_found" ] || fail "Yices shared library not found in YICES_LIB_DIR=$_libdir (expected $_pattern)"
    yices_lib_file=$_found
}

# Values the caller may override; otherwise best-effort discovery.
platform=$(uname -s)
CC=${CC:-gcc}
cc_version=$($CC --version 2>/dev/null | head -1)
[ -n "$cc_version" ] || cc_version=version-unavailable
LIBPOLY_REPO=${LIBPOLY_REPO:-https://github.com/SRI-CSL/libpoly.git}
LIBPOLY_COMMIT=${LIBPOLY_COMMIT:-c342ff1ad2f0cbcfc866b1ef024003ccc001add2}
GMP_VERSION=${GMP_VERSION:-6.3.0}
GMP_URL=${GMP_URL:-https://gmplib.org/download/gmp/gmp-${GMP_VERSION}.tar.xz}
GMP_SHA256=${GMP_SHA256:-a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898}

# The production Make target always supplies the library directory. Preserve
# the former direct-invocation behavior when it is unset: Linux did not inspect
# a shared library, while macOS looked beside the executables.
yices_lib_file=
if [ -n "${YICES_LIB_DIR:-}" ]; then
    find_yices_shared_library "$YICES_LIB_DIR"
fi

# ---------------------------------------------------------------------------
# 0. Build environment identity
# ---------------------------------------------------------------------------

note "recording build environment"

emit capture-utc          "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
emit hostname             "not-recorded"
emit kernel               "$(uname -sr)"
emit arch                 "$(uname -m)"

if [ -r /etc/os-release ]; then
    # shellcheck disable=SC1091
    . /etc/os-release
    emit os-id            "${ID:-unknown}"
    emit os-version       "${VERSION_ID:-unknown}"
    emit os-pretty        "${PRETTY_NAME:-unknown}"
fi

# When building in a container, the image digest is the only durable identity.
# Nothing on the inside can discover it reliably, so the invoker passes it.
if [ -n "${BUILDER_IMAGE_DIGEST:-}" ]; then
    emit builder-image-digest "$BUILDER_IMAGE_DIGEST"
else
    emit builder-image-digest "NOT-SUPPLIED"
    note "WARNING: BUILDER_IMAGE_DIGEST not set."
    note "         If this is a container build, set it. Without it the"
    note "         build environment cannot be identified later."
fi

emit cc "$CC"
if [ "$platform" = Darwin ]; then
    emit cc-version       "$cc_version"
    emit ld-version       "$(ld -v 2>&1 | head -1)"
    ar_version=$(ar -V 2>&1 | head -1)
    case "$ar_version" in
        "" | usage:* | Usage:* | ar:\ *) ar_version=version-unavailable ;;
    esac
    emit ar-version       "$ar_version"
    emit libc-runtime     "macOS libSystem (see otool-dependencies below)"
else
    # Keep the Linux fields byte-for-byte compatible with the original path.
    emit cc-version       "$cc_version"
    emit ld-version       "$(ld --version 2>/dev/null | head -1)"
    emit ar-version       "$(ar --version 2>/dev/null | head -1)"
    emit libc-runtime     "$(ldd --version 2>/dev/null | head -1)"
fi

# ---------------------------------------------------------------------------
# 1. The C library actually linked
#
# Establish the chain: linked file -> owning package -> source package.
# Hash the file itself, because that is the thing the binaries contain.
# ---------------------------------------------------------------------------

if [ "$platform" = Darwin ]; then
    note "recording the macOS system C library and Mach-O identities"
    emit packaging macos
    emit c-library-linkage "dynamic, supplied by macOS libSystem"
    emit c-library-identity "/usr/lib/libSystem.B.dylib from LC_LOAD_DYLIB"
    emit binary-format Mach-O
    emit binary-id-kind LC_UUID

    [ -n "${YICES_BIN_DIR:-}" ] || fail "YICES_BIN_DIR is required on macOS.
       Set it to the static_bin directory containing all four release
       executables. Set YICES_LIB_DIR if the shared library is elsewhere."
    [ -d "$YICES_BIN_DIR" ] || fail "YICES_BIN_DIR is not a directory: $YICES_BIN_DIR"
    command -v otool >/dev/null 2>&1 || fail "otool is required on macOS"
    command -v nm >/dev/null 2>&1 || fail "nm is required on macOS"

    if [ -z "$yices_lib_file" ]; then
        find_yices_shared_library "$YICES_BIN_DIR"
    fi

    for item in \
        "yices:$YICES_BIN_DIR/yices" \
        "yices-sat:$YICES_BIN_DIR/yices-sat" \
        "yices-smt:$YICES_BIN_DIR/yices-smt" \
        "yices-smt2:$YICES_BIN_DIR/yices-smt2" \
        "libyices:$yices_lib_file"; do
        name=${item%%:*}
        binary=${item#*:}
        if [ ! -f "$binary" ]; then
            case "$name" in
                yices-sat)  binary=$YICES_BIN_DIR/yices_sat ;;
                yices-smt)  binary=$YICES_BIN_DIR/yices_smtcomp ;;
                yices-smt2) binary=$YICES_BIN_DIR/yices_smt2 ;;
            esac
        fi
        [ -f "$binary" ] || fail "required Mach-O output not found for $name in $YICES_BIN_DIR"
        deps=$(otool -l "$binary" | awk '
            $1 == "cmd" && $2 == "LC_LOAD_DYLIB" { load=1; next }
            load && $1 == "name" { print $2; load=0 }
        ' | paste -s -d, -)
        uuid=$(otool -l "$binary" | awk '/cmd LC_UUID/{seen=1; next} seen && /uuid /{print $2; exit}')
        [ -n "$uuid" ] || fail "LC_UUID not found in $binary"
        emit "macho-$name-path" "$(basename -- "$binary")"
        emit "macho-$name-sha256" "$(sha256_file "$binary")"
        emit "macho-$name-lc-load-dylib" "${deps:-NONE}"
        emit "macho-$name-lc-uuid" "$uuid"
    done

    emit libxcrypt-symbols-found "NOT-APPLICABLE, macOS uses libSystem"
    note "macOS uses the system libSystem; no glibc or libxcrypt source capture is owed"
else
note "locating the static C library actually linked"

libc_a=$($CC -print-file-name=libc.a 2>/dev/null || true)
[ -n "$libc_a" ] && [ -f "$libc_a" ] || fail "cannot find libc.a; is the static libc package installed?"

libc_a=$(readlink -f "$libc_a")
emit glibc-archive-path   "$libc_a"
emit glibc-archive-sha256 "$(sha256sum "$libc_a" | cut -d' ' -f1)"

mkdir -p "$out/glibc"

if command -v rpm >/dev/null 2>&1; then
    # ---- PRIMARY: RHEL family. This is the production path. ---------------
    #
    # Production builds run in
    #   quay.io/pypa/manylinux_2_28_x86_64@sha256:e0b40ace...82ae8
    # which is AlmaLinux 8 based. glibc-static comes from PowerTools.
    #
    # The correspondence argument here is exact by construction rather than
    # by inference: the binary package NEVR and the source RPM NEVR are the
    # same NEVR, so the source we publish is the source the linked archive
    # was built from. That is asserted below and checked, not assumed.
    note "RPM-family builder (primary path)"
    emit packaging rpm

    # The image digest is the only durable identity of a container build, and
    # a tag is not sufficient because manylinux images are rebuilt under the
    # same tag. On this path it is required, not advisory.
    if [ -z "${BUILDER_IMAGE_DIGEST:-}" ]; then
        fail "BUILDER_IMAGE_DIGEST is required on the rpm path.
       A tag does not identify the package set that produced these objects,
       because manylinux images are rebuilt under the same tag. Pass the
       digest, for example:
         BUILDER_IMAGE_DIGEST=sha256:e0b40ace...82ae8 $0 $out"
    fi

    if [ -z "${YICES_BIN_DIR:-}" ]; then
        fail "YICES_BIN_DIR is required on the rpm path.
       Set it to the static_bin directory containing all four release
       executables so the libxcrypt symbol gate cannot be skipped."
    fi
    if [ ! -d "$YICES_BIN_DIR" ]; then
        fail "YICES_BIN_DIR is not a directory: $YICES_BIN_DIR"
    fi

    binpkg=$(rpm -qf --qf '%{NAME}' "$libc_a" 2>/dev/null) \
        || fail "no package owns $libc_a.
       If glibc-static is not installed there is no libc.a and no fully
       static build. Install it from PowerTools in the Dockerfile."
    emit glibc-binary-package "$binpkg"

    bin_nevr=$(rpm -q --qf '%{VERSION}-%{RELEASE}' "$binpkg")
    emit glibc-binary-nevr  "$bin_nevr"
    emit glibc-binary-nevra "$(rpm -q --qf '%{NEVRA}' "$binpkg")"

    srcrpm=$(rpm -q --qf '%{SOURCERPM}' "$binpkg")
    emit glibc-source-rpm "$srcrpm"

    # Derive the source NEVR from the SOURCERPM filename, then require it to
    # equal the binary NEVR. This is the correspondence evidence. Record the
    # comparison either way so the PROVENANCE file carries the proof rather
    # than a claim that a check was performed.
    src_nevr=$(echo "$srcrpm" | sed -e 's/\.src\.rpm$//' -e "s/^${binpkg%%-static}-//" -e "s/^glibc-//")
    emit glibc-source-nevr "$src_nevr"

    if [ "$bin_nevr" = "$src_nevr" ]; then
        emit glibc-nevr-match "YES, binary and source NEVR are identical"
        note "NEVR match confirmed: $bin_nevr"
    else
        emit glibc-nevr-match "NO"
        fail "glibc binary NEVR ($bin_nevr) does not equal source NEVR ($src_nevr).
       Correspondence cannot be established by construction. Do not continue
       and do not substitute a different patch level."
    fi

    # Source repos are normally absent or disabled in RHEL-derived images, and
    # AlmaLinux 8 has moved to the vault. Try dnf first, then the vault URL
    # built from the exact SOURCERPM name. Never fall back to a different NEVR.
    if command -v dnf >/dev/null 2>&1 &&
       ( cd "$out/glibc" && dnf download --source "$binpkg" >/dev/null 2>&1 ); then
        note "obtained $srcrpm via dnf"
        emit glibc-source-method "dnf download --source"
    else
        note "dnf source download unavailable, using the AlmaLinux vault"
        relver=${VERSION_ID:-8}
        url="https://repo.almalinux.org/vault/${relver}/BaseOS/Source/Packages/${srcrpm}"
        emit glibc-source-url    "$url"
        emit glibc-source-method "vault fetch by exact SOURCERPM name"
        ( cd "$out/glibc" && curl -fSL -O "$url" ) \
            || fail "could not obtain $srcrpm.
       Neither dnf nor the vault URL worked. Do not continue and do not
       substitute a different patch level."
    fi

elif command -v dpkg-query >/dev/null 2>&1; then
    # ---- SECONDARY: Debian and Ubuntu ------------------------------------
    #
    # Retained for the Ubuntu validation host. Not the production path.
    note "Debian-family builder (secondary path)"
    emit packaging debian

    binpkg=$(dpkg -S "$libc_a" 2>/dev/null | cut -d: -f1) \
        || fail "no package owns $libc_a"
    emit glibc-binary-package "$binpkg"
    emit glibc-binary-version "$(dpkg-query -W -f='${Version}' "$binpkg")"

    srcinfo=$(dpkg-query -W -f='${source:Package} ${source:Version}' "$binpkg")
    emit glibc-source-package "$(echo "$srcinfo" | cut -d' ' -f1)"
    emit glibc-source-version "$(echo "$srcinfo" | cut -d' ' -f2)"

    if ! apt-get source --print-uris "$(echo "$srcinfo" | cut -d' ' -f1)" \
            >/dev/null 2>&1; then
        fail "apt-get source is unavailable: no deb-src URIs configured.
       Add 'deb-src' to the Types: line in
       /etc/apt/sources.list.d/ubuntu.sources and run apt-get update."
    fi

    ( cd "$out/glibc" && apt-get source --download-only \
        "$(echo "$srcinfo" | cut -d' ' -f1)" ) \
        || fail "apt-get source failed for glibc"
else
    fail "unrecognised packaging system; cannot establish glibc source correspondence"
fi

# ---------------------------------------------------------------------------
# 1b. libxcrypt, conditional
#
# Installing glibc-static pulls libxcrypt-static, which is LGPL-2.1-or-later.
# As of 2026-08-07 nothing in Yices or its bundled dependencies references a
# crypt function, so libcrypt.a does not link in and no source capture is
# owed.
#
# That is a property of the current code, not a permanent one. Check the
# built executables rather than trusting the report, and capture the source
# if the answer ever flips.
# ---------------------------------------------------------------------------

if [ -n "${YICES_BIN_DIR:-}" ] && [ -d "$YICES_BIN_DIR" ]; then
    note "checking built executables for libxcrypt symbols"
    crypt_hits=0
    for name in yices yices-sat yices-smt yices-smt2; do
        b=$YICES_BIN_DIR/$name
        if [ ! -f "$b" ]; then
            case "$name" in
                yices-sat)  b=$YICES_BIN_DIR/yices_sat ;;
                yices-smt)  b=$YICES_BIN_DIR/yices_smtcomp ;;
                yices-smt2) b=$YICES_BIN_DIR/yices_smt2 ;;
            esac
        fi
        [ -f "$b" ] || fail "required built executable not found for $name in $YICES_BIN_DIR"
        n=$(nm --defined-only "$b" 2>/dev/null |
            grep -cE '\b(crypt|crypt_r|crypt_rn|crypt_ra|crypt_gensalt)\b|_xcrypt|_crypt_' || true)
        crypt_hits=$((crypt_hits + n))
    done
    emit libxcrypt-symbols-found "$crypt_hits"
    if [ "$crypt_hits" -gt 0 ]; then
        fail "libxcrypt symbols found in the built executables ($crypt_hits).
       libcrypt.a is LGPL-2.1-or-later and now carries a source and relink
       obligation. Capture libxcrypt source and add it to the kit and the
       notices before publishing."
    fi
    note "no libxcrypt symbols, no source capture owed"
else
    emit libxcrypt-symbols-found "NOT-CHECKED, YICES_BIN_DIR not set"
    note "WARNING: YICES_BIN_DIR not set, libxcrypt check skipped."
    note "         Set it to the static_bin directory to enable the check."
fi
fi

# ---------------------------------------------------------------------------
# 2. GMP
# ---------------------------------------------------------------------------

note "capturing GMP $GMP_VERSION"
mkdir -p "$out/gmp"
( cd "$out/gmp" && curl -fSL -O "$GMP_URL" ) || fail "GMP download failed"

gmp_file=$out/gmp/gmp-${GMP_VERSION}.tar.xz
got=$(sha256_file "$gmp_file")
[ "$got" = "$GMP_SHA256" ] || fail "GMP checksum mismatch: got $got expected $GMP_SHA256"

emit gmp-version          "$GMP_VERSION"
emit gmp-source-file      "$(basename "$gmp_file")"
emit gmp-source-sha256    "$got"
emit gmp-license-election "LGPL-3.0-or-later"

# ---------------------------------------------------------------------------
# 3. LibPoly
#
# The dependency lock pins a commit, and a commit is not a tarball. Produce
# one deterministically: git archive with a fixed prefix, then gzip -n so no
# timestamp is embedded.
# ---------------------------------------------------------------------------

note "producing a LibPoly tarball from $LIBPOLY_COMMIT"
mkdir -p "$out/libpoly"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

git clone --quiet --no-checkout "$LIBPOLY_REPO" "$work/libpoly" \
    || fail "libpoly clone failed"
git -C "$work/libpoly" fetch --quiet origin "$LIBPOLY_COMMIT" 2>/dev/null || true
git -C "$work/libpoly" cat-file -e "${LIBPOLY_COMMIT}^{commit}" \
    || fail "locked LibPoly commit $LIBPOLY_COMMIT not present in the clone"

short=$(echo "$LIBPOLY_COMMIT" | cut -c1-12)
git -C "$work/libpoly" archive --format=tar \
    --prefix="libpoly-${short}/" "$LIBPOLY_COMMIT" \
    | gzip -n -9 > "$out/libpoly/libpoly-${short}.tar.gz" \
    || fail "git archive failed"

emit libpoly-repo         "$LIBPOLY_REPO"
emit libpoly-commit       "$LIBPOLY_COMMIT"
emit libpoly-source-file  "libpoly-${short}.tar.gz"
emit libpoly-source-sha256 \
    "$(sha256_file "$out/libpoly/libpoly-${short}.tar.gz")"

# ---------------------------------------------------------------------------
# 4. Checksums over everything captured
# ---------------------------------------------------------------------------

note "writing SHA256SUMS"
( cd "$out" &&
  find . -type f ! -name SHA256SUMS -print | LC_ALL=C sort |
  while IFS= read -r file; do
      printf '%s  %s\n' "$(sha256_file "$file")" "$file"
  done > SHA256SUMS
)

note "done"
note "captured into $out"
note ""
note "Reminder: the link commands and the archive hashes from the Yices build"
note "itself are recorded separately, into the relink kit's BUILDINFO. This"
note "script covers the dependency source side only."
