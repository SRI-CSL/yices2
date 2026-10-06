#!/bin/sh
#
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
#
# Internal release-builder tool: capture, at build time, the source packages
# and metadata that the release must publish alongside the binary artifacts.
# It is shipped in the source archive for transparency, but is not a supported
# standalone end-user command. GMP, LibPoly, CUDD, CaDiCaL, CryptoMiniSat,
# and Kissat are canonical release inputs: one source archive for each is
# prepared before any platform build, and every builder must consume and
# verify those same bytes.
#
# This has to run ON THE PRODUCTION BUILDER, DURING THE BUILD. Distribution
# archives rotate. A glibc point release available today may be gone from the
# primary mirror in weeks, and the exact patch level is what matters. Do not
# defer the package-source capture and do not reconstruct it afterward from
# memory.
#
# Usage:
#   scripts/capture-release-provenance.sh <output-directory>
#
# Build-artifact inputs:
#   YICES_VERSION, YICES_SOURCE_REVISION, YICES_SOURCE_BRANCH,
#   YICES_TARGET_TRIPLE, YICES_BUILD_MODE, YICES_THREAD_SAFE
#                   release identity supplied by Make and checked against
#                   the checkout and the built yices executable
#   YICES_BIN_DIR   directory containing the four release executables
#   YICES_LIB_DIR   directory containing the versioned shared library
#   RELEASE_INPUTS_DIR
#                   verified canonical input directory made on the Linux host
#   GMP_SOURCE_ARCHIVE
#                   verified official GMP source archive used by this builder
#   GMP_SOURCE_RECEIPT
#                   receipt binding that source to this builder's GMP archives
#   GMP_STATIC_ARCHIVE, GMP_PIC_ARCHIVE
#                   exact GMP archives the Yices build consumes
#   GMP_NORMAL_HEADER, GMP_PIC_HEADER
#                   exact generated gmp.h files paired with those archives
#   LIBPOLY_SOURCE_RECEIPT
#                   receipt written when the configured LibPoly was built
#   LIBPOLY_STATIC_ARCHIVE, LIBPOLY_PIC_ARCHIVE
#                   exact LibPoly archives the Yices build consumes
#   LIBPOLY_HEADER_DIR
#                   exact installed poly/ header tree the Yices build consumes
#   DEPENDENCY_SOURCE_RECEIPT
#                   receipt for the CUDD, CaDiCaL, CryptoMiniSat, and Kissat
#                   build performed natively on this builder
#   DEPENDENCY_INCLUDE_DIR
#                   installed headers bound by that receipt
#   CUDD_STATIC_ARCHIVE, CADICAL_STATIC_ARCHIVE,
#   CRYPTOMINISAT_STATIC_ARCHIVE, KISSAT_RAW_ARCHIVE,
#   KISSAT_NAMESPACED_ARCHIVE
#                   exact delegate archives the Yices build consumes
#   KISSAT_NAMESPACE_SCRIPT
#                   exact script that produced the namespaced Kissat archive
#   MANUAL_PDF_FILE, MANUAL_PDF_SHA256
#                   rebuilt manual and its hash as computed by the host driver
#   MANUAL_BUILD_HOST_OS, MANUAL_LATEXMK_VERSION, MANUAL_PDFLATEX_VERSION
#                   host documentation-toolchain identity
#   MACOS_SDK_VERSION
#                   required on macOS and checked against the active SDK
#
# Produces, under <output-directory>:
#
#   PROVENANCE                 key/value metadata, feeds BUILDINFO
#   SHA256SUMS                 checksums of everything captured
#   glibc/                     glibc source package, distribution patches included
#   gmp/                       GMP source tarball
#   libpoly/                   the canonical pre-build LibPoly source tarball
#   cudd/, cadical/            canonical pre-build source tarballs
#   cryptominisat/, kissat/    canonical pre-build source tarballs
#   build-receipts/            exact dependency-build receipts
#   RELEASE-INPUTS*            the canonical manifest and its checksum file
#
# Exit status is nonzero if any required capture fails. A partial capture is
# worse than an obvious failure, because it looks complete.

set -eu

if [ $# -lt 1 ]; then
    echo "usage: $0 <output-directory>" >&2
    exit 2
fi

destination=$1

note() { echo "capture: $*"; }
fail() { echo "capture: ERROR: $*" >&2; exit 1; }
sha256_file() {
    _sha256_input=$1
    if command -v sha256sum >/dev/null 2>&1; then
        _sha256_line=$(sha256sum "$_sha256_input") || return $?
    elif command -v shasum >/dev/null 2>&1; then
        _sha256_line=$(shasum -a 256 "$_sha256_input") || return $?
    else
        fail "need sha256sum or shasum on PATH"
    fi
    _sha256_value=${_sha256_line%% *}
    case "$_sha256_value" in
        "" | *[!0-9a-f]*) return 1 ;;
    esac
    [ "${#_sha256_value}" -eq 64 ] || return 1
    printf '%s\n' "$_sha256_value"
}
field() {
    _field_key=$1
    _field_file=$2
    _field_count=$(awk -F ': ' -v key="$_field_key" '$1 == key { n++ } END { print n + 0 }' "$_field_file")
    [ "$_field_count" -eq 1 ] ||
        fail "expected one $_field_key field in $_field_file; found $_field_count"
    _field_value=$(awk -F ': ' -v key="$_field_key" '$1 == key { sub(/^[^:]*: /, ""); print }' "$_field_file")
    [ -n "$_field_value" ] || fail "empty $_field_key field in $_field_file"
    printf '%s\n' "$_field_value"
}
validate_test_summary() {
    _test_label=$1
    _test_value=$2
    set -f
    # Intentional word splitting: the receipt format is exactly six
    # space-separated key=value fields, in this order.
    # shellcheck disable=SC2086
    set -- $_test_value
    set +f
    [ "$#" -eq 6 ] ||
        fail "$_test_label test summary has the wrong field count: $_test_value"
    _test_total=${1#total=}
    _test_pass=${2#pass=}
    _test_skip=${3#skip=}
    _test_xfail=${4#xfail=}
    _test_fail=${5#fail=}
    _test_xpass=${6#xpass=}
    [ "$1" = "total=$_test_total" ] &&
        [ "$2" = "pass=$_test_pass" ] &&
        [ "$3" = "skip=$_test_skip" ] &&
        [ "$4" = "xfail=$_test_xfail" ] &&
        [ "$5" = "fail=$_test_fail" ] &&
        [ "$6" = "xpass=$_test_xpass" ] ||
        fail "$_test_label test summary has the wrong format: $_test_value"
    for _test_number in "$_test_total" "$_test_pass" "$_test_skip" \
        "$_test_xfail" "$_test_fail" "$_test_xpass"; do
        case "$_test_number" in
            0|[1-9]|[1-9][0-9]*) ;;
            *) fail "$_test_label test summary has an invalid count: $_test_value" ;;
        esac
    done
    [ "$_test_total" -gt 0 ] ||
        fail "$_test_label test summary is empty"
    [ "$_test_total" -eq "$((_test_pass + _test_skip + _test_xfail + _test_fail + _test_xpass))" ] ||
        fail "$_test_label test counts do not sum to total: $_test_value"
    [ "$_test_fail" -eq 0 ] && [ "$_test_xpass" -eq 0 ] ||
        fail "$_test_label tests did not pass cleanly: $_test_value"
}
validate_compiler_version() {
    _compiler_label=$1
    _compiler_command=$2
    _compiler_recorded=$3
    _compiler_lower=$(printf "%s\n" "$_compiler_recorded" | tr "[:upper:]" "[:lower:]")
    case "$_compiler_lower" in
        *fixture*|*placeholder*|*generated*|*unknown*|*unavailable*|*not-recorded*)
            fail "$_compiler_label version is a sentinel, not tool output: $_compiler_recorded"
            ;;
    esac
    command -v "$_compiler_command" >/dev/null 2>&1 ||
        fail "$_compiler_label command is not on PATH: $_compiler_command"
    _compiler_live=$("$_compiler_command" --version 2>/dev/null | head -1)
    [ -n "$_compiler_live" ] ||
        fail "cannot read $_compiler_label version from $_compiler_command"
    [ "$_compiler_recorded" = "$_compiler_live" ] ||
        fail "$_compiler_label version differs from live tool output: receipt=$_compiler_recorded live=$_compiler_live"
}
reject_sentinel() {
    _sentinel_label=$1
    _sentinel_value=$2
    _sentinel_lower=$(printf '%s\n' "$_sentinel_value" | tr '[:upper:]' '[:lower:]')
    case "$_sentinel_lower" in
        *fixture*|*placeholder*|*generated*|*unknown*|*unavailable*|*not-recorded*)
            fail "$_sentinel_label is a sentinel, not factual output: $_sentinel_value"
            ;;
    esac
}
verify_libpoly_header_manifest() {
    _header_root=$1
    _header_receipt=$2
    [ -d "$_header_root" ] && [ ! -L "$_header_root" ] ||
        fail "LibPoly header root is missing, not a directory, or a symlink: $_header_root"
    [ "$(field libpoly-header-root "$_header_receipt")" = poly ] ||
        fail "LibPoly receipt names the wrong header root"
    [ -z "$(find "$_header_root" -type l -print -quit)" ] ||
        fail "LibPoly header root contains a symlink: $_header_root"
    [ -z "$(find "$_header_root" ! -type d ! -type f -print -quit)" ] ||
        fail "LibPoly header root contains a non-regular entry: $_header_root"
    [ -z "$(find "$_header_root" -name '*[[:space:]]*' -print -quit)" ] ||
        fail "LibPoly header root contains a path with whitespace: $_header_root"

    header_manifest_work=$(mktemp -d "$parent/.${base}.libpoly-headers.XXXXXX") ||
        fail "cannot create a LibPoly header-manifest staging directory"
    _header_expected=$header_manifest_work/expected
    _header_actual=$header_manifest_work/actual
    awk -F ': ' '$1 == "libpoly-header" { sub(/^[^:]*: /, ""); print }' \
        "$_header_receipt" > "$_header_expected" ||
        fail "cannot extract the LibPoly header manifest from its receipt"
    _header_count=$(field libpoly-header-count "$_header_receipt")
    case "$_header_count" in
        [1-9]|[1-9][0-9]*) ;;
        *) fail "LibPoly receipt has an invalid header count: $_header_count" ;;
    esac
    [ "$(awk 'END { print NR + 0 }' "$_header_expected")" -eq "$_header_count" ] ||
        fail "LibPoly receipt header count differs from its embedded manifest"
    _header_manifest_sha=$(sha256_file "$_header_expected") ||
        fail "cannot hash the embedded LibPoly header manifest"
    [ "$(field libpoly-header-manifest-sha256 "$_header_receipt")" = \
        "$_header_manifest_sha" ] ||
        fail "LibPoly embedded header manifest checksum differs from its receipt"

    : > "$_header_actual"
    (
        cd "$_header_root" || exit 1
        find . -type f -print | LC_ALL=C sort
    ) | while IFS= read -r _header_path; do
        _header_path=${_header_path#./}
        case "$_header_path" in
            ""|/*|./*|../*|*/../*|*//*|*[![:print:]]*|*[[:space:]]*)
                fail "unsafe LibPoly header path: $_header_path"
                ;;
        esac
        _header_file=$_header_root/$_header_path
        [ -f "$_header_file" ] && [ ! -L "$_header_file" ] ||
            fail "LibPoly header is missing, non-regular, or a symlink: $_header_path"
        _header_sha=$(sha256_file "$_header_file") ||
            fail "cannot hash LibPoly header: $_header_path"
        printf '%s  %s\n' "$_header_sha" "$_header_path" >> "$_header_actual" ||
            fail "cannot write the actual LibPoly header manifest"
    done || fail "cannot enumerate the LibPoly header tree"
    cmp -s "$_header_expected" "$_header_actual" ||
        fail "LibPoly header tree differs from its embedded path/hash manifest"
    rm -rf -- "$header_manifest_work"
    header_manifest_work=
}

parent=$(dirname -- "$destination")
base=$(basename -- "$destination")
case "$base" in
    "" | . | ..) fail "unsafe output directory: $destination" ;;
esac
mkdir -p "$parent"
parent=$(CDPATH= cd -- "$parent" && pwd)
destination=$parent/$base
[ ! -e "$destination" ] && [ ! -L "$destination" ] ||
    fail "output directory already exists: $destination"
out=$(mktemp -d "$parent/.${base}.tmp.XXXXXX") ||
    fail "cannot create a staging directory beside $destination"
chmod 755 "$out" || fail "cannot make the staging directory readable"
cleanup() {
    [ -z "${manifest_list:-}" ] || rm -f -- "$manifest_list"
    [ -z "${header_manifest_work:-}" ] || rm -rf -- "$header_manifest_work"
    [ -z "${out:-}" ] || rm -rf -- "$out"
    [ -z "${publishing:-}" ] || rm -rf -- "$publishing"
}
trap cleanup 0 1 2 15

prov=$out/PROVENANCE
: > "$prov"
emit() { printf '%s: %s\n' "$1" "$2" >> "$prov"; }
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
AR=${AR:-ar}
LD=${LD:-ld}
cc_version=$($CC --version 2>/dev/null | head -1)
[ -n "$cc_version" ] ||
    fail "cannot read the Yices C compiler version from $CC"
LIBPOLY_REPO=${LIBPOLY_REPO:-https://github.com/SRI-CSL/libpoly.git}
LIBPOLY_COMMIT=${LIBPOLY_COMMIT:-c342ff1ad2f0cbcfc866b1ef024003ccc001add2}
GMP_VERSION=${GMP_VERSION:-6.3.0}
GMP_SHA256=${GMP_SHA256:-a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898}

[ -n "${GMP_SOURCE_ARCHIVE:-}" ] && [ -f "$GMP_SOURCE_ARCHIVE" ] &&
    [ ! -L "$GMP_SOURCE_ARCHIVE" ] ||
    fail "GMP_SOURCE_ARCHIVE is required and must be a regular file"
[ "$(basename -- "$GMP_SOURCE_ARCHIVE")" = "gmp-${GMP_VERSION}.tar.xz" ] ||
    fail "GMP_SOURCE_ARCHIVE has the wrong filename: $GMP_SOURCE_ARCHIVE"
gmp_source_sha=$(sha256_file "$GMP_SOURCE_ARCHIVE") ||
    fail "cannot hash GMP_SOURCE_ARCHIVE: $GMP_SOURCE_ARCHIVE"
[ "$gmp_source_sha" = "$GMP_SHA256" ] ||
    fail "GMP source checksum mismatch: got $gmp_source_sha expected $GMP_SHA256"

[ -n "${GMP_SOURCE_RECEIPT:-}" ] && [ -f "$GMP_SOURCE_RECEIPT" ] &&
    [ ! -L "$GMP_SOURCE_RECEIPT" ] ||
    fail "GMP_SOURCE_RECEIPT is required and must be a regular file"
[ -n "${GMP_STATIC_ARCHIVE:-}" ] && [ -f "$GMP_STATIC_ARCHIVE" ] &&
    [ ! -L "$GMP_STATIC_ARCHIVE" ] ||
    fail "GMP_STATIC_ARCHIVE is required and must be a regular file"
[ -n "${GMP_PIC_ARCHIVE:-}" ] && [ -f "$GMP_PIC_ARCHIVE" ] &&
    [ ! -L "$GMP_PIC_ARCHIVE" ] ||
    fail "GMP_PIC_ARCHIVE is required and must be a regular file"
[ -n "${GMP_NORMAL_HEADER:-}" ] && [ -f "$GMP_NORMAL_HEADER" ] &&
    [ ! -L "$GMP_NORMAL_HEADER" ] ||
    fail "GMP_NORMAL_HEADER is required and must be a regular non-symlinked file"
[ -n "${GMP_PIC_HEADER:-}" ] && [ -f "$GMP_PIC_HEADER" ] &&
    [ ! -L "$GMP_PIC_HEADER" ] ||
    fail "GMP_PIC_HEADER is required and must be a regular non-symlinked file"
[ "$(field format "$GMP_SOURCE_RECEIPT")" = yices-gmp-build-receipt-v2 ] ||
    fail "unsupported GMP build receipt"
[ "$(field gmp-version "$GMP_SOURCE_RECEIPT")" = "$GMP_VERSION" ] ||
    fail "GMP build receipt names the wrong version"
[ "$(field gmp-source-file "$GMP_SOURCE_RECEIPT")" = "$(basename -- "$GMP_SOURCE_ARCHIVE")" ] ||
    fail "GMP build receipt names the wrong source archive"
[ "$(field gmp-source-sha256 "$GMP_SOURCE_RECEIPT")" = "$gmp_source_sha" ] ||
    fail "GMP build receipt names the wrong source checksum"
case "$platform" in
    Darwin) gmp_expected_platform=macos ;;
    *)      gmp_expected_platform=linux ;;
esac
gmp_build_platform=$(field gmp-build-platform "$GMP_SOURCE_RECEIPT")
gmp_build_arch=$(field gmp-build-arch "$GMP_SOURCE_RECEIPT")
gmp_deployment_target=$(field gmp-deployment-target "$GMP_SOURCE_RECEIPT")
gmp_cc=$(field gmp-cc "$GMP_SOURCE_RECEIPT")
gmp_cc_version=$(field gmp-cc-version "$GMP_SOURCE_RECEIPT")
gmp_cxx=$(field gmp-cxx "$GMP_SOURCE_RECEIPT")
gmp_cxx_version=$(field gmp-cxx-version "$GMP_SOURCE_RECEIPT")
[ "$gmp_build_platform" = "$gmp_expected_platform" ] ||
    fail "GMP build receipt platform is $gmp_build_platform; expected $gmp_expected_platform"
[ "$gmp_build_arch" = "$(uname -m)" ] ||
    fail "GMP build receipt architecture is $gmp_build_arch; expected $(uname -m)"
case "$gmp_expected_platform" in
    macos)
        [ "$gmp_deployment_target" = 11.0 ] ||
            fail "macOS GMP deployment target is $gmp_deployment_target; expected 11.0"
        [ "$gmp_cc" = clang ] && [ "$gmp_cxx" = clang++ ] ||
            fail "macOS GMP receipt names an unexpected compiler"
        ;;
    linux)
        [ "$gmp_deployment_target" = NOT-APPLICABLE ] ||
            fail "Linux GMP receipt must mark deployment target NOT-APPLICABLE"
        [ "$gmp_cc" = gcc ] && [ "$gmp_cxx" = g++ ] ||
            fail "Linux GMP receipt names an unexpected compiler"
        ;;
esac
validate_compiler_version "GMP C compiler" "$gmp_cc" "$gmp_cc_version"
validate_compiler_version "GMP C++ compiler" "$gmp_cxx" "$gmp_cxx_version"
[ "$(field gmp-static-file "$GMP_SOURCE_RECEIPT")" = "$(basename -- "$GMP_STATIC_ARCHIVE")" ] ||
    fail "GMP build receipt names the wrong static archive"
[ "$(field gmp-pic-file "$GMP_SOURCE_RECEIPT")" = "$(basename -- "$GMP_PIC_ARCHIVE")" ] ||
    fail "GMP build receipt names the wrong PIC archive"
gmp_static_sha=$(sha256_file "$GMP_STATIC_ARCHIVE") ||
    fail "cannot hash the configured static GMP archive"
gmp_pic_sha=$(sha256_file "$GMP_PIC_ARCHIVE") ||
    fail "cannot hash the configured PIC GMP archive"
[ "$(field gmp-static-sha256 "$GMP_SOURCE_RECEIPT")" = "$gmp_static_sha" ] ||
    fail "static GMP archive differs from its build receipt"
[ "$(field gmp-pic-sha256 "$GMP_SOURCE_RECEIPT")" = "$gmp_pic_sha" ] ||
    fail "PIC GMP archive differs from its build receipt"
[ "$(field gmp-normal-header-file "$GMP_SOURCE_RECEIPT")" = gmp.h ] &&
    [ "$(basename -- "$GMP_NORMAL_HEADER")" = gmp.h ] ||
    fail "GMP receipt or input names the wrong normal generated header"
[ "$(field gmp-pic-header-file "$GMP_SOURCE_RECEIPT")" = gmp.h ] &&
    [ "$(basename -- "$GMP_PIC_HEADER")" = gmp.h ] ||
    fail "GMP receipt or input names the wrong PIC generated header"
gmp_normal_header_sha=$(sha256_file "$GMP_NORMAL_HEADER") ||
    fail "cannot hash the normal generated GMP header"
gmp_pic_header_sha=$(sha256_file "$GMP_PIC_HEADER") ||
    fail "cannot hash the PIC generated GMP header"
[ "$(field gmp-normal-header-sha256 "$GMP_SOURCE_RECEIPT")" = \
    "$gmp_normal_header_sha" ] ||
    fail "normal generated GMP header differs from its build receipt"
[ "$(field gmp-pic-header-sha256 "$GMP_SOURCE_RECEIPT")" = \
    "$gmp_pic_header_sha" ] ||
    fail "PIC generated GMP header differs from its build receipt"
gmp_layout=$(field gmp-layout "$GMP_SOURCE_RECEIPT")
case "$gmp_layout" in
    "separate normal and PIC archives")
        [ "$gmp_static_sha" != "$gmp_pic_sha" ] ||
            fail "separate GMP archives unexpectedly have the same checksum"
        ;;
    "one fat PIC archive for both payloads")
        [ "$gmp_static_sha" = "$gmp_pic_sha" ] ||
            fail "single-archive GMP receipt names different archive checksums"
        ;;
    *) fail "unsupported GMP archive layout: $gmp_layout" ;;
esac
gmp_normal_configure_args=$(field gmp-normal-configure-args "$GMP_SOURCE_RECEIPT")
gmp_normal_cflags=$(field gmp-normal-cflags "$GMP_SOURCE_RECEIPT")
gmp_normal_cxxflags=$(field gmp-normal-cxxflags "$GMP_SOURCE_RECEIPT")
gmp_normal_tests=$(field gmp-normal-tests "$GMP_SOURCE_RECEIPT")
gmp_pic_configure_args=$(field gmp-pic-configure-args "$GMP_SOURCE_RECEIPT")
gmp_pic_cflags=$(field gmp-pic-cflags "$GMP_SOURCE_RECEIPT")
gmp_pic_cxxflags=$(field gmp-pic-cxxflags "$GMP_SOURCE_RECEIPT")
gmp_pic_tests=$(field gmp-pic-tests "$GMP_SOURCE_RECEIPT")
validate_test_summary "GMP normal" "$gmp_normal_tests"
validate_test_summary "GMP PIC" "$gmp_pic_tests"

[ -n "${RELEASE_INPUTS_DIR:-}" ] ||
    fail "RELEASE_INPUTS_DIR is required; every platform must consume the canonical pre-build input"
release_inputs_dir=$(CDPATH= cd -- "$RELEASE_INPUTS_DIR" && pwd) ||
    fail "RELEASE_INPUTS_DIR is not accessible: $RELEASE_INPUTS_DIR"
release_inputs_manifest=$release_inputs_dir/RELEASE-INPUTS
release_inputs_checksums=$release_inputs_dir/RELEASE-INPUTS.sha256
[ -f "$release_inputs_manifest" ] && [ ! -L "$release_inputs_manifest" ] ||
    fail "canonical release-input manifest is missing or a symlink: $release_inputs_manifest"
[ -f "$release_inputs_checksums" ] && [ ! -L "$release_inputs_checksums" ] ||
    fail "canonical release-input checksum file is missing or a symlink: $release_inputs_checksums"

release_inputs_sha=$(sha256_file "$release_inputs_manifest") ||
    fail "cannot hash canonical release-input manifest"
expected_release_inputs_sha=12296dbf6cc3f924a91553259c95ee83682db5eca6a81cab2d9b00d820038bd8
[ "$(field format "$release_inputs_manifest")" = yices-release-inputs-v2 ] ||
    fail "unsupported release-input format; expected yices-release-inputs-v2"
[ "$release_inputs_sha" = "$expected_release_inputs_sha" ] ||
    fail "canonical release-input manifest differs from the release lock: $release_inputs_sha"
[ "$(field gmp-version "$release_inputs_manifest")" = "$GMP_VERSION" ] ||
    fail "canonical manifest names the wrong GMP version"
[ "$(field gmp-source-file "$release_inputs_manifest")" = "$(basename -- "$GMP_SOURCE_ARCHIVE")" ] ||
    fail "canonical manifest names the wrong GMP source archive"
[ "$(field gmp-source-sha256 "$release_inputs_manifest")" = "$gmp_source_sha" ] ||
    fail "canonical manifest names the wrong GMP source checksum"
[ "$(field cryptominisat-submodule-policy "$release_inputs_manifest")" = \
    "gitlinks-unexpanded; production-build-uses-none" ] ||
    fail "canonical CryptoMiniSat submodule policy differs from the release contract"

libpoly_repo=$(field libpoly-repo "$release_inputs_manifest")
libpoly_commit=$(field libpoly-commit "$release_inputs_manifest")
libpoly_tree=$(field libpoly-tree "$release_inputs_manifest")
libpoly_source_file=$(field libpoly-source-file "$release_inputs_manifest")
libpoly_source_sha=$(field libpoly-source-sha256 "$release_inputs_manifest")
cudd_repo=$(field cudd-repo "$release_inputs_manifest")
cudd_commit=$(field cudd-commit "$release_inputs_manifest")
cudd_tree=$(field cudd-tree "$release_inputs_manifest")
cudd_source_file=$(field cudd-source-file "$release_inputs_manifest")
cudd_source_sha=$(field cudd-source-sha256 "$release_inputs_manifest")
cadical_repo=$(field cadical-repo "$release_inputs_manifest")
cadical_commit=$(field cadical-commit "$release_inputs_manifest")
cadical_tree=$(field cadical-tree "$release_inputs_manifest")
cadical_source_file=$(field cadical-source-file "$release_inputs_manifest")
cadical_source_sha=$(field cadical-source-sha256 "$release_inputs_manifest")
cryptominisat_repo=$(field cryptominisat-repo "$release_inputs_manifest")
cryptominisat_commit=$(field cryptominisat-commit "$release_inputs_manifest")
cryptominisat_tree=$(field cryptominisat-tree "$release_inputs_manifest")
cryptominisat_source_file=$(field cryptominisat-source-file "$release_inputs_manifest")
cryptominisat_source_sha=$(field cryptominisat-source-sha256 "$release_inputs_manifest")
kissat_repo=$(field kissat-repo "$release_inputs_manifest")
kissat_commit=$(field kissat-commit "$release_inputs_manifest")
kissat_tree=$(field kissat-tree "$release_inputs_manifest")
kissat_source_file=$(field kissat-source-file "$release_inputs_manifest")
kissat_source_sha=$(field kissat-source-sha256 "$release_inputs_manifest")

[ "$libpoly_repo" = "$LIBPOLY_REPO" ] ||
    fail "canonical LibPoly repository differs from the release lock"
[ "$libpoly_commit" = "$LIBPOLY_COMMIT" ] ||
    fail "canonical LibPoly commit differs from the release lock"

validate_canonical_source() {
    _canonical_name=$1
    _canonical_file=$2
    _canonical_sha=$3
    case "$_canonical_file" in
        */*|.|..) fail "unsafe canonical $_canonical_name source filename: $_canonical_file" ;;
    esac
    _canonical_archive=$release_inputs_dir/$_canonical_file
    [ -s "$_canonical_archive" ] && [ -f "$_canonical_archive" ] &&
        [ ! -L "$_canonical_archive" ] ||
        fail "canonical $_canonical_name source archive is missing, empty, or a symlink: $_canonical_archive"
    _canonical_actual_sha=$(sha256_file "$_canonical_archive") ||
        fail "cannot hash canonical $_canonical_name source archive"
    [ "$_canonical_actual_sha" = "$_canonical_sha" ] ||
        fail "canonical $_canonical_name source archive does not match RELEASE-INPUTS"
    grep -F -x -- "$_canonical_sha  $_canonical_file" "$release_inputs_checksums" >/dev/null ||
        fail "canonical $_canonical_name source line is absent from RELEASE-INPUTS.sha256"
}

validate_canonical_source GMP "$(basename -- "$GMP_SOURCE_ARCHIVE")" "$gmp_source_sha"
validate_canonical_source LibPoly "$libpoly_source_file" "$libpoly_source_sha"
validate_canonical_source CUDD "$cudd_source_file" "$cudd_source_sha"
validate_canonical_source CaDiCaL "$cadical_source_file" "$cadical_source_sha"
validate_canonical_source CryptoMiniSat "$cryptominisat_source_file" "$cryptominisat_source_sha"
validate_canonical_source Kissat "$kissat_source_file" "$kissat_source_sha"

libpoly_source_archive=$release_inputs_dir/$libpoly_source_file
cudd_source_archive=$release_inputs_dir/$cudd_source_file
cadical_source_archive=$release_inputs_dir/$cadical_source_file
cryptominisat_source_archive=$release_inputs_dir/$cryptominisat_source_file
kissat_source_archive=$release_inputs_dir/$kissat_source_file

grep -F -x -- "$release_inputs_sha  RELEASE-INPUTS" "$release_inputs_checksums" >/dev/null ||
    fail "canonical manifest line is absent from RELEASE-INPUTS.sha256"
release_inputs_checksum_lines=$(awk 'END { print NR + 0 }' "$release_inputs_checksums")
[ "$release_inputs_checksum_lines" -eq 7 ] ||
    fail "RELEASE-INPUTS.sha256 must contain exactly six source archives and the manifest"

[ -n "${LIBPOLY_SOURCE_RECEIPT:-}" ] && [ -f "$LIBPOLY_SOURCE_RECEIPT" ] &&
    [ ! -L "$LIBPOLY_SOURCE_RECEIPT" ] ||
    fail "LIBPOLY_SOURCE_RECEIPT is required and must be a regular file"
[ -n "${LIBPOLY_STATIC_ARCHIVE:-}" ] && [ -f "$LIBPOLY_STATIC_ARCHIVE" ] &&
    [ ! -L "$LIBPOLY_STATIC_ARCHIVE" ] ||
    fail "LIBPOLY_STATIC_ARCHIVE is required and must be a regular file"
[ -n "${LIBPOLY_PIC_ARCHIVE:-}" ] && [ -f "$LIBPOLY_PIC_ARCHIVE" ] &&
    [ ! -L "$LIBPOLY_PIC_ARCHIVE" ] ||
    fail "LIBPOLY_PIC_ARCHIVE is required and must be a regular file"
[ -n "${LIBPOLY_HEADER_DIR:-}" ] && [ -d "$LIBPOLY_HEADER_DIR" ] &&
    [ ! -L "$LIBPOLY_HEADER_DIR" ] ||
    fail "LIBPOLY_HEADER_DIR is required and must be a regular non-symlinked directory"
[ "$(field format "$LIBPOLY_SOURCE_RECEIPT")" = yices-libpoly-build-receipt-v2 ] ||
    fail "unsupported LibPoly build receipt"
[ "$(field release-inputs-sha256 "$LIBPOLY_SOURCE_RECEIPT")" = "$release_inputs_sha" ] ||
    fail "LibPoly build receipt names a different release-input manifest"
for _key in libpoly-repo libpoly-commit libpoly-tree libpoly-source-file libpoly-source-sha256; do
    _receipt_value=$(field "$_key" "$LIBPOLY_SOURCE_RECEIPT")
    _manifest_value=$(field "$_key" "$release_inputs_manifest")
    [ "$_receipt_value" = "$_manifest_value" ] ||
        fail "LibPoly build receipt $_key differs from the canonical manifest"
done
[ "$(field libpoly-static-file "$LIBPOLY_SOURCE_RECEIPT")" = "$(basename "$LIBPOLY_STATIC_ARCHIVE")" ] ||
    fail "LibPoly build receipt names the wrong static archive"
[ "$(field libpoly-pic-file "$LIBPOLY_SOURCE_RECEIPT")" = "$(basename "$LIBPOLY_PIC_ARCHIVE")" ] ||
    fail "LibPoly build receipt names the wrong PIC archive"
libpoly_static_sha=$(sha256_file "$LIBPOLY_STATIC_ARCHIVE") ||
    fail "cannot hash the configured static LibPoly archive"
libpoly_pic_sha=$(sha256_file "$LIBPOLY_PIC_ARCHIVE") ||
    fail "cannot hash the configured PIC LibPoly archive"
[ "$(field libpoly-static-sha256 "$LIBPOLY_SOURCE_RECEIPT")" = "$libpoly_static_sha" ] ||
    fail "static LibPoly archive differs from its canonical-input build receipt"
[ "$(field libpoly-pic-sha256 "$LIBPOLY_SOURCE_RECEIPT")" = "$libpoly_pic_sha" ] ||
    fail "PIC LibPoly archive differs from its canonical-input build receipt"
[ "$(field libpoly-tests "$LIBPOLY_SOURCE_RECEIPT")" = \
    "ctest PASS; total=15 pass=15 fail=0" ] ||
    fail "LibPoly receipt does not record the parsed clean 15/15 test result"
verify_libpoly_header_manifest "$LIBPOLY_HEADER_DIR" "$LIBPOLY_SOURCE_RECEIPT"
libpoly_header_root=$(field libpoly-header-root "$LIBPOLY_SOURCE_RECEIPT")
libpoly_header_count=$(field libpoly-header-count "$LIBPOLY_SOURCE_RECEIPT")
libpoly_header_manifest_sha=$(field libpoly-header-manifest-sha256 "$LIBPOLY_SOURCE_RECEIPT")

[ -n "${DEPENDENCY_SOURCE_RECEIPT:-}" ] &&
    [ -s "$DEPENDENCY_SOURCE_RECEIPT" ] &&
    [ -f "$DEPENDENCY_SOURCE_RECEIPT" ] &&
    [ ! -L "$DEPENDENCY_SOURCE_RECEIPT" ] ||
    fail "DEPENDENCY_SOURCE_RECEIPT is required and must be a nonempty regular file"
[ -n "${DEPENDENCY_INCLUDE_DIR:-}" ] && [ -d "$DEPENDENCY_INCLUDE_DIR" ] ||
    fail "DEPENDENCY_INCLUDE_DIR is required and must be a directory"
for _dependency_archive in \
    "${CUDD_STATIC_ARCHIVE:-}" \
    "${CADICAL_STATIC_ARCHIVE:-}" \
    "${CRYPTOMINISAT_STATIC_ARCHIVE:-}" \
    "${KISSAT_RAW_ARCHIVE:-}" \
    "${KISSAT_NAMESPACED_ARCHIVE:-}" \
    "${KISSAT_NAMESPACE_SCRIPT:-}"; do
    [ -n "$_dependency_archive" ] &&
        [ -s "$_dependency_archive" ] &&
        [ -f "$_dependency_archive" ] &&
        [ ! -L "$_dependency_archive" ] ||
        fail "required dependency archive or namespace script is missing, empty, or a symlink: $_dependency_archive"
done

[ "$(field format "$DEPENDENCY_SOURCE_RECEIPT")" = yices-dependency-build-receipt-v1 ] ||
    fail "unsupported dependency build receipt"
[ "$(field release-inputs-file "$DEPENDENCY_SOURCE_RECEIPT")" = RELEASE-INPUTS ] ||
    fail "dependency build receipt names the wrong release-input manifest"
[ "$(field release-inputs-sha256 "$DEPENDENCY_SOURCE_RECEIPT")" = "$release_inputs_sha" ] ||
    fail "dependency build receipt names a different release-input manifest"

dependency_build_platform=$(field build-platform "$DEPENDENCY_SOURCE_RECEIPT")
dependency_build_arch=$(field build-arch "$DEPENDENCY_SOURCE_RECEIPT")
dependency_deployment_target=$(field deployment-target "$DEPENDENCY_SOURCE_RECEIPT")
dependency_cc=$(field cc "$DEPENDENCY_SOURCE_RECEIPT")
dependency_cc_version=$(field cc-version "$DEPENDENCY_SOURCE_RECEIPT")
dependency_cxx=$(field cxx "$DEPENDENCY_SOURCE_RECEIPT")
dependency_cxx_version=$(field cxx-version "$DEPENDENCY_SOURCE_RECEIPT")
dependency_ar_version=$(field ar-version "$DEPENDENCY_SOURCE_RECEIPT")
dependency_ar_command=$(field ar-command "$DEPENDENCY_SOURCE_RECEIPT")
dependency_cmake_version=$(field cmake-version "$DEPENDENCY_SOURCE_RECEIPT")
dependency_make_version=$(field make-version "$DEPENDENCY_SOURCE_RECEIPT")
dependency_ninja_version=$(field ninja-version "$DEPENDENCY_SOURCE_RECEIPT")
dependency_cflags=$(field cflags "$DEPENDENCY_SOURCE_RECEIPT")
dependency_cxxflags=$(field cxxflags "$DEPENDENCY_SOURCE_RECEIPT")

[ "$dependency_build_platform" = "$gmp_expected_platform" ] ||
    fail "dependency receipt platform is $dependency_build_platform; expected $gmp_expected_platform"
[ "$dependency_build_arch" = "$(uname -m)" ] ||
    fail "dependency receipt architecture is $dependency_build_arch; expected $(uname -m)"
[ "$dependency_deployment_target" = "$gmp_deployment_target" ] ||
    fail "dependency and GMP receipts name different deployment targets"
case "$dependency_build_platform" in
    macos)
        [ "$dependency_cc" = clang ] && [ "$dependency_cxx" = clang++ ] ||
            fail "macOS dependency receipt names an unexpected compiler"
        ;;
    linux)
        [ "$dependency_cc" = gcc ] && [ "$dependency_cxx" = g++ ] ||
            fail "Linux dependency receipt names an unexpected compiler"
        ;;
    *) fail "unsupported dependency receipt platform: $dependency_build_platform" ;;
esac
validate_compiler_version "dependency C compiler" "$dependency_cc" "$dependency_cc_version"
validate_compiler_version "dependency C++ compiler" "$dependency_cxx" "$dependency_cxx_version"
case "$dependency_build_platform" in
    macos)
        [ "$dependency_ar_command" = /usr/bin/ar ] ||
            fail "macOS dependency receipt does not pin /usr/bin/ar"
        if [ "$dependency_ar_version" != version-unavailable ]; then
            reject_sentinel "dependency ar version" "$dependency_ar_version"
        fi
        ;;
    linux)
        [ "$dependency_ar_command" = /opt/rh/gcc-toolset-14/root/usr/bin/ar ] ||
            fail "Linux dependency receipt does not pin the canonical GCC Toolset 14 ar"
        reject_sentinel "dependency ar version" "$dependency_ar_version"
        ;;
esac
for _dependency_tool in \
    "$dependency_cmake_version" \
    "$dependency_make_version" \
    "$dependency_ninja_version"; do
    reject_sentinel "dependency tool version" "$_dependency_tool"
done

for _dependency_component in cudd cadical cryptominisat kissat; do
    for _dependency_suffix in repo commit tree source-file source-sha256; do
        _dependency_key=$_dependency_component-$_dependency_suffix
        _dependency_receipt_value=$(field "$_dependency_key" "$DEPENDENCY_SOURCE_RECEIPT")
        _dependency_manifest_value=$(field "$_dependency_key" "$release_inputs_manifest")
        [ "$_dependency_receipt_value" = "$_dependency_manifest_value" ] ||
            fail "dependency receipt $_dependency_key differs from the canonical manifest"
    done
done

validate_dependency_archive() {
    _archive_key=$1
    _archive_expected_name=$2
    _archive_path=$3
    [ "$(basename -- "$_archive_path")" = "$_archive_expected_name" ] ||
        fail "$_archive_key archive argument has the wrong filename: $_archive_path"
    [ "$(field "$_archive_key-archive-file" "$DEPENDENCY_SOURCE_RECEIPT")" = \
        "$_archive_expected_name" ] ||
        fail "dependency receipt names the wrong $_archive_key archive"
    _archive_actual_sha=$(sha256_file "$_archive_path") ||
        fail "cannot hash $_archive_key archive"
    [ "$(field "$_archive_key-archive-sha256" "$DEPENDENCY_SOURCE_RECEIPT")" = \
        "$_archive_actual_sha" ] ||
        fail "$_archive_key archive differs from its dependency receipt"
}

validate_dependency_archive cudd libcudd.a "$CUDD_STATIC_ARCHIVE"
cudd_archive_sha=$_archive_actual_sha
validate_dependency_archive cadical libcadical.a "$CADICAL_STATIC_ARCHIVE"
cadical_archive_sha=$_archive_actual_sha
validate_dependency_archive cryptominisat libcryptominisat5.a "$CRYPTOMINISAT_STATIC_ARCHIVE"
cryptominisat_archive_sha=$_archive_actual_sha
validate_dependency_archive kissat-raw libkissat.a "$KISSAT_RAW_ARCHIVE"
kissat_raw_archive_sha=$_archive_actual_sha
validate_dependency_archive kissat-namespaced libkissat_yices.a "$KISSAT_NAMESPACED_ARCHIVE"
kissat_namespaced_archive_sha=$_archive_actual_sha
[ "$kissat_raw_archive_sha" != "$kissat_namespaced_archive_sha" ] ||
    fail "raw and namespaced Kissat archives unexpectedly have the same checksum"

validate_dependency_header() {
    _header_key=$1
    _header_expected_name=$2
    _header_path=$DEPENDENCY_INCLUDE_DIR/$_header_expected_name
    [ -s "$_header_path" ] && [ -f "$_header_path" ] && [ ! -L "$_header_path" ] ||
        fail "$_header_key header is missing, empty, or a symlink: $_header_path"
    [ "$(field "$_header_key-header-file" "$DEPENDENCY_SOURCE_RECEIPT")" = \
        "$_header_expected_name" ] ||
        fail "dependency receipt names the wrong $_header_key header"
    _header_actual_sha=$(sha256_file "$_header_path") ||
        fail "cannot hash $_header_key header"
    [ "$(field "$_header_key-header-sha256" "$DEPENDENCY_SOURCE_RECEIPT")" = \
        "$_header_actual_sha" ] ||
        fail "$_header_key header differs from its dependency receipt"
}

validate_dependency_header cudd cudd.h
cudd_header_sha=$_header_actual_sha
validate_dependency_header cadical ccadical.h
cadical_header_sha=$_header_actual_sha
validate_dependency_header cryptominisat cryptominisat5/cmsat_c.h
cryptominisat_header_sha=$_header_actual_sha
validate_dependency_header kissat kissat.h
kissat_header_sha=$_header_actual_sha

[ "$(field kissat-namespace-script-file "$DEPENDENCY_SOURCE_RECEIPT")" = \
    "$(basename -- "$KISSAT_NAMESPACE_SCRIPT")" ] ||
    fail "dependency receipt names the wrong Kissat namespace script"
kissat_namespace_script_sha=$(sha256_file "$KISSAT_NAMESPACE_SCRIPT") ||
    fail "cannot hash Kissat namespace script"
[ "$(field kissat-namespace-script-sha256 "$DEPENDENCY_SOURCE_RECEIPT")" = \
    "$kissat_namespace_script_sha" ] ||
    fail "Kissat namespace script differs from its dependency receipt"

cudd_configure_args=$(field cudd-configure-args "$DEPENDENCY_SOURCE_RECEIPT")
cudd_tests=$(field cudd-tests "$DEPENDENCY_SOURCE_RECEIPT")
cadical_configure_args=$(field cadical-configure-args "$DEPENDENCY_SOURCE_RECEIPT")
cadical_tests=$(field cadical-tests "$DEPENDENCY_SOURCE_RECEIPT")
cryptominisat_cmake_args=$(field cryptominisat-cmake-args "$DEPENDENCY_SOURCE_RECEIPT")
cryptominisat_tests=$(field cryptominisat-tests "$DEPENDENCY_SOURCE_RECEIPT")
kissat_configure_args=$(field kissat-configure-args "$DEPENDENCY_SOURCE_RECEIPT")
kissat_tests=$(field kissat-tests "$DEPENDENCY_SOURCE_RECEIPT")
[ "$cudd_configure_args" = "--disable-shared --enable-static --with-pic" ] ||
    fail "CUDD configure arguments differ from the release contract"
[ "$cryptominisat_cmake_args" = "-DONLY_SIMPLE=ON -DNOZLIB=ON -DNOM4RI=ON -DSTATS=OFF -DNOVALGRIND=ON -DENABLE_TESTING=OFF -DENABLE_PYTHON_INTERFACE=OFF -DBUILD_SHARED_LIBS=OFF -DCMAKE_DISABLE_FIND_PACKAGE_PythonInterp=ON -DCMAKE_DISABLE_FIND_PACKAGE_PythonLibs=ON" ] ||
    fail "CryptoMiniSat CMake arguments differ from the release contract"
for _dependency_test in \
    "$cudd_tests" \
    "$cadical_tests" \
    "$cryptominisat_tests" \
    "$kissat_tests"; do
    reject_sentinel "dependency test result" "$_dependency_test"
    case "$_dependency_test" in
        *PASS*) ;;
        *) fail "dependency test result does not record PASS: $_dependency_test" ;;
    esac
done

dependency_receipt_sha=$(sha256_file "$DEPENDENCY_SOURCE_RECEIPT") ||
    fail "cannot hash dependency build receipt"

# The production Make target supplies the library directory. A native macOS
# build may keep it beside the executables; Linux must supply YICES_LIB_DIR.
yices_lib_file=
if [ -n "${YICES_LIB_DIR:-}" ]; then
    find_yices_shared_library "$YICES_LIB_DIR"
elif [ "$platform" != Darwin ]; then
    fail "YICES_LIB_DIR is required on Linux"
fi

# ---------------------------------------------------------------------------
# 0. Build environment identity
# ---------------------------------------------------------------------------

note "recording build environment"

[ -n "${YICES_VERSION:-}" ] || fail "YICES_VERSION is required"
[ -n "${YICES_SOURCE_REVISION:-}" ] || fail "YICES_SOURCE_REVISION is required"
printf '%s\n' "$YICES_SOURCE_REVISION" | grep -Eq '^[0-9a-f]{40}$' ||
    fail "YICES_SOURCE_REVISION is not a full commit ID: $YICES_SOURCE_REVISION"
[ -n "${YICES_SOURCE_BRANCH:-}" ] || fail "YICES_SOURCE_BRANCH is required"
[ "$YICES_SOURCE_BRANCH" = "preparing-release-$YICES_VERSION" ] ||
    fail "YICES_SOURCE_BRANCH is not the release-preparation branch: $YICES_SOURCE_BRANCH"
[ -n "${YICES_TARGET_TRIPLE:-}" ] || fail "YICES_TARGET_TRIPLE is required"
[ "${YICES_BUILD_MODE:-}" = release ] ||
    fail "YICES_BUILD_MODE must be release: ${YICES_BUILD_MODE:-missing}"
[ "${YICES_THREAD_SAFE:-}" = no ] ||
    fail "YICES_THREAD_SAFE must be no for a published artifact: ${YICES_THREAD_SAFE:-missing}"
[ -n "${MANUAL_PDF_FILE:-}" ] && [ -f "$MANUAL_PDF_FILE" ] &&
    [ ! -L "$MANUAL_PDF_FILE" ] ||
    fail "MANUAL_PDF_FILE must name the rebuilt regular manual PDF"
[ -n "${MANUAL_PDF_SHA256:-}" ] || fail "MANUAL_PDF_SHA256 is required"
printf '%s\n' "$MANUAL_PDF_SHA256" | grep -Eq '^[0-9a-f]{64}$' ||
    fail "MANUAL_PDF_SHA256 is malformed: $MANUAL_PDF_SHA256"
manual_pdf_actual=$(sha256_file "$MANUAL_PDF_FILE") ||
    fail "cannot hash MANUAL_PDF_FILE: $MANUAL_PDF_FILE"
[ "$manual_pdf_actual" = "$MANUAL_PDF_SHA256" ] ||
    fail "MANUAL_PDF_FILE differs from MANUAL_PDF_SHA256"
for _manual_value in MANUAL_BUILD_HOST_OS MANUAL_LATEXMK_VERSION MANUAL_PDFLATEX_VERSION; do
    eval "_manual_text=\${$_manual_value:-}"
    [ -n "$_manual_text" ] || fail "$_manual_value is required"
done
if [ "$platform" = Darwin ]; then
    [ -n "${MACOS_SDK_VERSION:-}" ] || fail "MACOS_SDK_VERSION is required on macOS"
    active_sdk_version=$(xcrun --show-sdk-version 2>/dev/null) ||
        fail "cannot read the active macOS SDK version"
    [ "$active_sdk_version" = "$MACOS_SDK_VERSION" ] ||
        fail "MACOS_SDK_VERSION differs from the active SDK: $active_sdk_version"
else
    MACOS_SDK_VERSION="NOT-APPLICABLE, Linux build"
fi
command -v git >/dev/null 2>&1 || fail "git is required to verify Yices identity"
[ "$(git rev-parse --verify 'HEAD^{commit}' 2>/dev/null)" = "$YICES_SOURCE_REVISION" ] ||
    fail "YICES_SOURCE_REVISION differs from the checked-out commit"
[ "$(git rev-parse --abbrev-ref HEAD 2>/dev/null)" = "$YICES_SOURCE_BRANCH" ] ||
    fail "YICES_SOURCE_BRANCH differs from the checked-out branch"
[ -n "${YICES_BIN_DIR:-}" ] && [ -x "$YICES_BIN_DIR/yices" ] ||
    fail "YICES_BIN_DIR must contain the release yices executable"
yices_version_output=$($YICES_BIN_DIR/yices --version) ||
    fail "cannot execute the release yices binary"
printf '%s\n' "$yices_version_output" | grep -F -x -- "Yices $YICES_VERSION" >/dev/null ||
    fail "release yices binary reports the wrong version"
printf '%s\n' "$yices_version_output" |
    grep -F -x -- "Platform: $YICES_TARGET_TRIPLE ($YICES_BUILD_MODE/static)" >/dev/null ||
    fail "release yices binary reports the wrong target or mode"

emit yices-version         "$YICES_VERSION"
emit yices-commit          "$YICES_SOURCE_REVISION"
emit yices-branch          "$YICES_SOURCE_BRANCH"
emit target-triple         "$YICES_TARGET_TRIPLE"
emit yices-mode            "$YICES_BUILD_MODE"
emit thread-safe           "$YICES_THREAD_SAFE"
emit manual-pdf-sha256     "$MANUAL_PDF_SHA256"
emit manual-build-host-os  "$MANUAL_BUILD_HOST_OS"
emit manual-latexmk-version "$MANUAL_LATEXMK_VERSION"
emit manual-pdflatex-version "$MANUAL_PDFLATEX_VERSION"
emit sdk-version           "$MACOS_SDK_VERSION"

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

# A native Mac has no container identity. On Linux, the invoker supplies the
# derived image name and immutable local image ID plus its pinned base. The
# derived ID matters: the Dockerfile installs packages beyond the base image.
if [ "$platform" = Darwin ]; then
    emit builder-image        "NOT-APPLICABLE, native macOS build"
    emit builder-image-digest "NOT-APPLICABLE, native macOS build"
    emit builder-base-image   "NOT-APPLICABLE, native macOS build"
else
    [ -n "${BUILDER_IMAGE:-}" ] || fail "BUILDER_IMAGE is required on Linux"
    [ -n "${BUILDER_IMAGE_DIGEST:-}" ] || fail "BUILDER_IMAGE_DIGEST is required on Linux"
    [ -n "${BUILDER_BASE_IMAGE:-}" ] || fail "BUILDER_BASE_IMAGE is required on Linux"
    if [ "${#BUILDER_IMAGE_DIGEST}" -ne 71 ] ||
       ! printf "%s\n" "$BUILDER_IMAGE_DIGEST" |
           grep -Eq "^sha256:[0-9a-f]{64}$"; then
        fail "BUILDER_IMAGE_DIGEST is not a full sha256 image ID: $BUILDER_IMAGE_DIGEST"
    fi
    emit builder-image        "$BUILDER_IMAGE"
    emit builder-image-digest "$BUILDER_IMAGE_DIGEST"
    emit builder-base-image   "$BUILDER_BASE_IMAGE"
fi

emit cc "$CC"
if [ "$platform" = Darwin ]; then
    emit cc-version       "$cc_version"
    emit ld-version       "$("$LD" -v 2>&1 | head -1)"
    ar_version=$("$AR" -V 2>&1 | head -1)
    case "$ar_version" in
        "" | usage:* | Usage:* | ar:\ *) ar_version=version-unavailable ;;
    esac
    emit ar-version       "$ar_version"
    emit libc-runtime     "macOS libSystem (see macho-*-lc-load-dylib fields below)"
else
    # Keep the Linux fields byte-for-byte compatible with the original path.
    emit cc-version       "$cc_version"
    emit ld-version       "$("$LD" --version 2>/dev/null | head -1)"
    emit ar-version       "$("$AR" --version 2>/dev/null | head -1)"
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
        binary_sha=$(sha256_file "$binary") || fail "cannot hash $binary"
        emit "macho-$name-sha256" "$binary_sha"
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
libc_a_sha=$(sha256_file "$libc_a") || fail "cannot hash $libc_a"
emit glibc-archive-sha256 "$libc_a_sha"

mkdir -p "$out/glibc"

if command -v rpm >/dev/null 2>&1; then
    # ---- PRIMARY: RHEL family. This is the production path. ---------------
    #
    # Production builds use the pinned AlmaLinux 8-based image named by
    # BUILDER_BASE_IMAGE. glibc-static comes from PowerTools.
    #
    # The correspondence argument here is exact by construction rather than
    # by inference: the binary package NEVR and the source RPM NEVR are the
    # same NEVR, so the source we publish is the source the linked archive
    # was built from. That is asserted below and checked, not assumed.
    note "RPM-family builder (primary path)"
    emit packaging rpm

    # The derived image ID is the durable identity of this container build. A
    # tag or the base-image digest alone is insufficient because the
    # Dockerfile installs packages and tools beyond that base.
    if [ -z "${BUILDER_IMAGE_DIGEST:-}" ]; then
        fail "BUILDER_IMAGE_DIGEST is required on the rpm path.
       A tag does not identify the package set that produced these objects,
       because manylinux images are rebuilt under the same tag. Pass the
       full derived-image ID, for example:
         BUILDER_IMAGE_DIGEST=sha256:82f5f630...18e084 $0 $out"
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

    # The dependency build must pre-capture the exact signed source RPM. The
    # release provenance step is deliberately network-incapable: a missing
    # source input is a failed gate, never permission to fetch a substitute.
    [ -n "${GLIBC_SOURCE_FILE:-}" ] ||
        fail "GLIBC_SOURCE_FILE is required for the network-disabled release provenance step"
    [ -f "$GLIBC_SOURCE_FILE" ] && [ ! -L "$GLIBC_SOURCE_FILE" ] ||
        fail "GLIBC_SOURCE_FILE is not a regular file: $GLIBC_SOURCE_FILE"
    [ "$(basename "$GLIBC_SOURCE_FILE")" = "$srcrpm" ] ||
        fail "GLIBC_SOURCE_FILE does not match the linked package's SOURCERPM: $srcrpm"
    rpm -K "$GLIBC_SOURCE_FILE" 2>&1 | grep -q 'digests signatures OK' ||
        fail "GLIBC_SOURCE_FILE failed RPM signature verification"
    cp "$GLIBC_SOURCE_FILE" "$out/glibc/$srcrpm"
    emit glibc-source-method "pre-captured exact signed SOURCERPM"

    captured_glibc_source="$out/glibc/$srcrpm"
    [ -f "$captured_glibc_source" ] && [ ! -L "$captured_glibc_source" ] ||
        fail "captured glibc source RPM is missing or not a regular file: $captured_glibc_source"
    rpm -K "$captured_glibc_source" 2>&1 | grep -q 'digests signatures OK' ||
        fail "captured glibc source RPM failed signature verification: $captured_glibc_source"
    emit glibc-source-signature-verification "rpm -K: digests signatures OK"

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

    fail "Debian-family glibc source capture is not implemented offline.
       This release's production provenance path is the pinned RPM-family
       builder with an explicit GLIBC_SOURCE_FILE. Do not fetch during a
       provenance run or substitute an unverified source package."
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

if [ "$platform" != Darwin ]; then
    [ -n "${YICES_BIN_DIR:-}" ] && [ -d "$YICES_BIN_DIR" ] ||
        fail "YICES_BIN_DIR is required on Linux for the libxcrypt symbol gate"
fi

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
    fail "YICES_BIN_DIR is required for the libxcrypt symbol gate"
fi
fi

# ---------------------------------------------------------------------------
# 2. GMP
# ---------------------------------------------------------------------------

note "copying verified GMP $GMP_VERSION source"
mkdir -p "$out/gmp"
gmp_file=$out/gmp/gmp-${GMP_VERSION}.tar.xz
cp "$GMP_SOURCE_ARCHIVE" "$gmp_file" || fail "cannot copy GMP source archive"
got=$(sha256_file "$gmp_file") || fail "cannot hash copied GMP source archive"
[ "$got" = "$gmp_source_sha" ] || fail "GMP source changed while it was copied"

emit gmp-version               "$GMP_VERSION"
emit gmp-source-file           "$(basename "$gmp_file")"
emit gmp-source-sha256         "$got"
emit gmp-source-url            "$(field gmp-source-url "$release_inputs_manifest")"
emit gmp-build-platform        "$gmp_build_platform"
emit gmp-build-arch            "$gmp_build_arch"
emit gmp-deployment-target     "$gmp_deployment_target"
emit gmp-cc                    "$gmp_cc"
emit gmp-cc-version            "$gmp_cc_version"
emit gmp-cxx                   "$gmp_cxx"
emit gmp-cxx-version           "$gmp_cxx_version"
emit gmp-layout                "$gmp_layout"
emit gmp-normal-configure-args "$gmp_normal_configure_args"
emit gmp-normal-cflags         "$gmp_normal_cflags"
emit gmp-normal-cxxflags       "$gmp_normal_cxxflags"
emit gmp-normal-tests          "$gmp_normal_tests"
emit gmp-pic-configure-args    "$gmp_pic_configure_args"
emit gmp-pic-cflags            "$gmp_pic_cflags"
emit gmp-pic-cxxflags          "$gmp_pic_cxxflags"
emit gmp-pic-tests             "$gmp_pic_tests"
emit gmp-static-archive-sha256 "$gmp_static_sha"
emit gmp-pic-archive-sha256    "$gmp_pic_sha"
emit gmp-normal-header-file    "gmp.h"
emit gmp-normal-header-sha256  "$gmp_normal_header_sha"
emit gmp-pic-header-file       "gmp.h"
emit gmp-pic-header-sha256     "$gmp_pic_header_sha"
emit gmp-license-election      "LGPL-3.0-or-later"

# ---------------------------------------------------------------------------
# 3. Canonical source inputs and native dependency receipts
#
# Copy every pre-build canonical input. The checks above bind these exact
# source bytes to the exact archives and headers consumed by this platform
# build. Preserve the receipts themselves as evidence, not just fields
# transcribed from them.
# ---------------------------------------------------------------------------

copy_canonical_source() {
    _copy_name=$1
    _copy_repo=$2
    _copy_commit=$3
    _copy_tree=$4
    _copy_file=$5
    _copy_sha=$6
    _copy_source=$7
    _copy_directory=$out/$_copy_name
    note "copying verified canonical $_copy_name input $_copy_file"
    mkdir -p "$_copy_directory"
    cp "$_copy_source" "$_copy_directory/$_copy_file" ||
        fail "cannot copy canonical $_copy_name source archive"
    _copy_actual_sha=$(sha256_file "$_copy_directory/$_copy_file") ||
        fail "cannot hash copied canonical $_copy_name source archive"
    [ "$_copy_actual_sha" = "$_copy_sha" ] ||
        fail "canonical $_copy_name source changed while copied"
    emit "$_copy_name-repo" "$_copy_repo"
    emit "$_copy_name-commit" "$_copy_commit"
    emit "$_copy_name-tree" "$_copy_tree"
    emit "$_copy_name-source-file" "$_copy_file"
    emit "$_copy_name-source-sha256" "$_copy_sha"
}

copy_canonical_source libpoly "$libpoly_repo" "$libpoly_commit" \
    "$libpoly_tree" "$libpoly_source_file" "$libpoly_source_sha" \
    "$libpoly_source_archive"
copy_canonical_source cudd "$cudd_repo" "$cudd_commit" \
    "$cudd_tree" "$cudd_source_file" "$cudd_source_sha" \
    "$cudd_source_archive"
copy_canonical_source cadical "$cadical_repo" "$cadical_commit" \
    "$cadical_tree" "$cadical_source_file" "$cadical_source_sha" \
    "$cadical_source_archive"
copy_canonical_source cryptominisat "$cryptominisat_repo" \
    "$cryptominisat_commit" "$cryptominisat_tree" \
    "$cryptominisat_source_file" "$cryptominisat_source_sha" \
    "$cryptominisat_source_archive"
copy_canonical_source kissat "$kissat_repo" "$kissat_commit" \
    "$kissat_tree" "$kissat_source_file" "$kissat_source_sha" \
    "$kissat_source_archive"

cp "$release_inputs_manifest" "$out/RELEASE-INPUTS"
cp "$release_inputs_checksums" "$out/RELEASE-INPUTS.sha256"

emit libpoly-static-archive-sha256   "$libpoly_static_sha"
emit libpoly-pic-archive-sha256      "$libpoly_pic_sha"
emit libpoly-tests                   "ctest PASS; total=15 pass=15 fail=0"
emit libpoly-header-root             "$libpoly_header_root"
emit libpoly-header-count            "$libpoly_header_count"
emit libpoly-header-manifest-sha256  "$libpoly_header_manifest_sha"
awk -F ': ' '$1 == "libpoly-header" { sub(/^[^:]*: /, ""); print }' \
    "$LIBPOLY_SOURCE_RECEIPT" | while IFS= read -r _header_manifest_line; do
    emit libpoly-header "$_header_manifest_line"
done
emit cryptominisat-submodule-policy \
    "$(field cryptominisat-submodule-policy "$release_inputs_manifest")"
emit release-inputs-file           "RELEASE-INPUTS"
emit release-inputs-sha256         "$release_inputs_sha"

mkdir -p "$out/build-receipts"
cp "$GMP_SOURCE_RECEIPT" "$out/build-receipts/GMP-SOURCE-RECEIPT"
cp "$LIBPOLY_SOURCE_RECEIPT" "$out/build-receipts/LIBPOLY-SOURCE-RECEIPT"
cp "$DEPENDENCY_SOURCE_RECEIPT" \
    "$out/build-receipts/DEPENDENCY-SOURCE-RECEIPT"
gmp_receipt_sha=$(sha256_file "$GMP_SOURCE_RECEIPT") ||
    fail "cannot hash GMP build receipt"
libpoly_receipt_sha=$(sha256_file "$LIBPOLY_SOURCE_RECEIPT") ||
    fail "cannot hash LibPoly build receipt"
emit gmp-build-receipt-file "build-receipts/GMP-SOURCE-RECEIPT"
emit gmp-build-receipt-sha256 "$gmp_receipt_sha"
emit libpoly-build-receipt-file "build-receipts/LIBPOLY-SOURCE-RECEIPT"
emit libpoly-build-receipt-sha256 "$libpoly_receipt_sha"
emit dependency-build-receipt-file \
    "build-receipts/DEPENDENCY-SOURCE-RECEIPT"
emit dependency-build-receipt-sha256 "$dependency_receipt_sha"

emit dependency-build-platform "$dependency_build_platform"
emit dependency-build-arch "$dependency_build_arch"
emit dependency-deployment-target "$dependency_deployment_target"
emit dependency-cc "$dependency_cc"
emit dependency-cc-version "$dependency_cc_version"
emit dependency-cxx "$dependency_cxx"
emit dependency-cxx-version "$dependency_cxx_version"
emit dependency-ar-version "$dependency_ar_version"
emit dependency-ar-command "$dependency_ar_command"
emit dependency-cmake-version "$dependency_cmake_version"
emit dependency-make-version "$dependency_make_version"
emit dependency-ninja-version "$dependency_ninja_version"
emit dependency-cflags "$dependency_cflags"
emit dependency-cxxflags "$dependency_cxxflags"

emit cudd-configure-args "$cudd_configure_args"
emit cudd-tests "$cudd_tests"
emit cudd-archive-sha256 "$cudd_archive_sha"
emit cudd-header-sha256 "$cudd_header_sha"
emit cadical-configure-args "$cadical_configure_args"
emit cadical-tests "$cadical_tests"
emit cadical-archive-sha256 "$cadical_archive_sha"
emit cadical-header-sha256 "$cadical_header_sha"
emit cryptominisat-cmake-args "$cryptominisat_cmake_args"
emit cryptominisat-tests "$cryptominisat_tests"
emit cryptominisat-archive-sha256 "$cryptominisat_archive_sha"
emit cryptominisat-header-sha256 "$cryptominisat_header_sha"
emit kissat-configure-args "$kissat_configure_args"
emit kissat-tests "$kissat_tests"
emit kissat-raw-archive-sha256 "$kissat_raw_archive_sha"
emit kissat-namespaced-archive-sha256 "$kissat_namespaced_archive_sha"
emit kissat-header-sha256 "$kissat_header_sha"
emit kissat-namespace-script-file "$(basename -- "$KISSAT_NAMESPACE_SCRIPT")"
emit kissat-namespace-script-sha256 "$kissat_namespace_script_sha"

# ---------------------------------------------------------------------------
# 4. Checksums over everything captured
# ---------------------------------------------------------------------------

note "writing SHA256SUMS"
manifest_list=$(mktemp "$parent/.${base}.files.XXXXXX") ||
    fail "cannot create the checksum input list"
( cd "$out" && find . -type f ! -name SHA256SUMS -print | LC_ALL=C sort ) \
    > "$manifest_list" || fail "cannot enumerate captured files"
: > "$out/SHA256SUMS"
while IFS= read -r file; do
    file_sha=$(CDPATH= cd -- "$out" && sha256_file "$file") ||
        fail "cannot hash captured file: $file"
    printf '%s  %s\n' "$file_sha" "$file" >> "$out/SHA256SUMS" ||
        fail "cannot write SHA256SUMS"
done < "$manifest_list"
rm -f -- "$manifest_list"
manifest_list=

verify_manifest() {
    _verify_root=$1
    (
        cd "$_verify_root" || exit 1
        [ -s SHA256SUMS ] || exit 1
        _verify_count=0
        while IFS= read -r _verify_line; do
            _verify_expected=${_verify_line%%  *}
            _verify_file=${_verify_line#*  }
            [ "$_verify_line" = "$_verify_expected  $_verify_file" ] || exit 1
            case "$_verify_expected" in
                "" | *[!0-9a-f]*) exit 1 ;;
            esac
            [ "${#_verify_expected}" -eq 64 ] || exit 1
            case "$_verify_file" in
                ./*) ;;
                *) exit 1 ;;
            esac
            [ -f "$_verify_file" ] && [ ! -L "$_verify_file" ] || exit 1
            _verify_actual=$(sha256_file "$_verify_file") || exit 1
            [ "$_verify_actual" = "$_verify_expected" ] || exit 1
            _verify_count=$((_verify_count + 1))
        done < SHA256SUMS
        [ "$_verify_count" -gt 0 ]
    )
}
verify_manifest "$out" || fail "completed SHA256SUMS did not verify"

# mkdir is the portable no-clobber reservation primitive for a directory.
# CAPTURE-COMPLETE is written last, after the reserved copy verifies. A killed
# process can therefore leave only an obviously incomplete directory, never a
# partial tree that a caller is allowed to consume.
mkdir "$destination" || fail "cannot reserve output directory: $destination"
publishing=$destination
cp -R "$out"/. "$destination"/ || fail "cannot copy capture into reserved output directory"
verify_manifest "$destination" || fail "published SHA256SUMS did not verify"
manifest_sha=$(sha256_file "$destination/SHA256SUMS") ||
    fail "cannot hash published SHA256SUMS"
{
    printf 'format: yices-release-provenance-v1\n'
    printf 'sha256sums-sha256: %s\n' "$manifest_sha"
} > "$destination/CAPTURE-COMPLETE" || fail "cannot write completion marker"
[ -s "$destination/CAPTURE-COMPLETE" ] || fail "completion marker is empty"
rm -rf -- "$out"
out=
publishing=
trap - 0 1 2 15

note "done"
note "captured into $destination"
note ""
note "Reminder: the link commands and the archive hashes from the Yices build"
note "itself are recorded separately, into the relink kit's BUILDINFO. This"
note "script covers the dependency source side only."
