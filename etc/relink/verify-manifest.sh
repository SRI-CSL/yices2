#!/bin/sh
#
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
#
# Verify every immutable payload file in the Yices relink kit against
# MANIFEST.sha256. Files created by the documented relink procedure under
# ./relinked and regular .DS_Store metadata are not kit payload.
#
# Run this before relinking. The relink scripts call it automatically, but it
# is safe and useful to run on its own after downloading and extracting.
#
# Usage:  ./verify-manifest.sh [kit-directory]
#
# The kit directory defaults to the directory holding this script.

set -eu

kit=${1:-$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)}

if [ ! -f "$kit/MANIFEST.sha256" ] || [ -L "$kit/MANIFEST.sha256" ]; then
    echo "verify-manifest: MANIFEST.sha256 is missing or is not a regular file in $kit" >&2
    exit 1
fi

# Pick a checksum tool. Hash one file at a time after validating the manifest
# syntax, rather than relying on the tools' different check-mode parsers.
if command -v sha256sum >/dev/null 2>&1; then
    hash_file() { sha256sum "$1"; }
elif command -v shasum >/dev/null 2>&1; then
    hash_file() { shasum -a 256 "$1"; }
else
    echo "verify-manifest: need sha256sum or shasum on PATH" >&2
    exit 1
fi

echo "verify-manifest: checking $kit/MANIFEST.sha256"

fail() {
    echo "verify-manifest: $*" >&2
    exit 1
}

# The documented no-argument relink commands write beneath ./relinked. Keep
# that reserved output path out of the immutable-payload comparison, but do
# not let a symlink or another file type take its place.
if [ -e "$kit/relinked" ] || [ -L "$kit/relinked" ]; then
    [ -d "$kit/relinked" ] && [ ! -L "$kit/relinked" ] ||
        fail "reserved relink output path is not a real directory: ./relinked"
fi

manifest_names=$(mktemp "${TMPDIR:-/tmp}/yices-manifest-names.XXXXXX") ||
    fail "cannot create a temporary manifest list"
actual_names=$(mktemp "${TMPDIR:-/tmp}/yices-actual-names.XXXXXX") || {
    rm -f "$manifest_names"
    fail "cannot create a temporary file list"
}
trap 'rm -f "$manifest_names" "$actual_names"' 0 1 2 15

count=0
while IFS= read -r line || [ -n "$line" ]; do
    expected=${line%%  *}
    file=${line#*  }

    [ "$line" = "$expected  $file" ] ||
        fail "malformed MANIFEST.sha256 line: $line"
    [ "${#expected}" -eq 64 ] ||
        fail "malformed SHA-256 in MANIFEST.sha256: $expected"
    case "$expected" in
        *[!0-9a-f]*) fail "malformed SHA-256 in MANIFEST.sha256: $expected" ;;
    esac
    case "$file" in
        ./*) ;;
        *) fail "manifest path is not relative to the kit root: $file" ;;
    esac
    case "$file" in
        ./MANIFEST.sha256|*[[:space:]]*|*\\*)
            fail "unsafe manifest path: $file" ;;
    esac
    relative=${file#./}
    case "/$relative/" in
        */../*|*/./*|*//*) fail "unsafe manifest path: $file" ;;
    esac
    [ -f "$kit/$file" ] && [ ! -L "$kit/$file" ] ||
        fail "manifest path is missing or is not a regular file: $file"

    actual_line=$(hash_file "$kit/$file") ||
        fail "cannot hash manifest path: $file"
    actual=${actual_line%% *}
    [ "$actual" = "$expected" ] ||
        fail "checksum mismatch: $file"
    printf '%s\n' "$file" >> "$manifest_names"
    count=$((count + 1))
    printf '%s: OK\n' "$file"
done < "$kit/MANIFEST.sha256"

[ "$count" -gt 0 ] || fail "MANIFEST.sha256 is empty"
LC_ALL=C sort -o "$manifest_names" "$manifest_names"

# Reject special nodes everywhere. The Linux library relinker deliberately
# creates two symlinks under the reserved output directory; accept only those
# exact links and targets. A regular .DS_Store is harmless extraction
# metadata, but a link with that name is not.
unexpected_types=$(
    cd "$kit" &&
    find . ! -type d ! -type f ! -type l -print
)
[ -z "$unexpected_types" ] ||
    fail "kit contains an unexpected link or special node: $unexpected_types"

unexpected_links=$(
    cd "$kit" &&
    find . -type l \
        ! -path ./relinked/libyices.so \
        ! -path ./relinked/libyices.so.2.8 -print
)
[ -z "$unexpected_links" ] ||
    fail "kit contains an unexpected symbolic link: $unexpected_links"
if [ -L "$kit/relinked/libyices.so" ]; then
    [ "$(readlink "$kit/relinked/libyices.so")" = libyices.so.2.8 ] ||
        fail "reserved output link has an unsafe target: ./relinked/libyices.so"
fi
if [ -L "$kit/relinked/libyices.so.2.8" ]; then
    [ "$(readlink "$kit/relinked/libyices.so.2.8")" = libyices.so.2.8.0 ] ||
        fail "reserved output link has an unsafe target: ./relinked/libyices.so.2.8"
fi

( cd "$kit" &&
  find . -path ./relinked -prune -o \
      \( -type f -name .DS_Store \) -prune -o \
      -type f ! -path ./MANIFEST.sha256 -print | LC_ALL=C sort ) > "$actual_names"
cmp -s "$manifest_names" "$actual_names" ||
    fail "MANIFEST.sha256 does not enumerate every regular file exactly once"

echo "verify-manifest: all files match"
