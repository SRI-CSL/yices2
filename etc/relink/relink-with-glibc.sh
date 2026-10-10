#!/bin/sh
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
# Explicit static Linux link against a recipient's glibc build tree.
# The ordinary GCC runtime remains a stated toolchain prerequisite.
set -eu
fail() { echo "relink-with-glibc: $*" >&2; exit 1; }
[ "$#" -eq 2 ] || fail 'usage: relink-with-glibc.sh GLIBC-BUILD NEW-OUTPUT-DIRECTORY'
kit=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)
glibc=$(CDPATH= cd -- "$1" && pwd -P)
out=$2
[ ! -e "$out" ] && [ ! -L "$out" ] || fail 'output already exists'
parent=$(CDPATH= cd -- "$(dirname -- "$out")" && pwd -P)
leaf=$(basename -- "$out")
case "$leaf" in ''|.|..) fail 'unsafe output directory' ;; esac
out=$parent/$leaf
case "$out/" in "$kit/"*) fail 'use a new output directory outside the kit' ;; esac
case $(uname -s):$(uname -m) in Linux:x86_64) ;; *) fail 'Linux x86_64 only' ;; esac
CC=${CC:-gcc}
command -v "$CC" >/dev/null 2>&1 || fail 'CC must name a compatible GCC driver'
"$kit/verify-manifest.sh" "$kit"
for file in libc.a csu/crt1.o csu/crti.o csu/crtn.o math/libm.a nptl/libpthread.a; do
  [ -s "$glibc/$file" ] || fail "missing glibc build input: $file"
done
crtbegin=$("$CC" -print-file-name=crtbeginT.o)
crtend=$("$CC" -print-file-name=crtend.o)
libgcc=$("$CC" -print-libgcc-file-name)
libgcc_eh=$("$CC" -print-file-name=libgcc_eh.a)
libstdcxx=$("$CC" -print-file-name=libstdc++.a)
for file in "$crtbegin" "$crtend" "$libgcc" "$libgcc_eh" "$libstdcxx"; do
  [ -s "$file" ] || fail "missing GCC runtime input: $file"
done
GMP_A=${GMP_A:-$kit/deps/libgmp-static.a}
LIBPOLY_A=${LIBPOLY_A:-$kit/deps/libpoly.a}
mkdir -- "$out"
link() {
  name=$1; object=$2; shift 2
  # -nostdlib makes startup and C-library selection explicit. The linker map
  # records every input for recipient inspection. No system libc is selected.
  set -x
  "$CC" -static -no-pie -nostdlib -o "$out/$name" "-Wl,-Map=$out/$name.map" \
    "$glibc/csu/crt1.o" "$glibc/csu/crti.o" "$crtbegin" \
    "$kit/executables/$object" "$kit/executables/libyices.a" \
    "$kit/deps/libcudd.a" "$kit/deps/libcryptominisat5.a" \
    "$kit/deps/libcadical.a" "$kit/deps/libkissat_yices.a" "$@" \
    -Wl,--start-group "$libstdcxx" "$glibc/math/libm.a" \
    "$glibc/nptl/libpthread.a" "$glibc/libc.a" "$libgcc" "$libgcc_eh" \
    -Wl,--end-group "$crtend" "$glibc/csu/crtn.o"
  set +x
}
link yices yices.o "$LIBPOLY_A" "$GMP_A"
link yices-smt yices_smtcomp.o "$LIBPOLY_A" "$GMP_A"
link yices-smt2 yices_smt2.o "$LIBPOLY_A" "$GMP_A"
link yices-sat yices_sat.o
printf 'Relinked four executables using explicit glibc inputs; inspect %s/*.map and test before use.\n' "$out"
