#!/usr/bin/env bash
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
# Recipient convenience recipe, not the production release builder.
set -euo pipefail
export LC_ALL=C
fail() { printf 'rebuild-gmp-libpoly: %s\n' "$*" >&2; exit 1; }
active_phase='input and prerequisite checks'
active_log=
work_created=0
report_exit() {
  result=$?
  trap - EXIT
  if [[ $result -ne 0 ]]; then
    printf 'rebuild-gmp-libpoly: ERROR: %s failed (exit %s)\n' "$active_phase" "$result" >&2
    if [[ -n $active_log ]]; then
      printf 'rebuild-gmp-libpoly: inspect log: %s\n' "$active_log" >&2
    fi
    if [[ $work_created == 1 ]]; then
      printf 'rebuild-gmp-libpoly: partial workspace preserved: %s\n' "$work" >&2
    fi
  fi
  exit "$result"
}
trap report_exit EXIT
[[ $# -ge 3 && $# -le 4 ]] || fail 'usage: rebuild-gmp-libpoly.sh GMP-SOURCE LIBPOLY-SOURCE NEW-WORK-DIR [JOBS]'
gmp=$(cd -- "$1" && pwd -P)
poly=$(cd -- "$2" && pwd -P)
work=$3
jobs=${4:-2}
[[ $jobs =~ ^[1-9][0-9]*$ ]] || fail 'JOBS must be positive'
[[ -f $gmp/configure && -f $poly/CMakeLists.txt ]] || fail 'source directories are incomplete'
[[ ! -e $work && ! -L $work ]] || fail 'work directory already exists'
parent=$(cd -- "$(dirname -- "$work")" && pwd -P)
leaf=$(basename -- "$work")
[[ $leaf != . && $leaf != .. ]] || fail 'unsafe work directory'
work=$parent/$leaf
[[ $gmp != *[[:space:]]* && $poly != *[[:space:]]* && $work != *[[:space:]]* ]] ||
  fail 'these dependency build systems require paths without whitespace'
for tool in make cmake ctest ninja; do
  command -v "$tool" >/dev/null 2>&1 || fail "required tool is unavailable: $tool"
done
CC=${CC:-cc}
CXX=${CXX:-c++}
M4=${M4:-m4}
for tool in "$CC" "$CXX"; do
  command -v "$tool" >/dev/null 2>&1 || fail "required compiler is unavailable: $tool (CC/CXX must each name one executable)"
done
command -v "$M4" >/dev/null 2>&1 || fail "GNU m4 is required; executable unavailable: $M4 (set M4 to its path)"
m4_version=$("$M4" --version 2>&1) || fail "GNU m4 is required; $M4 --version failed"
[[ $m4_version == *'GNU M4'* ]] || fail "GNU m4 is required; $M4 did not identify GNU M4"
export CC CXX M4
case $(uname -s):$(uname -m) in
  Linux:x86_64) normal_options=(--enable-fat --without-pic); normal_flags='-O2' ;;
  Darwin:x86_64) normal_options=(--enable-fat --with-pic); normal_flags='-O2 -fPIC'; export MACOSX_DEPLOYMENT_TARGET=11.0 ;;
  Darwin:arm64) normal_options=(--with-pic); normal_flags='-O2 -fPIC'; export MACOSX_DEPLOYMENT_TARGET=11.0 ;;
  *) fail 'recipe supports Linux x86_64 and native macOS x86_64/arm64 only' ;;
esac
mkdir -- "$work"
work_created=1
for variant in normal pic; do
  active_phase="GMP $variant configure/build/check/install"
  active_log="$work/gmp-$variant.log"
  mkdir "$work/gmp-$variant-build"
  if [[ $variant == normal ]]; then
    options=("${normal_options[@]}"); flags=$normal_flags
  else
    options=(--disable-assembly --with-pic); flags='-O2 -fPIC'
  fi
  (
    cd "$work/gmp-$variant-build"
    "$gmp/configure" --prefix="$work/gmp-$variant" --disable-shared \
      --enable-static --enable-cxx "${options[@]}" CFLAGS="$flags" CXXFLAGS="$flags"
    make -j "$jobs"
    make -j "$jobs" check
    make install
  ) > "$active_log" 2>&1
done
active_phase='LibPoly configure'
active_log="$work/libpoly.log"
cmake -S "$poly" -B "$work/libpoly-build" -G Ninja \
  -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX="$work/libpoly" \
  -DCMAKE_C_FLAGS=-O2 -DCMAKE_CXX_FLAGS=-O2 \
  -DGMP_INCLUDE_DIR="$work/gmp-pic/include" -DGMP_LIBRARY="$work/gmp-pic/lib/libgmp.a" \
  -DLIBPOLY_BUILD_PYTHON_API=OFF -DLIBPOLY_BUILD_STATIC=ON \
  -DLIBPOLY_BUILD_STATIC_PIC=ON -DBUILD_TESTING=ON > "$active_log" 2>&1
active_phase='LibPoly build'
cmake --build "$work/libpoly-build" --parallel "$jobs" >> "$active_log" 2>&1
active_phase='LibPoly tests'
ctest --test-dir "$work/libpoly-build" --output-on-failure -j "$jobs" >> "$active_log" 2>&1
active_phase='LibPoly installation into the new private prefix'
cmake --install "$work/libpoly-build" >> "$active_log" 2>&1
active_phase='output archive verification'
active_log=
for archive in "$work"/gmp-{normal,pic}/lib/libgmp.a \
    "$work"/libpoly/lib/lib{poly,picpoly}.a; do
  [[ -s $archive ]] || fail "missing output: $archive"
done
printf 'PASS: recipient GMP and LibPoly builds/tests; prefixes and logs below %s\n' "$work"
