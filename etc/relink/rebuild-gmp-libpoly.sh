#!/usr/bin/env bash
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
# Recipient convenience recipe, not the production release builder.
set -euo pipefail
export LC_ALL=C
fail() { printf 'rebuild-gmp-libpoly: %s\n' "$*" >&2; exit 1; }
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
case $(uname -s):$(uname -m) in
  Linux:x86_64) normal_options=(--enable-fat --without-pic); normal_flags='-O2' ;;
  Darwin:x86_64) normal_options=(--enable-fat --with-pic); normal_flags='-O2 -fPIC'; export MACOSX_DEPLOYMENT_TARGET=11.0 ;;
  Darwin:arm64) normal_options=(--with-pic); normal_flags='-O2 -fPIC'; export MACOSX_DEPLOYMENT_TARGET=11.0 ;;
  *) fail 'recipe supports Linux x86_64 and native macOS x86_64/arm64 only' ;;
esac
mkdir -- "$work"
for variant in normal pic; do
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
  ) > "$work/gmp-$variant.log" 2>&1
done
cmake -S "$poly" -B "$work/libpoly-build" -G Ninja \
  -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX="$work/libpoly" \
  -DCMAKE_C_FLAGS=-O2 -DCMAKE_CXX_FLAGS=-O2 \
  -DGMP_INCLUDE_DIR="$work/gmp-pic/include" -DGMP_LIBRARY="$work/gmp-pic/lib/libgmp.a" \
  -DLIBPOLY_BUILD_PYTHON_API=OFF -DLIBPOLY_BUILD_STATIC=ON \
  -DLIBPOLY_BUILD_STATIC_PIC=ON -DBUILD_TESTING=ON > "$work/libpoly.log" 2>&1
cmake --build "$work/libpoly-build" --parallel "$jobs" >> "$work/libpoly.log" 2>&1
ctest --test-dir "$work/libpoly-build" --output-on-failure -j "$jobs" >> "$work/libpoly.log" 2>&1
cmake --install "$work/libpoly-build" >> "$work/libpoly.log" 2>&1
for archive in "$work"/gmp-{normal,pic}/lib/libgmp.a \
    "$work"/libpoly/lib/lib{poly,picpoly}.a; do
  [[ -s $archive ]] || fail "missing output: $archive"
done
printf 'PASS: recipient GMP and LibPoly builds/tests; prefixes and logs below %s\n' "$work"
