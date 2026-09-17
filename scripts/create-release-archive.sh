#!/bin/sh
#
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
#

# Create a gzip-compressed release archive without publishing the build
# account's uid, gid, user name, or group name in its headers.

set -eu

if [ "${1:-}" = --self-test ]; then
  [ "$#" -eq 1 ] || {
    echo "create-release-archive: --self-test takes no other arguments" >&2
    exit 2
  }
  self=$0
  case "$self" in
    /*) ;;
    *) self=`pwd`/$self ;;
  esac
  test_root=`mktemp -d "${TMPDIR:-/tmp}/create-release-archive-test.XXXXXX"`
  cleanup_self_test() {
    chmod -R u+w "$test_root" 2>/dev/null || true
    rm -rf "$test_root"
  }
  trap cleanup_self_test EXIT HUP INT TERM
  mkdir "$test_root/base"
  printf "%s\n" payload > "$test_root/base/member.txt"

  "$self" "$test_root/absent.tar.gz" "$test_root/base" member.txt
  [ -f "$test_root/absent.tar.gz" ] || exit 1
  "${TAR:-tar}" -tzf "$test_root/absent.tar.gz" | grep -x member.txt >/dev/null

  printf "%s\n" sentinel > "$test_root/existing.tar.gz"
  cp "$test_root/existing.tar.gz" "$test_root/existing.expected"
  chmod 0444 "$test_root/existing.tar.gz"
  if "$self" "$test_root/existing.tar.gz" "$test_root/base" member.txt; then
    echo "create-release-archive: self-test overwrote an existing file" >&2
    exit 1
  fi
  cmp -s "$test_root/existing.tar.gz" "$test_root/existing.expected" || exit 1

  printf "%s\n" symlink-target > "$test_root/symlink-target"
  cp "$test_root/symlink-target" "$test_root/symlink-target.expected"
  ln -s symlink-target "$test_root/symlink.tar.gz"
  if "$self" "$test_root/symlink.tar.gz" "$test_root/base" member.txt; then
    echo "create-release-archive: self-test replaced an existing symlink" >&2
    exit 1
  fi
  [ -L "$test_root/symlink.tar.gz" ] || exit 1
  cmp -s "$test_root/symlink-target" "$test_root/symlink-target.expected" || exit 1

  mkdir "$test_root/directory.tar.gz"
  if "$self" "$test_root/directory.tar.gz" "$test_root/base" member.txt; then
    echo "create-release-archive: self-test replaced an existing directory" >&2
    exit 1
  fi
  [ -d "$test_root/directory.tar.gz" ] || exit 1

  "$self" "$test_root/race.tar.gz" "$test_root/base" member.txt >/dev/null 2>&1 &
  first_pid=$!
  "$self" "$test_root/race.tar.gz" "$test_root/base" member.txt >/dev/null 2>&1 &
  second_pid=$!
  first_status=0
  second_status=0
  wait "$first_pid" || first_status=$?
  wait "$second_pid" || second_status=$?
  if [ "$first_status" -eq 0 ]; then
    [ "$second_status" -ne 0 ] || {
      echo "create-release-archive: self-test allowed two concurrent publishers" >&2
      exit 1
    }
  else
    [ "$second_status" -eq 0 ] || {
      echo "create-release-archive: self-test allowed no concurrent publisher" >&2
      exit 1
    }
  fi
  "${TAR:-tar}" -tzf "$test_root/race.tar.gz" | grep -x member.txt >/dev/null
  if find "$test_root" -name ".release-archive.*" -print | grep . >/dev/null; then
    echo "create-release-archive: self-test left a temporary archive" >&2
    exit 1
  fi

  cleanup_self_test
  trap - EXIT HUP INT TERM
  echo "create-release-archive self-test passed"
  exit 0
fi

usage() {
  echo "Usage: $0 OUTPUT.tar.gz BASE-DIRECTORY MEMBER [MEMBER ...]" >&2
  exit 2
}

[ $# -ge 3 ] || usage

output=$1
base=$2
shift 2

[ -d "$base" ] || {
  echo "create-release-archive: base directory not found: $base" >&2
  exit 1
}

case "$output" in
  /*) output_abs=$output ;;
  *) output_abs=`pwd`/$output ;;
esac

output_dir=`dirname "$output_abs"`
[ -d "$output_dir" ] || {
  echo "create-release-archive: output directory not found: $output_dir" >&2
  exit 1
}

TAR=${TAR:-tar}
tar_version=`"$TAR" --version 2>&1 | sed -n '1p'` || {
  echo "create-release-archive: cannot identify tar implementation: $TAR" >&2
  exit 1
}

temporary=`mktemp "$output_dir/.release-archive.XXXXXX"` || {
  echo "create-release-archive: cannot create a temporary sibling in $output_dir" >&2
  exit 1
}
cleanup() {
  rm -f "$temporary"
}
trap cleanup EXIT HUP INT TERM

case "$tar_version" in
  *bsdtar*)
    (cd "$base" && COPYFILE_DISABLE=1 "$TAR" \
      --uid 0 --gid 0 --uname root --gname root \
      -czf "$temporary" -- "$@")
    ;;
  *GNU\ tar*)
    (cd "$base" && COPYFILE_DISABLE=1 "$TAR" \
      --owner=0 --group=0 --numeric-owner \
      -czf "$temporary" -- "$@")
    ;;
  *)
    echo "create-release-archive: unsupported tar implementation: $tar_version" >&2
    exit 1
    ;;
esac

chmod 0644 "$temporary"
if ! command -v link >/dev/null 2>&1; then
  echo "create-release-archive: POSIX link utility was not found" >&2
  exit 1
fi
if ! link "$temporary" "$output_abs"; then
  echo "create-release-archive: output already exists or cannot be published: $output_abs" >&2
  exit 1
fi
rm -f "$temporary"
temporary=
trap - EXIT HUP INT TERM
