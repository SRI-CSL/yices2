#! /bin/sh
#
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
#

#
# Rewrite Kissat's private Kitten symbols for Yices static builds.

set -eu

usage() {
  echo "Usage: $0 --input libkissat.a --output libkissat_yices.a --rename-file renames.txt [--source-dir kissat-source]" >&2
  exit 2
}

input=
output=
rename_file=
source_dir=${KISSAT_SOURCE_DIR:-}

while [ $# -gt 0 ]; do
  case "$1" in
    --input)
      [ $# -gt 1 ] || usage
      input=$2
      shift 2
      ;;
    --output)
      [ $# -gt 1 ] || usage
      output=$2
      shift 2
      ;;
    --rename-file)
      [ $# -gt 1 ] || usage
      rename_file=$2
      shift 2
      ;;
    --source-dir)
      [ $# -gt 1 ] || usage
      source_dir=$2
      shift 2
      ;;
    --help|-h)
      usage
      ;;
    *)
      usage
      ;;
  esac
done

[ -n "$input" ] || usage
[ -n "$output" ] || usage
[ -n "$rename_file" ] || usage

if [ ! -f "$input" ]; then
  echo "rewrite-kissat-kitten-symbols: input archive not found: $input" >&2
  exit 1
fi

case "$input" in
  /*) input_abs=$input ;;
  *) input_abs=`pwd`/$input ;;
esac

case "$output" in
  /*) output_abs=$output ;;
  *) output_abs=`pwd`/$output ;;
esac

case "$rename_file" in
  /*) rename_abs=$rename_file ;;
  *) rename_abs=`pwd`/$rename_file ;;
esac

output_dir=`dirname "$output_abs"`
rename_dir=`dirname "$rename_abs"`

mkdir -p "$output_dir" "$rename_dir"

canonical_target() {
  canonical_parent=`dirname "$1"`
  canonical_leaf=`basename "$1"`
  canonical_parent=`cd -P "$canonical_parent" 2>/dev/null && pwd -P` || {
    echo "rewrite-kissat-kitten-symbols: cannot resolve path parent: $1" >&2
    exit 1
  }
  printf '%s/%s\n' "$canonical_parent" "$canonical_leaf"
}

assert_distinct() {
  alias_a_label=$1
  alias_a_path=$2
  alias_b_label=$3
  alias_b_path=$4
  if [ "$alias_a_path" = "$alias_b_path" ] ||
     { [ -e "$alias_a_path" ] && [ -e "$alias_b_path" ] &&
       [ "$alias_a_path" -ef "$alias_b_path" ]; }; then
    echo "rewrite-kissat-kitten-symbols: $alias_a_label aliases $alias_b_label" >&2
    exit 1
  fi
}

validate_output_target() {
  target_label=$1
  target_path=$2
  if [ -L "$target_path" ]; then
    echo "rewrite-kissat-kitten-symbols: refusing symlink $target_label: $target_path" >&2
    exit 1
  fi
  if [ -e "$target_path" ] && [ ! -f "$target_path" ]; then
    echo "rewrite-kissat-kitten-symbols: $target_label is not a regular file: $target_path" >&2
    exit 1
  fi
}

input_abs=`canonical_target "$input_abs"`
output_abs=`canonical_target "$output_abs"`
rename_abs=`canonical_target "$rename_abs"`
output_dir=`dirname "$output_abs"`
rename_dir=`dirname "$rename_abs"`
manifest=`canonical_target "$output_dir/manifest.txt"`

validate_output_target output "$output_abs"
validate_output_target rename-file "$rename_abs"
validate_output_target manifest "$manifest"
assert_distinct input "$input_abs" output "$output_abs"
assert_distinct input "$input_abs" rename-file "$rename_abs"
assert_distinct input "$input_abs" manifest "$manifest"
assert_distinct output "$output_abs" rename-file "$rename_abs"
assert_distinct output "$output_abs" manifest "$manifest"
assert_distinct rename-file "$rename_abs" manifest "$manifest"

command_exists() {
  command -v "$1" >/dev/null 2>&1
}

sha256_value() {
  if command_exists sha256sum; then
    hash_line=`sha256sum "$1"` || return 1
  elif command_exists shasum; then
    hash_line=`shasum -a 256 "$1"` || return 1
  else
    return 1
  fi
  hash_value=${hash_line%% *}
  case "$hash_value" in
    ''|*[!0-9a-f]*) return 1 ;;
  esac
  [ "${#hash_value}" -eq 64 ] || return 1
  printf '%s\n' "$hash_value"
}

classify_archive_members() {
  archive=$1
  all_members=$2
  object_members=$3
  index_members=$4

  "$AR" t "$archive" > "$all_members"
  : > "$object_members"
  : > "$index_members"
  while IFS= read -r member; do
    [ -n "$member" ] || continue
    case "$member" in
      "__.SYMDEF"|"__.SYMDEF SORTED"|"__.SYMDEF_64"|"__.SYMDEF SORTED_64")
        printf '%s\n' "$member" >> "$index_members"
        ;;
      *.o)
        printf '%s\n' "$member" >> "$object_members"
        ;;
      __.SYMDEF*)
        echo "rewrite-kissat-kitten-symbols: unrecognized archive index member: $member" >&2
        exit 1
        ;;
      *)
        echo "rewrite-kissat-kitten-symbols: unexpected non-object archive member: $member" >&2
        exit 1
        ;;
    esac
  done < "$all_members"
  if [ ! -s "$object_members" ]; then
    echo "rewrite-kissat-kitten-symbols: archive has no object members: $archive" >&2
    exit 1
  fi
}

NM=${NM:-nm}
AR=${AR:-ar}
RANLIB=${RANLIB:-ranlib}
MAKE=${MAKE:-make}

if ! command_exists "$NM"; then
  echo "rewrite-kissat-kitten-symbols: nm was not found" >&2
  exit 1
fi

tmp=`mktemp -d "${TMPDIR:-/tmp}/rewrite-kissat-kitten.XXXXXX"`
output_work=
rename_work=
manifest_work=
cleanup() {
  rm -rf "$tmp"
  [ -z "${output_work:-}" ] || rm -f "$output_work"
  [ -z "${rename_work:-}" ] || rm -f "$rename_work"
  [ -z "${manifest_work:-}" ] || rm -f "$manifest_work"
}
trap cleanup EXIT HUP INT TERM

output_work=`mktemp "$output_dir/.kissat-output.XXXXXX"`
rename_work=`mktemp "$rename_dir/.kissat-renames.XXXXXX"`
manifest_work=`mktemp "$output_dir/.kissat-manifest.XXXXXX"`

symbols=$tmp/symbols.txt
archive_members=$tmp/archive-members.txt
duplicates=$tmp/duplicate-members.txt
tool_error=$tmp/objcopy.err
nm_output=$tmp/output-nm.txt

"$NM" -g "$input_abs" |
  awk '
    {
      sym = $NF
      if (sym ~ /^kitten_/) {
        print sym " yices_kissat_" sym
      } else if (sym ~ /^_kitten_/) {
        print sym " _yices_kissat_" substr(sym, 2)
      } else if (sym == "new_learned_klause" || sym == "completely_backtrack_to_root_level") {
        print sym " yices_kissat_" sym
      } else if (sym == "_new_learned_klause" || sym == "_completely_backtrack_to_root_level") {
        print sym " _yices_kissat_" substr(sym, 2)
      }
    }
  ' |
  sort -u > "$symbols"

if [ ! -s "$symbols" ]; then
  echo "rewrite-kissat-kitten-symbols: no global Kitten symbols found in $input" >&2
  exit 1
fi

cp "$symbols" "$rename_work"

method=
tool_name=
tool_version=

if [ -n "$source_dir" ]; then
  case "$source_dir" in
    /*) source_abs=$source_dir ;;
    *) source_abs=`pwd`/$source_dir ;;
  esac
  if [ ! -f "$source_abs/build/makefile" ] ||
     [ ! -f "$source_abs/build/libkissat.a" ] ||
     [ ! -f "$source_abs/src/kissat.h" ]; then
    echo "rewrite-kissat-kitten-symbols: source mode requires the configured Kissat tree that built the raw archive" >&2
    exit 1
  fi
  if ! cmp -s "$input_abs" "$source_abs/build/libkissat.a"; then
    echo "rewrite-kissat-kitten-symbols: source tree's raw archive differs from --input" >&2
    exit 1
  fi
  if ! command_exists "$MAKE"; then
    echo "rewrite-kissat-kitten-symbols: source mode requires make" >&2
    exit 1
  fi
  if ! command_exists "$AR"; then
    echo "rewrite-kissat-kitten-symbols: source mode requires ar" >&2
    exit 1
  fi

  source_copy=$tmp/kissat-source
  cp -R "$source_abs" "$source_copy"
  namespace_header=$source_copy/kissat-yices-namespace.h
  {
    echo '#ifndef YICES_KISSAT_NAMESPACE_H'
    echo '#define YICES_KISSAT_NAMESPACE_H'
    awk '{
      old = $1
      new = $2
      sub(/^_/, "", old)
      sub(/^_/, "", new)
      print "#define " old " " new
    }' "$symbols"
    echo '#endif'
  } > "$namespace_header"

  cc_count=`grep -c '^CC=' "$source_copy/build/makefile" || true`
  if [ "$cc_count" -ne 1 ]; then
    echo "rewrite-kissat-kitten-symbols: configured Kissat makefile has $cc_count CC assignments" >&2
    exit 1
  fi
  configured_cc=`sed -n 's/^CC=//p' "$source_copy/build/makefile"`
  if [ -z "$configured_cc" ]; then
    echo "rewrite-kissat-kitten-symbols: configured Kissat compiler is empty" >&2
    exit 1
  fi
  compiler_command=`printf '%s\n' "$configured_cc" | awk '{print $1}'`
  if [ -z "$compiler_command" ] || ! command_exists "$compiler_command"; then
    echo "rewrite-kissat-kitten-symbols: configured Kissat compiler was not found: $compiler_command" >&2
    exit 1
  fi

  phony_build_header_count=`grep -c '^\.PHONY:.* build\.h$' "$source_copy/build/makefile" || true`
  if [ "$phony_build_header_count" -ne 1 ] || [ ! -f "$source_copy/build/build.h" ]; then
    echo "rewrite-kissat-kitten-symbols: could not preserve the raw archive's generated build.h" >&2
    exit 1
  fi
  sed 's/ build\.h$//' "$source_copy/build/makefile" > "$source_copy/build/makefile.namespaced"
  mv "$source_copy/build/makefile.namespaced" "$source_copy/build/makefile"

  rm -f "$source_copy"/build/*.o "$source_copy"/build/*.a \
    "$source_copy"/build/kissat "$source_copy"/build/tissat \
    "$source_copy"/build/kitten
  "$MAKE" -C "$source_copy/build" \
    CC="$configured_cc -include ../kissat-yices-namespace.h" \
    AR="$AR" libkissat.a
  cp "$source_copy/build/libkissat.a" "$output_work"

  classify_archive_members "$input_abs" "$tmp/raw-members.txt" \
    "$tmp/raw-object-members.txt" "$tmp/raw-index-members.txt"
  classify_archive_members "$output_work" "$tmp/namespaced-members.txt" \
    "$tmp/namespaced-object-members.txt" "$tmp/namespaced-index-members.txt"
  if ! cmp -s "$tmp/raw-members.txt" "$tmp/namespaced-members.txt"; then
    echo "rewrite-kissat-kitten-symbols: source build changed archive member names or order" >&2
    exit 1
  fi
  if ! cmp -s "$tmp/raw-index-members.txt" "$tmp/namespaced-index-members.txt"; then
    echo "rewrite-kissat-kitten-symbols: source build changed archive index layout" >&2
    exit 1
  fi
  sort "$tmp/raw-object-members.txt" | uniq -d > "$duplicates"
  if [ -s "$duplicates" ]; then
    echo "rewrite-kissat-kitten-symbols: source build verification cannot compare duplicate archive member names" >&2
    sed 's/^/  /' "$duplicates" >&2
    exit 1
  fi

  mkdir "$tmp/raw-objects" "$tmp/namespaced-objects"
  (cd "$tmp/raw-objects" && "$AR" x "$input_abs")
  (cd "$tmp/namespaced-objects" && "$AR" x "$output_work")
  while IFS= read -r member; do
    [ -n "$member" ] || continue
    if ! cmp -s "$tmp/raw-objects/$member" "$tmp/namespaced-objects/$member"; then
      {
        "$NM" -g "$tmp/raw-objects/$member"
        "$NM" -g "$tmp/namespaced-objects/$member"
      } | awk '{
        sym = $NF
        if (sym ~ /^_?kitten_/ ||
            sym ~ /^_?(new_learned_klause|completely_backtrack_to_root_level)$/ ||
            sym ~ /^_?yices_kissat_kitten_/ ||
            sym ~ /^_?yices_kissat_(new_learned_klause|completely_backtrack_to_root_level)$/)
          found = 1
      } END { exit found ? 0 : 1 }' || {
        echo "rewrite-kissat-kitten-symbols: archive member changed without a mapped private symbol: $member" >&2
        exit 1
      }
    fi
  done < "$tmp/raw-object-members.txt"

  "$NM" -g "$input_abs" |
    awk '{
      sym = $NF
      if (sym !~ /^_?[A-Za-z][A-Za-z0-9_]*$/) next
      if (sym ~ /^_?kitten_/) next
      if (sym ~ /^_?(new_learned_klause|completely_backtrack_to_root_level)$/) next
      print sym
    }' | sort -u > "$tmp/raw-public.txt"
  "$NM" -g "$output_work" |
    awk '{
      sym = $NF
      if (sym !~ /^_?[A-Za-z][A-Za-z0-9_]*$/) next
      if (sym ~ /^_?yices_kissat_kitten_/) next
      if (sym ~ /^_?yices_kissat_(new_learned_klause|completely_backtrack_to_root_level)$/) next
      print sym
    }' | sort -u > "$tmp/namespaced-public.txt"
  if ! cmp -s "$tmp/raw-public.txt" "$tmp/namespaced-public.txt"; then
    echo "rewrite-kissat-kitten-symbols: source build changed a non-private global symbol" >&2
    exit 1
  fi

  awk '{print $2}' "$symbols" | sort -u > "$tmp/expected-namespaced.txt"
  "$NM" -g "$output_work" |
    awk '{
      sym = $NF
      if (sym ~ /^_?yices_kissat_kitten_/ ||
          sym ~ /^_?yices_kissat_(new_learned_klause|completely_backtrack_to_root_level)$/)
        print sym
    }' | sort -u > "$tmp/actual-namespaced.txt"
  if ! cmp -s "$tmp/expected-namespaced.txt" "$tmp/actual-namespaced.txt"; then
    echo "rewrite-kissat-kitten-symbols: source build did not produce exactly the mapped private symbols" >&2
    exit 1
  fi

  method=source-compile
  tool_name=$configured_cc
  tool_version=`"$compiler_command" --version 2>&1 | sed -n '1p'`
else
  if [ "`uname -s 2>/dev/null || echo unknown`" = Darwin ]; then
    echo "rewrite-kissat-kitten-symbols: Mach-O requires --source-dir or KISSAT_SOURCE_DIR; binary objcopy rewriting is unsafe" >&2
    exit 1
  fi

  if [ "${OBJCOPY:-}" ]; then
    objcopy_tool=$OBJCOPY
  elif command_exists objcopy; then
    objcopy_tool=objcopy
  elif command_exists gobjcopy; then
    objcopy_tool=gobjcopy
  elif command_exists llvm-objcopy; then
    objcopy_tool=llvm-objcopy
  else
    echo "rewrite-kissat-kitten-symbols: neither objcopy nor llvm-objcopy was found" >&2
    exit 1
  fi

  if "$objcopy_tool" --redefine-syms "$rename_work" "$input_abs" "$output_work" 2>"$tool_error"; then
    :
  else
    if ! command_exists "$AR"; then
      echo "rewrite-kissat-kitten-symbols: archive rewrite failed and ar was not found" >&2
      cat "$tool_error" >&2
      exit 1
    fi

    "$AR" t "$input_abs" > "$archive_members"
    sort "$archive_members" | uniq -d > "$duplicates"
    if [ -s "$duplicates" ]; then
      echo "rewrite-kissat-kitten-symbols: archive rewrite failed and extraction fallback is unsafe" >&2
      echo "duplicate archive member names:" >&2
      sed 's/^/  /' "$duplicates" >&2
      cat "$tool_error" >&2
      exit 1
    fi

    mkdir -p "$tmp/extract" "$tmp/rewrite"
    (cd "$tmp/extract" && "$AR" x "$input_abs")

    while IFS= read -r member; do
      [ -n "$member" ] || continue
      "$objcopy_tool" --redefine-syms "$rename_work" \
        "$tmp/extract/$member" "$tmp/rewrite/$member"
    done < "$archive_members"

    members=`cat "$archive_members"`
    rm -f "$output_work"
    (cd "$tmp/rewrite" && "$AR" cr "$output_work" $members)
  fi
  method=binary-objcopy
  tool_name=$objcopy_tool
  tool_version=`$objcopy_tool --version 2>&1 | sed -n '1p'`
fi

if command_exists "$RANLIB"; then
  "$RANLIB" "$output_work" >/dev/null 2>&1 || true
fi

"$NM" -g "$output_work" > "$nm_output"

if ! awk '{ if ($NF ~ /^_?kissat_solve$/) found=1 } END { exit found ? 0 : 1 }' "$nm_output"; then
  echo "rewrite-kissat-kitten-symbols: rewritten archive is missing public symbol kissat_solve" >&2
  exit 1
fi

if ! awk '{ if ($NF ~ /^_?yices_kissat_kitten_/) found=1 } END { exit found ? 0 : 1 }' "$nm_output"; then
  echo "rewrite-kissat-kitten-symbols: rewritten archive has no yices_kissat_kitten_* symbols" >&2
  exit 1
fi

if awk '{ if ($NF ~ /^_?kitten_/) found=1 } END { exit found ? 0 : 1 }' "$nm_output"; then
  echo "rewrite-kissat-kitten-symbols: raw kitten_* symbols remain in rewritten archive" >&2
  awk '{ if ($NF ~ /^_?kitten_/) print "  " $0 }' "$nm_output" >&2
  exit 1
fi

if awk '{ if ($NF ~ /^_?(new_learned_klause|completely_backtrack_to_root_level)$/) found=1 } END { exit found ? 0 : 1 }' "$nm_output"; then
  echo "rewrite-kissat-kitten-symbols: raw Kitten helper symbols remain in rewritten archive" >&2
  awk '{ if ($NF ~ /^_?(new_learned_klause|completely_backtrack_to_root_level)$/) print "  " $0 }' "$nm_output" >&2
  exit 1
fi

input_sha=`sha256_value "$input_abs"` || {
  echo "rewrite-kissat-kitten-symbols: cannot hash input archive" >&2
  exit 1
}
output_sha=`sha256_value "$output_work"` || {
  echo "rewrite-kissat-kitten-symbols: cannot hash rewritten archive" >&2
  exit 1
}
{
  echo "input=$input_abs"
  echo "output=$output_abs"
  echo "rename_file=$rename_abs"
  echo "method=$method"
  echo "tool=$tool_name"
  echo "tool_version=$tool_version"
  if [ -n "$source_dir" ]; then
    echo "source_dir=$source_abs"
  fi
  printf '%s  %s\n' "$input_sha" "$input_abs"
  printf '%s  %s\n' "$output_sha" "$output_abs"
} > "$manifest_work"

# Recheck all targets immediately before publication. The archive is moved
# last, so a visible successful output always has both sidecars beside it.
validate_output_target output "$output_abs"
validate_output_target rename-file "$rename_abs"
validate_output_target manifest "$manifest"
assert_distinct input "$input_abs" output "$output_abs"
assert_distinct input "$input_abs" rename-file "$rename_abs"
assert_distinct input "$input_abs" manifest "$manifest"
assert_distinct output "$output_abs" rename-file "$rename_abs"
assert_distinct output "$output_abs" manifest "$manifest"
assert_distinct rename-file "$rename_abs" manifest "$manifest"

chmod 0644 "$output_work" "$rename_work" "$manifest_work"
mv -f "$rename_work" "$rename_abs"
rename_work=
mv -f "$manifest_work" "$manifest"
manifest_work=
mv -f "$output_work" "$output_abs"
output_work=

echo "Generated $output_abs"
