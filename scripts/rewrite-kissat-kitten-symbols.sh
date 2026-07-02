#! /bin/sh
#
# Rewrite Kissat's private Kitten symbols for Yices static builds.

set -eu

usage() {
  echo "Usage: $0 --input libkissat.a --output libkissat_yices.a --rename-file renames.txt" >&2
  exit 2
}

input=
output=
rename_file=

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

command_exists() {
  command -v "$1" >/dev/null 2>&1
}

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

NM=${NM:-nm}
AR=${AR:-ar}
RANLIB=${RANLIB:-ranlib}

if ! command_exists "$NM"; then
  echo "rewrite-kissat-kitten-symbols: nm was not found" >&2
  exit 1
fi

tmp=${TMPDIR:-/tmp}/rewrite-kissat-kitten-$$
rm -rf "$tmp"
mkdir -p "$tmp"
trap 'rm -rf "$tmp"' EXIT HUP INT TERM

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

cp "$symbols" "$rename_abs"
rm -f "$output_abs"

if "$objcopy_tool" --redefine-syms "$rename_abs" "$input_abs" "$output_abs" 2>"$tool_error"; then
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
    "$objcopy_tool" --redefine-syms "$rename_abs" \
      "$tmp/extract/$member" "$tmp/rewrite/$member"
  done < "$archive_members"

  members=`cat "$archive_members"`
  (cd "$tmp/rewrite" && "$AR" cr "$output_abs" $members)
fi

if command_exists "$RANLIB"; then
  "$RANLIB" "$output_abs" >/dev/null 2>&1 || true
fi

"$NM" -g "$output_abs" > "$nm_output"

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

manifest=$output_dir/manifest.txt
{
  echo "input=$input_abs"
  echo "output=$output_abs"
  echo "rename_file=$rename_abs"
  echo "tool=$objcopy_tool"
  echo "tool_version=`$objcopy_tool --version 2>&1 | sed -n '1p'`"
  if command_exists sha256sum; then
    sha256sum "$input_abs" "$output_abs"
  elif command_exists shasum; then
    shasum -a 256 "$input_abs" "$output_abs"
  fi
} > "$manifest"

echo "Generated $output_abs"
