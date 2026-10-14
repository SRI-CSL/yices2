#!/bin/bash

#
#  This file is part of the Yices SMT Solver.
#  Copyright (C) 2017 SRI International.
#
#  Yices is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 3 of the License, or
#  (at your option) any later version.
#
#  Yices is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with Yices.  If not, see <http://www.gnu.org/licenses/>.
#

#
# Run one single regression tests
#
# Usage: run_test.sh [-c] [-s <smt2-options>] [-x <tags>] <test-file> <bin-dir> [<out-dir>]
#
# test-file is the test file the SMT1, SMT2, or Yices input language
# bin-dir contains the Yices binaries for each of these languages
# tmp-dir (optional) and specifies the location to put the results
#
# An input is run once per option set, and each run counts as its own test. An
# option set is a file of command line options next to the input: file.options
# for the untagged one, file.<tag>.options for the one named <tag>. A variant of
# an existing input therefore needs a sidecar, not a copy of the input. An input
# with no option set at all is run once, untagged, with no options.
#
# Once an input has tags, its untagged run is the one named by file.options, so
# an empty file.options is meaningful: it keeps the plain run of an input that
# takes no options. Leaving it out drops that run, which is what regress/both
# does to be run under its two tags only.
#
# Each run is compared against file.<tag>.gold, falling back to file.gold when
# the tag has no gold of its own.
#
# The tests in regress/both use this for the two solver modes, under the tags
# mcsat and dpllt. -x disables tags, as in -x dpllt for an MCSAT-only run.
#

usage() {
  echo "Usage: $0 [-c] [-s <smt2-options>] [-x <tags>] <test-file> <bin-dir> [out-dir]"
  exit 4
}

smt2_options=
color=
disabled_tags=

while getopts "cs:x:" o; do
    case "$o" in
    s)
      smt2_options=${OPTARG}
      ;;
    x)
      disabled_tags=${OPTARG}
      ;;
    c)
      color="on"
      ;;
    *)
      usage
      ;;
    esac
done
shift $((OPTIND-1))

if [ $# -lt 2 ] ; then
  usage
fi

test_file=$1
bin_dir=$2

if [ $# -ge 3 ] ; then
  out_dir=$3
fi

# Tags may be given separated by commas or by spaces
disabled_tags=$(echo "$disabled_tags" | tr ',' ' ')

export LIBC_FATAL_STDERR_=1

#
# System-dependent configuration
#
os_name=$(uname 2>/dev/null) || os_name=unknown

case "$os_name" in
  *Darwin* )
     mktemp_cmd="/usr/bin/mktemp -t out"
  ;;

  * )
     mktemp_cmd=mktemp
  ;;

esac

#
# We try bash's builtin time command
#
TIMEFORMAT="%U"


#
# Output colors
#
red=
green=
black=
if [ -t 1 ] || [ -n "$color" ]; then
    red=$(tput setaf 1)
    green=$(tput setaf 2)
    black=$(tput sgr0)
fi

#
# The temp files for output, reused by every option set
#
outfile=$($mktemp_cmd) || { echo "Can't create temp file" ; exit 3 ; }
timefile=$($mktemp_cmd) || { echo "Can't create temp file" ; exit 3 ; }

cleanup() {
    rm -f "$timefile" "$outfile"
}
trap cleanup EXIT

if [[ -z "$TIME_LIMIT" ]];
then
    TIME_LIMIT=60
fi

# Get the binary based on the filename
filename=$(basename "$test_file")

base_options=

case $filename in
    *.smt2)
        binary=yices_smt2
        base_options=$smt2_options
        ;;
    *.smt)
        binary=yices_smtcomp
        ;;
    *.ys)
        binary=yices
        ;;
    *)
        echo "FAIL: unknown extension for $filename"
        exit 2
esac

run_solver_once() {
  local run_options=$1
  local run_outfile=$2
  local run_timefile=$3

  (
    ulimit -S -t $TIME_LIMIT &> /dev/null
    ulimit -H -t $((1+$TIME_LIMIT)) &> /dev/null
    (time "./$bin_dir/$binary" $run_options "./$test_file" >& "$run_outfile") >& "$run_timefile"
  )
}

# The tags that have an option set, one per <test-file>.<tag>.options. The
# pattern cannot match the untagged <test-file>.options, which has nothing
# between the input name and the suffix.
#
# A tag is one name, without a dot. Inputs come in families that share a prefix,
# such as fuzz17.smt2 and its reduction fuzz17.smt2.dd.smt2, and the options of
# the second must not read as a tag "dd.smt2" of the first. A candidate that is
# the options of an existing input is skipped for the same reason.
collect_tags() {
  local file
  local tag

  for file in "$test_file".*.options; do
    [ -e "$file" ] || continue
    tag=${file#"$test_file".}
    tag=${tag%.options}
    case "$tag" in
      ""|*.*)
        continue
        ;;
    esac
    if [ -e "$test_file.$tag" ] ; then
      continue
    fi
    echo "$tag"
  done
}

is_tag_disabled() {
  local tag=$1
  local disabled

  for disabled in $disabled_tags; do
    if [ "$disabled" = "$tag" ] ; then
      return 0
    fi
  done

  return 1
}

# The options file of a tag, the untagged one for an empty tag
options_file_of() {
  local tag=$1

  if [ -n "$tag" ] ; then
    echo "$test_file.$tag.options"
  else
    echo "$test_file.options"
  fi
}

# The gold of a tag, falling back to the one shared by every tag
gold_of() {
  local tag=$1

  if [ -n "$tag" ] && [ -e "$test_file.$tag.gold" ] ; then
    echo "$test_file.$tag.gold"
  elif [ -e "$test_file.gold" ] ; then
    echo "$test_file.gold"
  fi
}

# Where the log of a run goes. One log per option set, so that the counts in
# check.sh see every run.
log_file_of() {
  local tag=$1
  local base

  if [ ! -d "$out_dir" ] ; then
    return 0
  fi

  # replace _ with __ and / with _
  base="$out_dir/_$(echo "${test_file//_/__}" | tr '/' '_')"
  if [ -n "$tag" ] ; then
    base="$base@$tag"
  fi

  echo "$base"
}

# Run the test under one option set. Returns 0 when it passes.
run_option_set() {
  local tag=$1
  local options_file
  local options
  local test_string
  local log_file
  local gold
  local code

  options_file=$(options_file_of "$tag")
  options=$base_options
  test_string="$test_file"
  if [ -n "$tag" ] ; then
    test_string="$test_string ($tag)"
  fi
  if [ -e "$options_file" ] ; then
    options="$options $(cat "$options_file")"
  fi
  # An option set may well be empty: unquoted, it collapses to nothing
  if [ -n "$(echo $options)" ] ; then
    test_string="$test_string [ $options ]"
  fi

  log_file=$(log_file_of "$tag")

  gold=$(gold_of "$tag")
  if [ -z "$gold" ] ; then
    echo "$red FAIL: missing file: $test_file.gold $black"
    if [ -n "$log_file" ] ; then
      echo "$test_string" > "$log_file.error"
      echo "missing file: $test_file.gold" >> "$log_file.error"
    fi
    return 2
  fi

  # Declared before the assignments: "local x=$(cmd)" would overwrite the exit
  # status of cmd with the one of local
  local status runtime DIFF diff_status

  run_solver_once "$options" "$outfile" "$timefile"
  status=$?
  runtime=$(cat "$timefile")

  DIFF=$(diff -w "$outfile" "$gold")
  diff_status=$?

  if [ $diff_status -eq 0 ] && [ $status -eq 0 ]
  then
      echo -e "$green PASS [${runtime} s] $black $test_string"
      if [ -n "$log_file" ] ; then
          echo "$test_string" > "$log_file.pass"
          echo "$runtime" >> "$log_file.pass"
      fi
      code=0
  else
      echo -e "$red FAIL $black $test_string"
      if [ -n "$log_file" ] ; then
          echo "$test_string" > "$log_file.error"
          echo "$runtime" >> "$log_file.error"
          if [ $status -ne 0 ]; then
              echo "exit status: $status" >> "$log_file.error"
          fi
          echo "$DIFF" >> "$log_file.error"
      fi
      code=1
  fi

  return $code
}

#
# One run per option set: the untagged one when it exists, or when the input has
# no option set at all, then one per tag that is not disabled.
#
tags=$(collect_tags)
code=0

if [ -e "$test_file.options" ] || [ -z "$tags" ] ; then
  run_option_set "" || code=1
fi

while IFS= read -r tag; do
  [ -n "$tag" ] || continue
  is_tag_disabled "$tag" && continue
  run_option_set "$tag" || code=1
done <<< "$tags"

exit $code
