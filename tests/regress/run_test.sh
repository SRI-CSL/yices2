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
# Usage: run_test.sh <test-file> <bin-dir> [<out-dir>]
#
# test-file is the test file the SMT1, SMT2, or Yices input language
# bin-dir contains the Yices binaries for each of these languages
# tmp-dir (optional) and specifies the location to put the results
#
# For each test file, the expected results are stored in file.gold
# and command-line options are stored in file.options.
#
# This scripts calls the appropriate binary on each test file, passing it
# the command-line options if any, then check whether the output matches
# what's expected.
#

usage() {
  echo "Usage: $0 <test-file> <bin-dir> [out-dir]"
  exit 4
}

smt2_options=
color=

while getopts "cs:" o; do
    case "$o" in
    s)
      smt2_options=${OPTARG}
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
# The temp file for output
#
outfile=$($mktemp_cmd) || { echo "Can't create temp file" ; exit 3 ; }
timefile=$($mktemp_cmd) || { echo "Can't create temp file" ; exit 3 ; }

if [[ -z "$TIME_LIMIT" ]];
then
    TIME_LIMIT=60
fi

# Get the binary based on the filename
filename=$(basename "$test_file")

options=

case $filename in
    *.smt2)
        binary=yices_smt2
        options=$smt2_options
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

# Get the options
if [ -e "$test_file.options" ]
then
    options="$options $(cat $test_file.options)"
    test_string="$test_file [ $options ]"
else
    test_string="$test_file"
fi

# Get the expected result
if [ -e "$test_file.gold" ]
then
    gold=$test_file.gold
else
    echo "$red FAIL: missing file: $test_file.gold $black"
    exit 2
fi

if [ -d "$out_dir" ] ; then
    # add pid in case there are multiple tests with the same name
    log_file="$out_dir/$filename.$BASHPID"
fi

# Run the binary
(
  ulimit -S -t $TIME_LIMIT &> /dev/null
  ulimit -H -t $((1+$TIME_LIMIT)) &> /dev/null
  (time ./$bin_dir/$binary $options ./$test_file >& $outfile ) >& $timefile
)
status=$?
runtime=$(cat "$timefile")

# Do the diff
DIFF=$(diff -w "$outfile" "$gold")

if [ $? -eq 0 ] && [ $status -eq 0 ]
then
    echo -e "$green PASS [${runtime} s] $black $test_string"
    if [ -n "$log_file" ] ; then
        log_file="$log_file.pass"
        echo "$test_string" > "$log_file"
    fi
    code=0
else
    echo -e "$red FAIL $black $test_string"
    if [ -n "$log_file" ] ; then
        log_file="$log_file.error"
        echo "$test_string" > "$log_file"
        echo "$DIFF" >> "$log_file"
    fi
    code=1
fi

rm "$timefile"
rm "$outfile"
exit $code
