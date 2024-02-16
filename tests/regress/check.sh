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
# Run regression tests
#
# Usage: check.sh <test-dir> <bin-dir>
#
# tests-dir contains test files in the SMT1, SMT2, or Yices input language
# bin-dir contains the Yices binaries for each of these languages
#
# For each test file, the expected results are stored in file.gold
# and command-line options are stored in file.options.
#
# This scripts calls the appropriate binary on each test file, passing it
# the command-line options if any, then check whether the output matches
# what's expected.
#

usage() {
   echo "Usage: $0 <test-directory> <bin-directory> [test1] [test2] ..."
   exit
}

smt2_options=
use_parallel=

while getopts "js:" o; do
    case "$o" in
    s)
      smt2_options=${OPTARG}
      ;;
    j)
      use_parallel=yes
      ;;
    *)
      usage
      ;;
    esac
done
shift $((OPTIND-1))

if test $# "<" 2 ; then
    usage
fi

regress_dir=$1
bin_dir=$2
shift 2
all_tests="$@"

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
# The temp file for output
#
logdir=$($mktemp_cmd -d) || { echo "Can't create temp folder" ; exit 1 ; }

if [[ -z "$REGRESS_FILTER" ]];
then
    REGRESS_FILTER="."
fi

#
# Check if MCSAT is supported
#
./"$bin_dir"/yices_smt2 --mcsat >& /dev/null < /dev/null
if [ $? -ne 0 ]
then
    MCSAT_FILTER="-v mcsat"
else
    MCSAT_FILTER="."
fi

if [ -z "$all_tests" ] ; then
    all_tests=$(
    find "$regress_dir" -name '*.smt' -or -name '*.smt2' -or -name '*.ys' |
      grep $REGRESS_FILTER | grep $MCSAT_FILTER |
      sort
    )
fi

run_parallel="no"
if [ -n "$use_parallel" ] ; then
    if command -v parallel &> /dev/null ; then
        if parallel --version 2>&1 | grep GNU > /dev/null 2>&1 ; then
            run_parallel="gnu"
        else
            run_parallel="more"
        fi
    else
        echo "****************************************************************"
        echo "HINT: Install moreutils or GNU parallel to run tests in parallel"
        echo "****************************************************************"
    fi
fi

if [ -t 1 ] ; then
  color_flag="-c"
fi

case "$run_parallel" in
    more)
        parallel -i bash "${BASH_SOURCE%/*}/run_test.sh" $color_flag -s "$smt2_options" {} "$bin_dir" "$logdir" -- $all_tests
        ;;
    gnu)
        parallel -q bash "${BASH_SOURCE%/*}/run_test.sh" $color_flag -s "$smt2_options" {} "$bin_dir" "$logdir" ::: $all_tests
        ;;
    *)
        for file in $all_tests; do
            bash "${BASH_SOURCE%/*}"/run_test.sh $color_flag -s "$smt2_options" "$file" "$bin_dir" "$logdir"
        done
        ;;
esac

pass=$(find "$logdir" -type f -name "*.pass" | wc -l)
fail=$(find "$logdir" -type f -name "*.error" | wc -l)

echo "Pass: $pass"
echo "Fail: $fail"

if [ "$fail" -eq 0 ] ; then
    code=0
else
    for f in "$logdir"/*.error ; do
      cat "$f"
      echo
    done
    code=1
fi

rm -rf "$logdir"
exit $code
