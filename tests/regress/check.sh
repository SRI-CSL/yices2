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

cleanup() {
    [[ -n "$logdir" ]] && rm -rf "$logdir"
}

smt2_options=
j_option=

while getopts "js:" o; do
    case "$o" in
    s)
      smt2_options=${OPTARG}
      ;;
    j)
      j_option=yes
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

parallel_tool=
if command -v parallel &> /dev/null ; then
    if parallel --version 2>&1 | grep GNU > /dev/null 2>&1 ; then
        parallel_tool="gnu"
    else
        parallel_tool="more"
    fi
fi

#
# The temp file for output
#
trap cleanup EXIT
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

if [ -t 1 ] ; then
  color_flag="-c"
fi

# job_count 1: serial execution, 0: unrestricted parallel, n>1: n processes
job_count=1

#check if we are in a make run with -j N
if [[ -n "$j_option" ]]; then
    job_count=0
elif [[ "$MAKEFLAGS" =~ --jobserver-(fds|auth)=([0-9]+),([0-9]+) ]]; then
    # greedy get as many tokens as possible
    fdR=$(echo "$MAKEFLAGS" | sed -E "s|.*--jobserver-(fds\|auth)=([0-9]+),([0-9]+).*|\2|")
    fdW=$(echo "$MAKEFLAGS" | sed -E "s|.*--jobserver-(fds\|auth)=([0-9]+),([0-9]+).*|\3|")
    while IFS= read -r -d '' -t 1 -n 1 <&"$fdR"; do
      job_count=$((job_count+1))
    done
elif [[ "$MAKEFLAGS" =~ --jobserver-auth=fifo:([^ ]+) ]]; then
    fifo=$(echo "$MAKEFLAGS" | sed -E "s|.*--jobserver-auth=fifo:([^ ]+).*|\1|")
    while IFS= read -r -d '' -t 1 -n 1 <"$fifo"; do
      job_count=$((job_count+1))
    done
elif [[ "$MAKEFLAGS" =~ (^|[ ])-?j($|[ ]) ]]; then
    job_count=0
fi

if [[ $job_count != 1 ]] && [[ -z "$parallel_tool" ]]; then
    echo "**********************************************************"
    echo "Install moreutils or GNU parallel to run tests in parallel"
    echo "**********************************************************"
else
    case $job_count in
        0) echo "Running in parallel";;
        1) echo "Running sequentially";;
        *) echo "Running with $job_count parallel jobs";;
    esac
fi

j_param="-j$job_count"
if [[ $job_count == 0 ]]; then j_param=""; fi

case "$parallel_tool" in
    more)
        parallel -i $j_param bash "${BASH_SOURCE%/*}/run_test.sh" $color_flag -s "$smt2_options" {} "$bin_dir" "$logdir" -- $all_tests
        ;;
    gnu)
        parallel -q $j_param bash "${BASH_SOURCE%/*}/run_test.sh" $color_flag -s "$smt2_options" {} "$bin_dir" "$logdir" ::: $all_tests
        ;;
    *)
        for file in $all_tests; do
            bash "${BASH_SOURCE%/*}"/run_test.sh $color_flag -s "$smt2_options" "$file" "$bin_dir" "$logdir"
        done
        ;;
esac

# give back tokens
while [[ $job_count -gt 1 ]]; do
    [[ -n $fdW ]] && echo -n '+' >&"$fdW"
    [[ -n $fifo ]] && echo -n '+' >"$fifo"
    job_count=$((job_count-1))
done

pass=$(find "$logdir" -type f -name "*.pass" | wc -l)
fail=$(find "$logdir" -type f -name "*.error" | wc -l)

echo "Pass: $pass"
echo "Fail: $fail"
if [[ $pass -gt 0 ]]; then
    echo "Runtime:          $(find "$logdir" -type f -exec sed -n '2p' {} \; | paste -sd+ - | bc) s"
    if [[ $fail -gt 0 ]]; then
        echo "Runtime (passed): $(find "$logdir" -type f -name "*.pass" -exec sed -n '2p' {} \; | paste -sd+ - | bc) s"
    fi
fi

if [ "$fail" -eq 0 ] ; then
    code=0
else
    for f in "$logdir"/*.error ; do
      cat "$f"
      echo
    done
    code=1
fi

exit $code
