#!/bin/bash

#
#  Copyright (c) 2026, SRI International
#  SPDX-License-Identifier: BSD-3-Clause
#

#
# Run one regression test
#
# Usage: run_test.sh <test-file> <bin-dir> [<out-dir>]
#
# test-file is the test file the SMT1, SMT2, or Yices input language
# bin-dir contains the Yices binaries for each of these languages
# out-dir (optional) specifies the location to put the results
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
test_string=$test_file
out_dir=

if [ $# -ge 3 ] ; then
  out_dir=$3
fi

export LIBC_FATAL_STDERR_=1

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
# Always record a terminal result, including setup failures. A unique marker
# per invocation prevents repeated test selections or parallel workers from
# overwriting each other's results. The first line is the exact input identity
# passed by check.sh; it is used for independent batch accounting.
#
outfile=
timefile=
outfile2=
timefile2=
log_file=
result_line=
result_detail=
completed=no
termination_signal=

finish() {
    local status=$?
    local suffix=error
    local result_color=$red
    trap - EXIT

    if [ "$completed" != yes ] && [ "$status" -eq 0 ]; then
        status=1
    fi
    if [ -z "$result_line" ]; then
        result_line="FAIL: worker exited with status $status: $test_string"
    fi
    if [ "$status" -eq 0 ]; then
        suffix=pass
        result_color=$green
    fi

    if [ -n "$log_file" ]; then
        if ! printf '%s\n' "$test_file" "$test_string" "$result_detail" > "$log_file" ||
           ! mv "$log_file" "$log_file.$suffix"; then
            result_line="FAIL: cannot record result for $test_string"
            result_color=$red
            status=3
        fi
    fi
    # These paths are only this worker's successfully allocated temporary
    # files. The published .pass/.error marker is not removed here.
    for tmp_file in "$outfile" "$timefile" "$outfile2" "$timefile2" "$log_file"; do
        [ -z "$tmp_file" ] || rm -f "$tmp_file"
    done
    printf '%s %s %s\n' "$result_color" "$result_line" "$black"
    if [ -n "$termination_signal" ]; then
        # Preserve signal termination after recording the failed test. In
        # particular, bash's parent must see a child killed by SIGINT, not
        # an ordinary exit 130, for Ctrl-C to stop a serial check.sh run.
        trap - "$termination_signal"
        kill -s "$termination_signal" "$$"
    fi
    exit "$status"
}

fail_test() {
    local status=$1
    shift
    result_detail="$*"
    result_line="FAIL: $result_detail"
    exit "$status"
}

trap finish EXIT
trap 'termination_signal=HUP; exit 129' HUP
trap 'termination_signal=INT; exit 130' INT
trap 'termination_signal=TERM; exit 143' TERM

if [ -n "$out_dir" ]; then
    [ -d "$out_dir" ] || fail_test 3 "result directory is missing: $out_dir"
    log_file=$(mktemp "$out_dir/result.XXXXXXXX") || fail_test 3 "cannot allocate result in $out_dir"
fi

if [[ -z "$test_file" || "$test_file" == *$'\n'* ]]; then
    fail_test 2 "empty or newline-containing regression pathname is not supported"
fi

if [[ -z "$TIME_LIMIT" ]];
then
    TIME_LIMIT=60
fi

# Keep the original spelling for result accounting, but make every file
# operand unambiguous even for a direct invocation with a leading '-'.
case "$test_file" in
    /*|./*|../*) test_path=$test_file ;;
    *) test_path="./$test_file" ;;
esac

# Get the binary based on the filename without parsing it as an option.
filename=${test_path##*/}

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
        fail_test 2 "unknown extension for $filename"
esac

[ -f "$test_path" ] && [ -r "$test_path" ] || fail_test 2 "missing or unreadable test: $test_file"
[ -x "$bin_dir/$binary" ] || fail_test 2 "solver is missing or not executable: $bin_dir/$binary"

# Get the options
if [ -e "$test_path.options" ]
then
    file_options=$(cat "$test_path.options") || fail_test 2 "cannot read $test_file.options"
    options="$options $file_options"
    test_string="$test_file [ $options ]"
else
    test_string="$test_file"
fi

# Get the expected result
if [ -f "$test_path.gold" ] && [ -r "$test_path.gold" ]
then
    gold=$test_path.gold
else
    fail_test 2 "missing or unreadable file: $test_file.gold"
fi

# Keep absolute paths absolute; disambiguate relative names from options.
case "$bin_dir" in /*) ;; *) bin_dir="./$bin_dir" ;; esac
solver_test_file=$test_path

outfile=$(mktemp "${TMPDIR:-/tmp}/yices-test.XXXXXXXX") || fail_test 3 "cannot create solver output file"
timefile=$(mktemp "${TMPDIR:-/tmp}/yices-test.XXXXXXXX") || fail_test 3 "cannot create timing file"

run_solver_once() {
  local run_options=$1
  local run_outfile=$2
  local run_timefile=$3

  (
    ulimit -S -t $TIME_LIMIT &> /dev/null
    ulimit -H -t $((1+$TIME_LIMIT)) &> /dev/null
    (time "$bin_dir/$binary" $run_options "$solver_test_file" >& "$run_outfile") >& "$run_timefile"
  )
}

strip_solver_mode_flags() {
  local input=$1
  local output=
  local tok

  for tok in $input; do
    case "$tok" in
      --mcsat|--dpllt)
        ;;
      *)
        output="$output $tok"
        ;;
    esac
  done

  echo "$output"
}

if [ "$binary" = yices_smt2 ] && [[ "$test_path" == *"/both/"* ]]; then
  options=$(strip_solver_mode_flags "$options")
  test_string="$test_file [ $options --mcsat ] [ $options --dpllt ]"
  gold_mcsat=$gold
  gold_dpllt=$gold

  if [ -e "$test_path.mcsat.gold" ]; then
    gold_mcsat=$test_path.mcsat.gold
  fi

  if [ -e "$test_path.dpllt.gold" ]; then
    gold_dpllt=$test_path.dpllt.gold
  fi

  outfile2=$(mktemp "${TMPDIR:-/tmp}/yices-test.XXXXXXXX") || fail_test 3 "cannot create second solver output file"
  timefile2=$(mktemp "${TMPDIR:-/tmp}/yices-test.XXXXXXXX") || fail_test 3 "cannot create second timing file"

  run_solver_once "$options --mcsat" "$outfile" "$timefile"
  status_mcsat=$?
  runtime_mcsat=$(cat "$timefile") || fail_test 3 "cannot read MCSAT timing file"
  diff_mcsat=$(diff -w "$outfile" "$gold_mcsat")
  diff_status_mcsat=$?

  run_solver_once "$options --dpllt" "$outfile2" "$timefile2"
  status_dpllt=$?
  runtime_dpllt=$(cat "$timefile2") || fail_test 3 "cannot read DPLL(T) timing file"
  diff_dpllt=$(diff -w "$outfile2" "$gold_dpllt")
  diff_status_dpllt=$?

  if [ $status_mcsat -eq 0 ] && [ $diff_status_mcsat -eq 0 ] && [ $status_dpllt -eq 0 ] && [ $diff_status_dpllt -eq 0 ]; then
    result_line="PASS [mcsat ${runtime_mcsat} s, dpllt ${runtime_dpllt} s] $test_string"
    result_detail="mcsat: $runtime_mcsat"$'\n'"dpllt: $runtime_dpllt"
    code=0
  else
    DIFF=
    if [ $status_mcsat -ne 0 ] || [ $diff_status_mcsat -ne 0 ]; then
      DIFF+="--- mcsat (--mcsat) ---"$'\n'
      if [ $status_mcsat -ne 0 ]; then
        DIFF+="exit status: $status_mcsat"$'\n'
      fi
      DIFF+="$diff_mcsat"$'\n'
    fi
    if [ $status_dpllt -ne 0 ] || [ $diff_status_dpllt -ne 0 ]; then
      DIFF+="--- dpllt (--dpllt) ---"$'\n'
      if [ $status_dpllt -ne 0 ]; then
        DIFF+="exit status: $status_dpllt"$'\n'
      fi
      DIFF+="$diff_dpllt"$'\n'
    fi

    result_line="FAIL $test_string"
    result_detail="mcsat: $runtime_mcsat"$'\n'"dpllt: $runtime_dpllt"$'\n'"$DIFF"
    code=1
  fi
else
  # Run the binary once
  run_solver_once "$options" "$outfile" "$timefile"
  status=$?
  runtime=$(cat "$timefile") || fail_test 3 "cannot read timing file"

  # Do the diff
  DIFF=$(diff -w "$outfile" "$gold")

  if [ $? -eq 0 ] && [ $status -eq 0 ]
  then
      result_line="PASS [${runtime} s] $test_string"
      result_detail=$runtime
      code=0
  else
      result_line="FAIL $test_string"
      result_detail="exit status: $status"$'\n'"$runtime"$'\n'"$DIFF"
      code=1
  fi
fi

completed=yes
exit $code
