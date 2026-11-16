#!/bin/bash

#
#  Copyright (c) 2026, SRI International
#  SPDX-License-Identifier: BSD-3-Clause
#

#
# Run regression tests
#
# Usage: check.sh [-j] [-s options] [-x tags] [-d extra-dir] <test-dir> <bin-dir>
#
# test-dir contains test files in the SMT1, SMT2, or Yices input language.
# A literal directory takes priority over the legacy space-separated list.
# Repeat -d for additional directories, including paths containing spaces.
# Each file.options or file.<tag>.options is one separately counted test.
# -x / REGRESS_DISABLE_TAGS excludes named tags (comma/space separated).
# Tagged gold falls back to file.gold; see test_options.sh and run_test.sh.
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
   echo "Usage: $0 [-j] [-s options] [-x tags] [-d extra-directory] <test-directory> <bin-directory> [test1] [test2] ..."
   exit 2
}

script_dir=${BASH_SOURCE%/*}
[ "$script_dir" != "$BASH_SOURCE" ] || script_dir=.
source "$script_dir/test_options.sh" || exit 2

cleanup() {
    [[ -n "$logdir" ]] && rm -rf "$logdir"
}

run_test_batch() {
    local local_smt2_options="$1"
    local run_label="$2"
    shift 2
    local test_set=("$@")
    local run_logdir="$logdir/$run_label"
    local batch_status=0
    local file marker recorded_test recorded_tag tag
    local runnable=() batch_selected=0
    local batch_pass=0 batch_fail=0

    if [ ${#test_set[@]} -eq 0 ] ; then
        return 0
    fi

    mkdir -p "$run_logdir" || { echo "Can't create temp folder $run_logdir" >&2 ; return 1 ; }
    : > "$run_logdir/expected" || return 1
    : > "$run_logdir/observed" || return 1
    for file in "${test_set[@]}"; do
        collect_test_tags "$file" "$disabled_tags" || return 1
        filter_test_tags_for_delegates "$file" "$unavailable_delegates"
        if [ ${#test_tags[@]} -eq 0 ]; then
            echo "Skipping $file: all option-set variants are disabled or unsupported" >&2
            continue
        fi
        runnable+=("$file")
        for tag in "${test_tags[@]}"; do
            test_result_key "$file" "$tag" >> "$run_logdir/expected" || return 1
            batch_selected=$((batch_selected + 1))
        done
    done
    selected=$((selected + batch_selected))
    test_set=("${runnable[@]}")
    [ ${#test_set[@]} -ne 0 ] || return 0

    case "$parallel_tool" in
        more)
            parallel -i $j_param bash "$script_dir/run_test.sh" $color_flag -s "$local_smt2_options" -x "$disabled_tags" -u "$unavailable_delegates" {} "$bin_dir" "$run_logdir" -- "${test_set[@]}" || batch_status=1
            ;;
        gnu)
            parallel -q $j_param bash "$script_dir/run_test.sh" $color_flag -s "$local_smt2_options" -x "$disabled_tags" -u "$unavailable_delegates" -- {} "$bin_dir" "$run_logdir" ::: "${test_set[@]}" || batch_status=1
            ;;
        *)
            for file in "${test_set[@]}"; do
                bash "$script_dir/run_test.sh" $color_flag -s "$local_smt2_options" -x "$disabled_tags" -u "$unavailable_delegates" -- "$file" "$bin_dir" "$run_logdir" || batch_status=1
            done
            ;;
    esac

    if [ "$batch_status" -ne 0 ]; then
        echo "Regression worker or dispatcher failed in batch $run_label" >&2
    fi

    # Every selected option variant owns a unique marker. Its first two lines
    # identify the input and tag. Compare multisets: duplicates must run twice,
    # and a repeated variant cannot conceal a missing or failed variant.
    for marker in "$run_logdir"/*.pass "$run_logdir"/*.error; do
        [ -f "$marker" ] || continue
        if ! { IFS= read -r recorded_test && IFS= read -r recorded_tag; } < "$marker"; then
            echo "Unreadable regression result: $marker" >&2
            batch_status=1
        else
            test_result_key "$recorded_test" "$recorded_tag" >> "$run_logdir/observed" || batch_status=1
        fi
        case "$marker" in
            *.pass) batch_pass=$((batch_pass + 1)) ;;
            *.error) batch_fail=$((batch_fail + 1)) ;;
        esac
    done
    pass=$((pass + batch_pass))
    fail=$((fail + batch_fail))

    LC_ALL=C sort "$run_logdir/expected" > "$run_logdir/expected.sorted" || return 1
    LC_ALL=C sort "$run_logdir/observed" > "$run_logdir/observed.sorted" || return 1
    if ! cmp -s "$run_logdir/expected.sorted" "$run_logdir/observed.sorted"; then
        echo "Regression result accounting failed in batch $run_label: $batch_selected selected, $batch_pass pass, $batch_fail fail" >&2
        diff -u "$run_logdir/expected.sorted" "$run_logdir/observed.sorted" >&2
        batch_status=1
    fi
    [ "$batch_fail" -eq 0 ] || batch_status=1
    return "$batch_status"
}

is_qf_bv_delegate_candidate() {
    local file="$1"
    local opt_file gold_file tag

    case "$file" in
        *.smt2)
            ;;
        *)
            return 1
            ;;
    esac

    case "$file" in
        */mcsat/*)
            return 1
            ;;
    esac

    if ! grep -Eq '^[[:space:]]*\(set-logic[[:space:]]+QF_BV\)' "$file" ; then
        return 1
    fi

    # Delegate regressions should compare SAT status only.
    # Exclude tests that query models/values/cores/assumptions.
    if grep -Eq '\(get-model\)|\(get-value\)|\(get-unsat-core\)|\(get-unsat-assumptions\)|\(get-assignment\)' "$file"; then
        return 1
    fi

    if grep -Eq '\(echo[[:space:]]' "$file"; then
        return 1
    fi

    # Fan-out is conservative: every selected variant must accept an added
    # delegate and compare status only. Never combine --mcsat with a delegate
    # merely because its option set is tagged rather than untagged.
    collect_test_tags "$file" "$disabled_tags" || return 1
    filter_test_tags_for_delegates "$file" "$unavailable_delegates"
    [ ${#test_tags[@]} -ne 0 ] || return 1
    for tag in "${test_tags[@]}"; do
        opt_file="$file.options"
        gold_file="$file.gold"
        if [ -n "$tag" ]; then
            opt_file="$file.$tag.options"
            if [ -e "$file.$tag.gold" ] || [ -L "$file.$tag.gold" ]; then
                gold_file="$file.$tag.gold"
            fi
        fi
        [ -f "$gold_file" ] && [ -r "$gold_file" ] || return 1
        if grep -Eqv '^[[:space:]]*$|^[[:space:]]*(sat|unsat|unknown)[[:space:]]*$' "$gold_file"; then
            return 1
        fi
        if [ -e "$opt_file" ] || [ -L "$opt_file" ]; then
            [ -f "$opt_file" ] && [ -r "$opt_file" ] || return 1
            if grep -Eq '(^|[[:space:]])--delegate(=|[[:space:]])|(^|[[:space:]])--mcsat([[:space:]]|$)' "$opt_file"; then
                return 1
            fi
        fi
    done

    return 0
}

supports_delegate() {
    local delegate="$1"
    "$bin_dir"/yices_smt2 --delegate="$delegate" < /dev/null > /dev/null 2>&1
}

check_test_path() {
    # Result identities and the existing grep-based selection filters are
    # line-oriented. Reject, rather than split, a pathname containing LF.
    if [[ -z "$1" || "$1" == *$'\n'* ]]; then
        echo "Empty or newline-containing regression pathname is not supported" >&2
        exit 1
    fi
}

smt2_options=
j_option=
disabled_tags=$REGRESS_DISABLE_TAGS
extra_dirs=()

while getopts "js:x:d:" o; do
    case "$o" in
    s)
      smt2_options=${OPTARG}
      ;;
    x)
      disabled_tags=${OPTARG}
      ;;
    d)
      extra_dirs+=("$OPTARG")
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

if [ "$#" -lt 2 ]; then
    usage
fi

regress_dir=$1
bin_dir=$2
shift 2
all_tests=("$@")

# Preserve a real directory with spaces. Otherwise accept master's legacy
# space-separated directory list; -d is the unambiguous form for new callers.
check_test_path "$regress_dir"
regress_dirs=()
if [ -d "$regress_dir" ]; then
    regress_dirs=("$regress_dir")
else
    IFS=$' \t\n' read -r -a regress_dirs <<< "$regress_dir"
fi
[ ${#regress_dirs[@]} -ne 0 ] || usage
regress_dirs+=("${extra_dirs[@]}")
for ((i=0; i<${#regress_dirs[@]}; i++)); do
    directory=${regress_dirs[$i]}
    check_test_path "$directory"
    case "$directory" in /*|./*|../*) ;; *) directory="./$directory" ;; esac
    if [[ ! -d "$directory" ]]; then
        echo "Regression test directory is missing: $directory" >&2
        exit 1
    fi
    regress_dirs[$i]=$directory
done
case "$bin_dir" in /*) ;; *) bin_dir="./$bin_dir" ;; esac
if [[ ! -x "$bin_dir/yices_smt2" ]]; then
    echo "Regression solver is missing or not executable: $bin_dir/yices_smt2" >&2
    exit 1
fi

# REGRESS_DELEGATE_MODE selects whether the regression run also fans out
# into one extra pass per installed external SAT delegate (CaDiCaL,
# CryptoMiniSat, Kissat) on QF_BV tests:
#
#   off  : baseline pass only. This is the default so that "make check"
#          and "make regress" keep their pre-delegate runtime.
#   auto : baseline pass + one pass per installed delegate (opt-in).
#   only : delegate passes only, no baseline. Used by the
#          delegate-regress / static-delegate-regress make targets.
if [[ -z "$REGRESS_DELEGATE_MODE" ]]; then
    REGRESS_DELEGATE_MODE="off"
fi

case "$REGRESS_DELEGATE_MODE" in
    auto|only|off)
        ;;
    *)
        echo "Invalid REGRESS_DELEGATE_MODE='$REGRESS_DELEGATE_MODE' (expected auto|only|off)"
        exit 2
        ;;
esac

# Use the installed parallel backend, if any.
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
logdir=$(mktemp -d "${TMPDIR:-/tmp}/yices-regress.XXXXXXXX") || { echo "Can't create temp folder" ; exit 1 ; }

if [[ -z "$REGRESS_FILTER" ]];
then
    REGRESS_FILTER="."
fi

if [[ -z "$REGRESS_EXCLUDE_FILTER" ]];
then
    REGRESS_EXCLUDE_FILTER="^$"
fi

#
# Check if MCSAT is supported
#
"$bin_dir"/yices_smt2 --mcsat >& /dev/null < /dev/null
if [ $? -ne 0 ]
then
    MCSAT_FILTER="-v -E /(mcsat|both)/"
else
    MCSAT_FILTER="."
fi

if [ ${#all_tests[@]} -eq 0 ] ; then
    # Do not hide find's failure behind successful grep/sort processes.
    if ! find "${regress_dirs[@]}" -type f \( -name '*.smt' -o -name '*.smt2' -o -name '*.ys' \) -print0 > "$logdir/discovered"; then
        echo "Could not enumerate regression tests: $regress_dir" >&2
        exit 1
    fi
    : > "$logdir/discovered.lines" || exit 1
    while IFS= read -r -d '' file; do
        check_test_path "$file"
        printf '%s\n' "$file" >> "$logdir/discovered.lines" || exit 1
    done < "$logdir/discovered"
    (
    cat "$logdir/discovered.lines" |
      grep $REGRESS_FILTER | grep $MCSAT_FILTER | grep -v "$REGRESS_EXCLUDE_FILTER" |
      sort
    ) > "$logdir/selected" || exit 1
    while IFS= read -r file; do
        all_tests+=("$file")
    done < "$logdir/selected"
fi

for ((i=0; i<${#all_tests[@]}; i++)); do
    file=${all_tests[$i]}
    check_test_path "$file"
    # moreutils uses -- to separate its command and inputs, so no second --
    # can be passed to the worker. Prefix relative paths to disambiguate a
    # test basename beginning with '-'; never prefix an absolute pathname.
    case "$file" in
        /*|./*|../*) ;;
        *) all_tests[$i]="./$file" ;;
    esac
done
unavailable_delegates=
for d in cadical cryptominisat kissat; do
    if ! supports_delegate "$d"; then
        unavailable_delegates="$unavailable_delegates $d"
    fi
done

if [ ${#all_tests[@]} -eq 0 ]; then
    echo "No runnable regression tests selected from $regress_dir; zero tests is not a PASS" >&2
    exit 1
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

#
# Baseline regression pass
#
pass=0
fail=0
selected=0
failed_batches=0
if [[ "$REGRESS_DELEGATE_MODE" != "only" ]]; then
    run_test_batch "$smt2_options" baseline "${all_tests[@]}" || failed_batches=$((failed_batches + 1))
fi

#
# Delegate passes on QF_BV tests:
# run one extra pass for each installed external delegate.
#
delegate_tests=()
if [[ "$REGRESS_DELEGATE_MODE" != "off" ]] && ! echo " $smt2_options " | grep -Eq '(^|[[:space:]])--delegate(=|[[:space:]])'; then
    for file in "${all_tests[@]}"; do
        if is_qf_bv_delegate_candidate "$file"; then
            delegate_tests+=("$file")
        fi
    done
fi

if [ ${#delegate_tests[@]} -ne 0 ]; then
    delegates=
    for d in cadical cryptominisat kissat; do
        if supports_delegate "$d"; then
            delegates="$delegates $d"
        fi
    done

    for d in $delegates; do
        echo "=== Running QF_BV delegate regressions ($d) ==="
        run_test_batch "$smt2_options --delegate=$d" "delegate_$d" "${delegate_tests[@]}" || failed_batches=$((failed_batches + 1))
    done
fi

# give back tokens
while [[ $job_count -gt 1 ]]; do
    [[ -n $fdW ]] && echo -n '+' >&"$fdW"
    [[ -n $fifo ]] && echo -n '+' >"$fifo"
    job_count=$((job_count-1))
done

echo "Selected: $selected"
echo "Pass: $pass"
echo "Fail: $fail"
echo "Failed batches: $failed_batches"

if [ "$pass" -eq 0 ] && [ "$fail" -eq 0 ]; then
    echo "No regression test results were produced; zero tests is not a PASS" >&2
    exit 1
fi

if [ "$fail" -eq 0 ] && [ "$failed_batches" -eq 0 ] ; then
    code=0
else
    while IFS= read -r f; do
      cat "$f"
      echo
    done < <(find "$logdir" -type f -name "*.error" | sort)
    code=1
fi

exit $code
