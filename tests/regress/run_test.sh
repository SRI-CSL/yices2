#!/bin/bash

#
#  Copyright (c) 2026, SRI International
#  SPDX-License-Identifier: BSD-3-Clause
#

# Run an input once per option set: file.options is untagged and
# file.<tag>.options is tagged. Without any sidecars there is one plain run.
# Tagged sets do not inherit file.options. An empty file.options explicitly
# retains the plain run alongside tags. Tags have no dot; options belonging
# to another input sharing this prefix are not tags.
# Compare file.<tag>.gold when present, otherwise file.gold.
# -x excludes tags (comma/space separated). regress/both uses mcsat/dpllt
# sidecars, not implicit directory-specific execution.
#
# One unique terminal record per variant preserves duplicates and parallel
# safety. Its first two lines are the exact input spelling and tag, consumed
# by check.sh's independently enumerated expected-result multiset.

usage() {
    echo "Usage: $0 [-c] [-s <smt2-options>] [-x <tags>] [-u <unavailable-delegates>] <test-file> <bin-dir> [out-dir]"
    exit 4
}

script_dir=${BASH_SOURCE%/*}
[ "$script_dir" != "$BASH_SOURCE" ] || script_dir=.
source "$script_dir/test_options.sh" || exit 4
smt2_options=
disabled_tags=
unavailable_delegates=
color=
while getopts "cs:x:u:" o; do
    case "$o" in
        s) smt2_options=$OPTARG ;;
        x) disabled_tags=$OPTARG ;;
        u) unavailable_delegates=$OPTARG ;;
        c) color=on ;;
        *) usage ;;
    esac
done
shift $((OPTIND-1))
[ $# -ge 2 ] && [ $# -le 3 ] || usage
test_file=$1
bin_dir=$2
out_dir=${3-}
test_string=$test_file
tag=
export LIBC_FATAL_STDERR_=1
TIMEFORMAT="%U"
TIME_LIMIT=${TIME_LIMIT:-60}

red= green= black=
if [ -t 1 ] || [ -n "$color" ]; then
    red=$(tput setaf 1)
    green=$(tput setaf 2)
    black=$(tput sgr0)
fi

outfile= timefile= log_file=
result_line= result_detail=
completed=no
active=no
termination_signal=

record_result() {
    local status=$1 suffix=error result_color=$red tmp_file
    if [ -z "$result_line" ]; then
        result_line="FAIL: worker exited with status $status: $test_string"
    fi
    if [ "$status" -eq 0 ]; then
        suffix=pass
        result_color=$green
    fi
    if [ -n "$log_file" ]; then
        if ! printf '%s\n' "$test_file" "$tag" "$test_string" "$result_detail" > "$log_file" ||
           ! mv "$log_file" "$log_file.$suffix"; then
            result_line="FAIL: cannot record result for $test_string"
            result_color=$red
            status=3
        fi
    fi
    # Only this worker's successfully allocated temporary files are removed.
    for tmp_file in "$outfile" "$timefile" "$log_file"; do
        [ -z "$tmp_file" ] || rm -f "$tmp_file"
    done
    outfile= timefile= log_file=
    active=no
    printf '%s %s %s\n' "$result_color" "$result_line" "$black"
    result_line= result_detail=
    return "$status"
}

finish() {
    local status=$?
    trap - EXIT
    if [ "$completed" != yes ] && [ "$status" -eq 0 ]; then
        status=1
    fi
    if [ "$active" = yes ] || [ "$completed" != yes ]; then
        record_result "$status"
        status=$?
    fi
    if [ -n "$termination_signal" ]; then
        # Bash's parent must see SIGINT termination, not an ordinary exit 130.
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

# A setup failure must also leave a terminal error record.
if [ -n "$out_dir" ]; then
    [ -d "$out_dir" ] || fail_test 3 "result directory is missing: $out_dir"
    log_file=$(mktemp "$out_dir/result.XXXXXXXX") || fail_test 3 "cannot allocate result in $out_dir"
fi
active=yes

if [[ -z "$test_file" || "$test_file" == *$'\n'* ]]; then
    fail_test 2 "empty or newline-containing regression pathname is not supported"
fi
# Keep the caller's spelling as identity, but make file operands unambiguous.
case "$test_file" in
    /*|./*|../*) test_path=$test_file ;;
    *) test_path="./$test_file" ;;
esac
case "$bin_dir" in /*|./*|../*) ;; *) bin_dir="./$bin_dir" ;; esac
filename=${test_path##*/}
base_options=
case "$filename" in
    *.smt2) binary=yices_smt2; base_options=$smt2_options ;;
    *.smt) binary=yices_smtcomp ;;
    *.ys) binary=yices ;;
    *) fail_test 2 "unknown extension for $filename" ;;
esac
[ -f "$test_path" ] && [ -r "$test_path" ] || fail_test 2 "missing or unreadable test: $test_file"
[ -x "$bin_dir/$binary" ] || fail_test 2 "solver is missing or not executable: $bin_dir/$binary"
collect_test_tags "$test_path" "$disabled_tags" || fail_test 2 "cannot enumerate option sets for $test_file"
filter_test_tags_for_delegates "$test_path" "$unavailable_delegates"

if [ ${#test_tags[@]} -eq 0 ]; then
    [ -z "$log_file" ] || rm -f "$log_file"
    log_file=
    active=no
    completed=yes
    echo "SKIP: all option-set variants are disabled or unsupported: $test_file"
    # A direct worker with zero runs must not report successful testing.
    exit 1
fi

run_solver_once() {
    local run_options=$1
    (
        ulimit -S -t "$TIME_LIMIT" &> /dev/null || exit 3
        ulimit -H -t $((1+TIME_LIMIT)) &> /dev/null || exit 3
        # Options files use whitespace-separated arguments, not shell syntax.
        # Disable glob expansion so an option cannot expand into local files.
        set -f
        (time "$bin_dir/$binary" $run_options "$test_path" >& "$outfile") >& "$timefile"
    )
}

variant_error() {
    result_detail="$*"
    result_line="FAIL: $result_detail"
    return 2
}

run_variant() {
    local options_file="$test_path.options" gold="$test_path.gold"
    local options=$base_options file_options status runtime difference diff_status
    test_string=$test_file
    if [ -n "$tag" ]; then
        options_file="$test_path.$tag.options"
        test_string="$test_file ($tag)"
        if [ -e "$test_path.$tag.gold" ] || [ -L "$test_path.$tag.gold" ]; then
            gold="$test_path.$tag.gold"
        fi
    fi
    if [ -e "$options_file" ] || [ -L "$options_file" ]; then
        if ! file_options=$(cat "$options_file"); then
            variant_error "cannot read $options_file"; return 2
        fi
        options="$options $file_options"
    fi
    test_string="$test_string [ $options ]"
    if [ ! -f "$gold" ] || [ ! -r "$gold" ]; then
        variant_error "missing or unreadable file: $gold"; return 2
    fi
    outfile=$(mktemp "${TMPDIR:-/tmp}/yices-test.XXXXXXXX") || {
        variant_error "cannot create solver output file"; return 3;
    }
    timefile=$(mktemp "${TMPDIR:-/tmp}/yices-test.XXXXXXXX") || {
        variant_error "cannot create timing file"; return 3;
    }
    run_solver_once "$options"
    status=$?
    if ! runtime=$(cat "$timefile"); then
        variant_error "cannot read timing file"; return 3
    fi
    difference=$(diff -w "$outfile" "$gold")
    diff_status=$?
    if [ "$status" -eq 0 ] && [ "$diff_status" -eq 0 ]; then
        result_line="PASS [${runtime} s] $test_string"
        result_detail=$runtime
        return 0
    fi
    result_line="FAIL $test_string"
    result_detail="exit status: $status"$'\n'"$runtime"$'\n'"$difference"
    return 1
}

code=0
for tag in "${test_tags[@]}"; do
    active=yes
    if [ -n "$out_dir" ] && [ -z "$log_file" ]; then
        log_file=$(mktemp "$out_dir/result.XXXXXXXX") || fail_test 3 "cannot allocate result in $out_dir"
    fi
    run_variant
    status=$?
    record_result "$status" || code=1
done
completed=yes
exit "$code"
