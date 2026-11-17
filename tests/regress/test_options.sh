# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause

# Shared selection only: callers independently enumerate expected and actual
# runs. An empty tag is the untagged run; tagged options do not inherit it.
# Keep this compatible with Bash 3.2 (no associative arrays or mapfile).
collect_test_tags() {
    local input=$1 disabled_list=$2 file tag disabled skip
    local tags=() disabled_array=()
    test_tags=()
    disabled_list=${disabled_list//,/ }
    IFS=$' \t\n' read -r -a disabled_array <<< "$disabled_list"

    for file in "$input".*.options; do
        [ -e "$file" ] || [ -L "$file" ] || continue
        tag=${file#"$input".}
        tag=${tag%.options}
        case "$tag" in ''|*.*) continue ;; esac
        # Do not treat another input's options as a tag of this input.
        [ ! -e "$input.$tag" ] || continue
        if [[ "$tag" == *$'\n'* ]]; then
            echo "Newline-containing regression tag is not supported: $file" >&2
            return 2
        fi
        tags+=("$tag")
    done
    if [ -e "$input.options" ] || [ -L "$input.options" ] || [ ${#tags[@]} -eq 0 ]; then
        test_tags+=("")
    fi
    for tag in "${tags[@]}"; do
        skip=no
        for disabled in "${disabled_array[@]}"; do
            [ "$disabled" != "$tag" ] || skip=yes
        done
        [ "$skip" = yes ] || test_tags+=("$tag")
    done
}

# Optional delegates are a property of each option set, not of the whole
# input. The dispatcher supplies its feature-probe results to the worker.
option_file_delegate() (
    local opt_file=$1 tok next= text
    [ -e "$opt_file" ] || return 1
    text=$(cat "$opt_file") || return 2
    set -f
    for tok in $text; do
        if [ -n "$next" ]; then
            printf '%s\n' "$tok"
            return 0
        fi
        case "$tok" in
            --delegate=*) printf '%s\n' "${tok#--delegate=}"; return 0 ;;
            --delegate) next=yes ;;
        esac
    done
    return 1
)

filter_test_tags_for_delegates() {
    local input=$1 unavailable=$2 tag opt_file delegate item skip
    local retained=()
    [ -n "$unavailable" ] || return 0
    for tag in "${test_tags[@]}"; do
        opt_file="$input.options"
        [ -z "$tag" ] || opt_file="$input.$tag.options"
        delegate=$(option_file_delegate "$opt_file")
        skip=no
        for item in $unavailable; do
            [ "$delegate" != "$item" ] || skip=yes
        done
        if [ "$skip" = yes ]; then
            echo "Skipping $input (${tag:-untagged}): delegate '$delegate' is not supported by this build" >&2
        else
            retained+=("$tag")
        fi
    done
    test_tags=("${retained[@]}")
}

# %q makes the pair unambiguous even for tabs, spaces and shell metacharacters.
# Nothing evaluates these keys: the dispatcher compares sorted text only.
test_result_key() {
    printf '%q %q\n' "$1" "$2"
}
