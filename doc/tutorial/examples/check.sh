#!/usr/bin/env bash
# Runs each example of the tutorial with the solver expected.txt names and compares the outcome
# with the one the tutorial shows.
#
# Usage: check.sh [-n] [pattern]
#   -n       list the runs the selection chooses, and run nothing
#   pattern  run only the files whose path contains it
#
# THRUST_RUSTC names the thrust-rustc binary (default: the debug build of this checkout); the
# toolchain's libraries must be on LD_LIBRARY_PATH, as `cargo run` sets them.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
thrust=${THRUST_RUSTC:-$root/target/debug/thrust-rustc}
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

# Prints the outcome of verifying $1 with solver $2.
verify() {
    local file=$1 solver=$2 log=$out/log
    local -a env=(THRUST_SOLVER_TIMEOUT_SECS=30)
    if [[ $solver == pcsat ]]; then
        env=(THRUST_SOLVER="$root/tests/thrust-pcsat-wrapper" THRUST_SOLVER_TIMEOUT_SECS=60)
    fi
    if env "${env[@]}" "$thrust" -C debug-assertions=off --out-dir "$out" "$file" >"$log" 2>&1; then
        echo safe
    elif grep -q 'verification error: Unsat' "$log"; then
        echo unsat
    elif grep -q 'verification error: Timeout' "$log"; then
        echo timeout
    else
        echo error
    fi
}

dry_run=0
if [[ ${1:-} == -n ]]; then
    dry_run=1
    shift
fi
pattern=${1:-}

cd "$here"
failed=0
while read -r file solver expected; do
    [[ -z $file || $file == \#* ]] && continue
    [[ $file == *"$pattern"* ]] || continue
    if (( dry_run )); then
        echo "$file $solver $expected"
        continue
    fi
    actual=$(verify "$file" "$solver")
    if [[ $actual == "$expected" ]]; then
        echo "ok   $file $solver $actual"
    else
        echo "FAIL $file $solver: expected $expected, got $actual"
        failed=1
    fi
done < expected.txt
exit $failed
