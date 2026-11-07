#!/bin/sh
# Captures the outputs the unit tests read: for each case, the JSON report, the rustc JSON
# diagnostics on standard error and the exit status of one Thrust run with z3.
#
# Usage: test/capture.sh <thrust-rustc command...>
#   e.g. test/capture.sh rustup run nightly-2025-09-08 ../../target/debug/thrust-rustc
# The command runs in test/fixtures, so the report's spans name the files relatively; the
# report's root, that directory, is written as `.` so the fixtures do not name the machine.
set -eu
[ $# -ge 1 ] || { echo "usage: $0 <thrust-rustc command...>" >&2; exit 2; }
fixtures=$(cd "$(dirname "$0")/fixtures" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT

# capture <case> <source> [VAR=value...]
capture() {
  case_name=$1 source=$2
  shift 2
  out="$fixtures/$case_name"
  mkdir -p "$out"
  status=0
  (cd "$fixtures" && env "$@" THRUST_REPORT=1 THRUST_REPORT_FORMAT=json \
    THRUST_REPORT_FILE="$out/report.jsonl" \
    $thrust -Awarnings -C debug-assertions=off --error-format=json \
    --crate-type bin --out-dir "$scratch" "$source" 2> "$out/stderr.jsonl") || status=$?
  if [ -f "$out/report.jsonl" ]; then
    sed -i "1s|\"root\":\"$fixtures\"|\"root\":\".\"|" "$out/report.jsonl"
  fi
  echo "$status" > "$out/exit"
  echo "$case_name: exit $status"
}

thrust="$*"
capture safe safe.rs
capture safe-split safe.rs THRUST_SPLIT=2 THRUST_CACHE_DIR="$scratch/cache"
capture unsafe unsafe.rs
capture split unsafe.rs THRUST_SPLIT=2 THRUST_CACHE_DIR="$scratch/cache"
capture unknown unknown.rs THRUST_SOLVER_TIMEOUT_SECS=2
capture unknown-split unknown.rs THRUST_SOLVER_TIMEOUT_SECS=2 THRUST_SPLIT=2
capture contracts contracts.rs
capture precondition precondition.rs
capture broken broken.rs
capture only-main safe.rs THRUST_VERIFY_ONLY=main
capture only-main-split safe.rs THRUST_VERIFY_ONLY=main THRUST_SPLIT=2
capture only-trusted trusted.rs THRUST_VERIFY_ONLY=bad
capture only-trusted-split trusted.rs THRUST_VERIFY_ONLY=bad THRUST_SPLIT=2
capture only-twin-split trusted.rs THRUST_VERIFY_ONLY=twin THRUST_SPLIT=2
capture only-nested nested.rs THRUST_VERIFY_ONLY=outer
capture only-nested-split nested.rs THRUST_VERIFY_ONLY=outer THRUST_SPLIT=2
