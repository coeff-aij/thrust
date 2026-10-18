#!/bin/sh
# Captures the outputs the cargo tests read: for each case, cargo's JSON messages, its exit status
# and the crates' reports of one `cargo check` of test/fixtures/cargo/workspace through
# bin/thrust-rustc-cargo with z3, and the workspace's `cargo metadata`. The cases run one after
# the other on one target directory and one report directory, as the extension's checks do, so
# a crate cargo finds fresh keeps its report; each case's `reports` is that directory after it.
#
# Usage: test/capture-cargo.sh <thrust-rustc command...>
#   e.g. test/capture-cargo.sh /path/to/thrust/target/debug/thrust-rustc
# cargo is run as `cargo +nightly-2025-09-08`, which also gives thrust-rustc its libraries. The
# workspace's directory is written as /workspace and the scratch directory as /scratch, so the
# fixtures do not name the machine.
set -eu
[ $# -ge 1 ] || { echo "usage: $0 <thrust-rustc command...>" >&2; exit 2; }
here=$(cd "$(dirname "$0")" && pwd)
fixtures="$here/fixtures/cargo"
workspace="$fixtures/workspace"
wrapper=$(cd "$here/../bin" && pwd)/thrust-rustc-cargo
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
sep=$(printf '\037')

# The words of the arguments joined by the separator the wrapper splits at.
joined() {
  out=
  for word in "$@"; do
    out="${out:+$out$sep}$word"
  done
  printf '%s' "$out"
}

anonymize() {
  sed -i -e "s|$workspace|/workspace|g" -e "s|$scratch|/scratch|g" "$@"
}

# capture <case> [VAR=value...] -- <cargo check arguments...>
capture() {
  case_name=$1
  shift
  vars=
  while [ "$1" != "--" ]; do
    vars="$vars $1"
    shift
  done
  shift
  out="$fixtures/$case_name"
  rm -rf "$out"
  mkdir -p "$out/reports" "$scratch/reports"
  status=0
  # shellcheck disable=SC2086
  env THRUST_VERIFY_ONLY= $vars RUSTC="$wrapper" RUSTC_WRAPPER= RUSTC_WORKSPACE_WRAPPER= \
    CARGO_TARGET_DIR="$scratch/target" THRUST_VSCODE_COMMAND="$command" \
    THRUST_VSCODE_ARGS="$(joined -Awarnings -C debug-assertions=off)" \
    THRUST_VSCODE_REPORT_DIR="$scratch/reports" THRUST_REPORT=1 THRUST_REPORT_FORMAT=json \
    cargo +nightly-2025-09-08 check --message-format=json \
    --manifest-path "$workspace/Cargo.toml" "$@" > "$out/stdout.jsonl" 2> "$scratch/stderr" ||
    status=$?
  cp "$scratch"/reports/*.jsonl "$out/reports/"
  anonymize "$out/stdout.jsonl" "$out"/reports/*.jsonl
  echo "$status" > "$out/exit"
  echo "$case_name: exit $status, reports: $(ls "$out/reports" | tr '\n' ' ')"
}

command=$(joined "$@")
cargo +nightly-2025-09-08 metadata --no-deps --format-version 1 \
  --manifest-path "$workspace/Cargo.toml" > "$fixtures/metadata.json"
anonymize "$fixtures/metadata.json"
capture check -- --workspace --keep-going
capture check-again -- --workspace --keep-going
capture check-split THRUST_SPLIT=2 THRUST_CACHE_DIR="$scratch/cache" -- --workspace --keep-going
capture only THRUST_VSCODE_VERIFY_ONLY=Pair::scale THRUST_VSCODE_VERIFY_CRATE=arith.lib -- -p arith --lib
capture only-bin THRUST_VSCODE_VERIFY_ONLY=helper THRUST_VSCODE_VERIFY_CRATE=both.bin -- -p both --bin both
