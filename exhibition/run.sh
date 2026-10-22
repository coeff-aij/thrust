#!/bin/bash
# Verifies one file with Thrust and PCSat and shows the report: the loop invariants Thrust
# infers and, when verification fails, the obligation PCSat refutes.
# usage: ./run.sh <file.rs>

root=$(cd "$(dirname "$0")/.." && pwd)

cd "$(dirname "$0")"
THRUST_REPORT=1 \
THRUST_SOLVER="$root/tests/thrust-pcsat-model-standin" \
THRUST_PCSAT_TRACE="$root/tests/thrust-pcsat-trace-wrapper" \
    cargo run -q --manifest-path "$root/Cargo.toml" -- \
    --edition 2021 -A dead_code -C debug-assertions=off --out-dir "$root/target/exhibition" "$1"
