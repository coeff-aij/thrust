#!/bin/bash
# Emits the query Thrust builds for one file without solving it.
# Usage: emit.sh THRUST_TREE FILE.rs OUT_DIR [EDITION]
# THRUST_SOLVER=true is a command other than z3, so the query takes the form the PCSat tests
# use (declare-dep-exists-fun); `true` prints no verdict, so the run ends in NoVerdict.
# Other THRUST_* variables (THRUST_TRY_SPECS) are passed through from the caller.
set -eu
tree=$1 file=$2 out=$3 edition=${4:-2021}
mkdir -p "$out"
LD_LIBRARY_PATH=$(cd "$tree" && rustc --print sysroot)/lib THRUST_SOLVER=true THRUST_OUTPUT_DIR="$out" \
  "$tree/target/debug/thrust-rustc" --edition "$edition" -A unused -Adead_code \
  -C debug-assertions=off --out-dir "$out" "$file" > "$out/frontend.log" 2>&1 || true
grep -o "verification error: [A-Za-z]*" "$out/frontend.log" | head -1 || echo "no verification line"
