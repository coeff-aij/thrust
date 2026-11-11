#!/bin/bash
# Runs each case below with thrust-rustc and PCSat, from the repository root as the ui harness
# does, and prints one line per case: the exit status, whether the solver reported `Unsat`, and
# how many "generic def at an instance" lines of the analysis log say `analyze_body=true` (the
# generic's body analysed again at that instance).
# A case is <file>[:<THRUST_VERIFY_ONLY>]: a file of this directory without `.rs`, or a path from
# the repository root. -n prints the commands and runs nothing.
# usage: run.sh [-n] [case...]; env: THRUST_RUSTC, COAR_IMAGE (a CoAR image, never coar:latest)
set -uo pipefail
dry=0
if [ "${1:-}" = "-n" ]; then dry=1; shift; fi
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
binary=${THRUST_RUSTC:?the thrust-rustc binary}
image=${COAR_IMAGE:?a CoAR image}
cases=("$@")
if [ ${#cases[@]} -eq 0 ]; then
  cases=(e1 e2 e5 e3 e4 e6 v1 v1:caller v1:g v1_m1 v1_m1:caller v1_m1:g
    tests/ui/fail/verify_only/uncontracted_under_unselected.rs
    tests/ui/fail/verify_only/uncontracted_under_unselected.rs:main,g)
fi
out="<a temporary directory>"
[ "$dry" -eq 1 ] || out=$(mktemp -d)
sysroot=$(cd "$(dirname "$binary")/../.." && rustc --print sysroot)

run_case() {
  local file=${1%%:*} select=
  [[ $file == */* ]] || file=drafts/generic-instance-designs/$file.rs
  [[ $1 == *:* ]] && select=${1#*:}
  local envs=(COAR_IMAGE=$image THRUST_SOLVER=tests/thrust-pcsat-wrapper RUST_LOG=thrust::analyze=info)
  [ -n "$select" ] && envs+=(THRUST_VERIFY_ONLY=$select)
  local cmd=(env "${envs[@]}" LD_LIBRARY_PATH=$sysroot/lib "$binary" -Awarnings
    -C debug-assertions=off --edition 2021 -o "$out/a.out" "$file")
  if [ "$dry" -eq 1 ]; then echo "cd $root && ${cmd[*]}"; return; fi
  local name=${1//\//_}
  local log=$out/${name//:/_}.log
  (cd "$root" && "${cmd[@]}") > "$log" 2>&1
  local status=$?
  local unsat=no
  grep -q "Unsat" "$log" && unsat=yes
  echo "$1 status=$status unsat=$unsat per_instance=$(sed 's/\x1b\[[0-9;]*m//g' "$log" | grep 'generic def at an instance' | grep -c 'analyze_body=true') log=$log"
}

for c in "${cases[@]}"; do run_case "$c"; done
