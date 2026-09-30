#!/bin/bash
# Solves one emitted query with PCSat's default chain in a container limited to 2 CPUs and 3 GB.
# Usage: solve.sh FILE.smt2 [TIMEOUT_SECS] [IMAGE]
# Prints the file, the solver's verdict line ("timeout" at the limit), seconds, the exit code
# (137: killed for memory).
set -u
file=$(realpath "$1") limit=${2:-300} image=${3:-coar:804d76744}
dir=$(dirname "$file") name=$(basename "$file")
log=$(mktemp -p "$dir" solve.XXXX.log)
container=$(docker create --cpus=2 --memory=3g --memory-swap=3g -v "$dir:/mnt:ro" -w /root/coar \
  "$image" main.exe -c ./config/solver/pcsat_tbq_ar.json -p pcsp "/mnt/$name")
start=$(date +%s.%N)
timeout "$limit" docker start --attach "$container" > "$log" 2>&1
code=$?
end=$(date +%s.%N)
docker rm --force "$container" > /dev/null
verdict=$(grep -m1 -E "^(sat|unsat|unknown|timeout)" "$log" || tail -1 "$log")
[ "$code" = 124 ] && verdict=timeout
printf '%s %s %.1f %s\n' "$1" "${verdict:-none}" "$(echo "$end - $start" | bc)" "$code"
