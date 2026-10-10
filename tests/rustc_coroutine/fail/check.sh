#!/bin/sh
# Regenerates each fail root under tests/ui/fail/rustc_coroutine/ from its pass root under
# tests/ui/pass/rustc_coroutine/ and the patch next to this script, and reports every fail root
# that differs from what the patch gives. `--write` replaces the fail roots with the regenerated
# files. Run from the repository root or anywhere; paths are resolved from this script.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
pass="$repo/tests/ui/pass/rustc_coroutine"
fail="$repo/tests/ui/fail/rustc_coroutine"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

write=0
if [ "${1:-}" = "--write" ]; then
    write=1
fi

status=0
for patch in "$here"/*.patch; do
    name=$(basename "$patch" .patch)
    if ! patch --quiet -o "$tmp/$name.rs" "$pass/$name.rs" "$patch" > "$tmp/$name.log" 2>&1; then
        echo "$name: the patch no longer applies to the pass root"
        cat "$tmp/$name.log"
        status=1
        continue
    fi
    if cmp -s "$tmp/$name.rs" "$fail/$name.rs"; then
        echo "$name: up to date"
        continue
    fi
    if [ "$write" -eq 1 ]; then
        cp "$tmp/$name.rs" "$fail/$name.rs"
        echo "$name: regenerated"
        continue
    fi
    echo "$name: drift"
    diff -u "$fail/$name.rs" "$tmp/$name.rs" || true
    status=1
done
exit "$status"
