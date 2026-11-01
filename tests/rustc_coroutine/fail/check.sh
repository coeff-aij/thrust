#!/bin/sh
# Regenerates each fail root under tests/ui/fail/rustc_coroutine/ from its pass root under
# tests/ui/pass/rustc_coroutine/ and the patch next to this script, and reports every fail root
# that differs from what the patch gives. A twin that mutates the module tree has a second patch,
# `<name>.tree.patch`, against one crate of tests/rustc_coroutine/compiler/ (paths relative to
# `compiler/`); the mutated copy of that crate is regenerated and checked under
# tests/rustc_coroutine/fail/mutants/<name>/. `--write` replaces the fail roots and the mutant
# trees with the regenerated ones. Run from the repository root or anywhere; paths are resolved
# from this script.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
pass="$repo/tests/ui/pass/rustc_coroutine"
fail="$repo/tests/ui/fail/rustc_coroutine"
compiler="$repo/tests/rustc_coroutine/compiler"
mutants="$here/mutants"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

write=0
if [ "${1:-}" = "--write" ]; then
    write=1
fi

# check_root <name>: the fail root the root patch gives.
check_root() {
    name=$1
    if ! patch --quiet -o "$tmp/$name.rs" "$pass/$name.rs" "$here/$name.patch" > "$tmp/$name.log" 2>&1; then
        echo "$name: the patch no longer applies to the pass root"
        cat "$tmp/$name.log"
        return 1
    fi
    if cmp -s "$tmp/$name.rs" "$fail/$name.rs"; then
        echo "$name: up to date"
        return 0
    fi
    if [ "$write" -eq 1 ]; then
        cp "$tmp/$name.rs" "$fail/$name.rs"
        echo "$name: regenerated"
        return 0
    fi
    echo "$name: drift"
    diff -u "$fail/$name.rs" "$tmp/$name.rs" || true
    return 1
}

# check_tree <name>: the mutated crate the tree patch gives.
check_tree() {
    name=$1
    patch_file="$here/$name.tree.patch"
    crate=$(sed -n 's|^--- \([^/]*\)/.*|\1|p' "$patch_file" | head -n 1)
    mkdir -p "$tmp/$name"
    cp -r "$compiler/$crate" "$tmp/$name/$crate"
    if ! patch --quiet -p0 -d "$tmp/$name" < "$patch_file" > "$tmp/$name.tree.log" 2>&1; then
        echo "$name tree: the patch no longer applies to compiler/$crate"
        cat "$tmp/$name.tree.log"
        return 1
    fi
    if diff -r "$tmp/$name/$crate" "$mutants/$name/$crate" > /dev/null 2>&1; then
        echo "$name tree: up to date"
        return 0
    fi
    if [ "$write" -eq 1 ]; then
        rm -rf "$mutants/$name"
        mkdir -p "$mutants/$name"
        cp -r "$tmp/$name/$crate" "$mutants/$name/$crate"
        echo "$name tree: regenerated"
        return 0
    fi
    echo "$name tree: drift"
    diff -ru "$mutants/$name/$crate" "$tmp/$name/$crate" || true
    return 1
}

status=0
for patch_file in "$here"/*.patch; do
    name=$(basename "$patch_file" .patch)
    case "$name" in
        *.tree) continue ;;
    esac
    check_root "$name" || status=1
    if [ -f "$here/$name.tree.patch" ]; then
        check_tree "$name" || status=1
    fi
done
exit "$status"
