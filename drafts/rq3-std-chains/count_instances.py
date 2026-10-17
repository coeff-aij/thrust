#!/usr/bin/env python3
"""Count the instances of generic functions over iterators in a cargo build.

usage: count_instances.py program|crates MONO_DIR [--top N]

MONO_DIR holds one file per rustc run, `<crate name>.<pid>.txt`, its stdout under
`-Zprint-mono-items=yes`; `rustc-tee` next to this script writes them when it is the build's
RUSTC_WRAPPER with MONO_OUT=MONO_DIR. Build scripts are left out. `core::` and `alloc::` paths are
read as `std::`, the spelling of crates with std.

- program: over the whole build, an instance counted once however many crates print it:
  - adapter: per std adapter (Map, Filter, ...), the distinct types with an `Iterator` method;
  - consumer: per `Iterator` method that consumes the iterator (fold, collect, ...), its distinct
    instances over every Self type, default bodies and overrides together;
  - local: per generic function of a crate other than std, its distinct instances that take an
    iterator type among their generic arguments.
- crates: per crate, the adapter or consumer with the most instances that crate prints.
"""

import argparse
import collections
import os
import re
import statistics

ADAPTERS = ("Map", "Filter", "FilterMap", "Chain", "Zip", "Skip", "Take", "Enumerate", "Rev",
            "Cloned", "Copied", "Peekable", "Flatten", "FlatMap", "TakeWhile", "SkipWhile",
            "StepBy", "Fuse", "Inspect", "Scan", "MapWhile")
CONSUMERS = ("fold", "for_each", "count", "sum", "product", "collect", "any", "all", "find",
             "find_map", "position", "try_fold", "try_for_each", "max", "min", "max_by_key",
             "min_by_key", "max_by", "min_by", "last", "nth", "partition", "unzip", "cmp", "eq")
ITERATOR_ARG = re.compile(r"std::iter::|std::slice::Iter|IntoIter|std::ops::Range|"
                          r"std::str::(?:Chars|Split|Lines|Bytes|CharIndices)|"
                          r"hash_map::(?:Iter|Keys|Values)|btree_map::")


def normalize(path):
    return re.sub(r"\b(?:core|alloc)::", "std::", path)


def crate_items(mono_dir):
    """crate -> the set of mono fn items its rustc run printed."""
    out = collections.defaultdict(set)
    for name in os.listdir(mono_dir):
        crate = name.split(".")[0]
        if crate == "build_script_build":
            continue
        with open(os.path.join(mono_dir, name), errors="replace") as f:
            for line in f:
                m = re.match(r"MONO_ITEM fn (.*?) @@", line)
                if m:
                    out[crate].add(normalize(m.group(1)))
    return out


def split_top(path):
    """The text and the top-level `<...>` groups of a path, in order."""
    parts, depth, start, last = [], 0, 0, 0
    for i, ch in enumerate(path):
        if ch == "<":
            if depth == 0:
                parts.append(("text", path[last:i]))
                start = i
            depth += 1
        elif ch == ">" and depth:
            depth -= 1
            if depth == 0:
                parts.append(("group", path[start + 1:i]))
                last = i + 1
    parts.append(("text", path[last:]))
    return parts


def erase(path):
    return "".join(t if kind == "text" else "<..>" for kind, t in split_top(path))


def qualified_self(path):
    """(X, Tr, m) of `<X as Tr>::m...`, Tr with its generic arguments erased; None otherwise."""
    if not path.startswith("<"):
        return None
    parts = split_top(path)
    group, depth = parts[1][1], 0
    for i, ch in enumerate(group):
        depth += {"<": 1, ">": -1}.get(ch, 0)
        if depth == 0 and group.startswith(" as ", i):
            rest = parts[2][1] if len(parts) > 2 else ""
            method = re.match(r"::(\w+)", rest)
            return group[:i], erase(group[i + 4:]), method.group(1) if method else ""
    return None


def adapter_of(self_ty):
    m = re.match(r"std::iter::(?:adapters::(?:\w+::)*)?(\w+)<", self_ty)
    return m.group(1) if m and m.group(1) in ADAPTERS else None


def iterator_groups(items):
    """adapter -> its types, `Iterator::m` -> its instances, over a set of items."""
    adapters, consumers = collections.defaultdict(set), collections.defaultdict(set)
    for path in items:
        q = qualified_self(path)
        if not q or q[1] != "std::iter::Iterator":
            continue
        adapter = adapter_of(q[0])
        if adapter:
            adapters[adapter].add(q[0])
        if q[2] in CONSUMERS:
            consumers["Iterator::" + q[2]].add(path)
    return adapters, consumers


def local_groups(items):
    """function -> its instances with an iterator type among their generic arguments."""
    out = collections.defaultdict(set)
    for path in items:
        q = qualified_self(path)
        if path.startswith("std::") or "{shim" in path or (q and q[0].startswith("std::") and q[1].startswith("std::")):
            continue
        key = erase(path)
        if not key.startswith("<..>") and ITERATOR_ARG.search(path):
            out[key].add(path)
    return out


def summary(name, group, top):
    sizes = sorted((len(v) for v in group.values()), reverse=True)
    if not sizes:
        print(f"## {name}: none")
        return
    print(f"## {name}: {len(sizes)} functions, max {sizes[0]}, median {statistics.median(sizes)}")
    for key, v in sorted(group.items(), key=lambda kv: (-len(kv[1]), kv[0]))[:top]:
        print(f"{len(v):5d}  {key}")


def program(per_crate, top):
    items = set().union(*per_crate.values())
    adapters, consumers = iterator_groups(items)
    print(f"# {len(items)} distinct mono fn items")
    summary("adapter", adapters, top)
    summary("consumer", consumers, top)
    summary("local", local_groups(items), top)


def crates(per_crate, top):
    rows = []
    for crate, items in per_crate.items():
        groups = {**{"type " + k: v for k, v in iterator_groups(items)[0].items()},
                  **iterator_groups(items)[1]}
        if groups:
            key, v = max(groups.items(), key=lambda kv: len(kv[1]))
            rows.append((len(v), crate, key))
    rows.sort(reverse=True)
    print(f"# {len(rows)} crates, median of the per-crate maximum {statistics.median(r[0] for r in rows)}")
    for n, crate, key in rows[:top]:
        print(f"{n:5d}  {crate}  {key}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("mode", choices=("program", "crates"))
    ap.add_argument("mono_dir")
    ap.add_argument("--top", type=int, default=10)
    args = ap.parse_args()
    per_crate = crate_items(args.mono_dir)
    {"program": program, "crates": crates}[args.mode](per_crate, args.top)


if __name__ == "__main__":
    main()
