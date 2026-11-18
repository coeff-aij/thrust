#!/usr/bin/env python3
"""List existing functions similar to what is about to be added or changed.

Reads the rustdoc JSON of the crate; it builds nothing. Build the JSON first:

    cargo rustdoc --lib -- -Z unstable-options --output-format json --document-private-items

then, from the repository root:

    scripts/similar_functions.py QUERY...          # query terms, e.g. block requires precondition
    scripts/similar_functions.py --like PATH       # functions like an existing one, e.g. local_def::build_block_requires
    scripts/similar_functions.py --groups          # clusters of mutually similar functions
    scripts/similar_functions.py --list-inputs     # what would be read, without scoring

Similarity combines name tokens (snake_case split), doc-comment words, the types in the
signature and the body size taken from the span. Output is deterministic.
"""
import argparse
import itertools
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

DEFAULT_JSON = "target/doc/thrust.json"
WEIGHTS = {"name": 0.45, "doc": 0.15, "types": 0.30, "size": 0.10}
STOP_WORDS = {"the", "a", "an", "of", "to", "in", "is", "for", "and", "or", "with", "this", "that", "it", "self"}
NAME_PRECISION_WEIGHT = 0.2
GROUP_THRESHOLD = 0.6
MIN_GROUP_BODY_LINES = 5
CONSTRUCTOR_NAMES = {"new", "default"}


class Function:
    def __init__(self, item, owner):
        sig = item["inner"]["function"]["sig"]
        self.name = item["name"]
        self.file = item["span"]["filename"] if item["span"] else "?"
        self.line = item["span"]["begin"][0] if item["span"] else 0
        end = item["span"]["end"][0] if item["span"] else 0
        self.body_lines = end - self.line + 1
        self.module = module_of(self.file)
        self.owner = owner
        self.in_trait_impl = owner is not None and owner[1]
        self.name_tokens = name_tokens(self.name)
        self.path_tokens = set(itertools.chain.from_iterable(name_tokens(p) for p in self.module))
        self.doc_tokens = words(item.get("docs") or "")
        self.type_tokens = type_tokens([t for _, t in sig["inputs"]]) | type_tokens([sig["output"]])

    def label(self):
        owner = f"{self.owner[0]}::" if self.owner else ""
        return f"{'::'.join(self.module)}::{owner}{self.name}"

    def where(self):
        return f"{self.file}:{self.line}"


def module_of(filename):
    parts = Path(filename).with_suffix("").parts
    parts = parts[1:] if parts and parts[0] == "src" else parts
    parts = parts[:-1] if parts and parts[-1] in ("mod", "lib") else parts
    return tuple(parts)


def stem(word):
    for suffix in ("ies", "es", "s"):
        if len(word) > len(suffix) + 2 and word.endswith(suffix):
            return word[: -len(suffix)] + ("y" if suffix == "ies" else "")
    return word


def name_tokens(name):
    return {stem(t) for t in name.lower().split("_") if t}


def words(text):
    return {stem(w) for w in re.findall(r"[a-z]{3,}", text.lower())} - STOP_WORDS


def type_tokens(types):
    tokens = set()
    for t in types:
        collect_type_names(t, tokens)
    return tokens


def collect_type_names(node, tokens):
    if isinstance(node, dict):
        for key, value in node.items():
            if key in ("path", "generic", "primitive") and isinstance(value, str):
                tokens.add(value.split("::")[-1])
            else:
                collect_type_names(value, tokens)
    elif isinstance(node, list):
        for value in node:
            collect_type_names(value, tokens)


def load_functions(json_path):
    data = json.loads(Path(json_path).read_text())
    index = data["index"]
    owners = {}
    for item in index.values():
        impl = item["inner"].get("impl") if isinstance(item["inner"], dict) else None
        if impl is None:
            continue
        type_name = impl["for"].get("resolved_path", {}).get("path", "?").split("::")[-1]
        for child in impl["items"]:
            owners[child] = (type_name, impl["trait"] is not None)
    functions = []
    for item_id, item in index.items():
        inner = item["inner"]
        if item["crate_id"] != 0 or not isinstance(inner, dict) or "function" not in inner:
            continue
        if not inner["function"]["has_body"] or item["span"] is None:
            continue
        functions.append(Function(item, owners.get(int(item_id))))
    functions.sort(key=lambda f: (f.file, f.line, f.name))
    return data, drop_macro_copies(functions)


def drop_macro_copies(functions):
    """Functions a macro generates share one span; keep the first of each span."""
    seen = set()
    kept = []
    for f in functions:
        if (f.file, f.line, f.body_lines) in seen:
            continue
        seen.add((f.file, f.line, f.body_lines))
        kept.append(f)
    return kept


def jaccard(a, b):
    return len(a & b) / len(a | b) if a | b else 0.0


def similarity(a, b):
    size = min(a.body_lines, b.body_lines) / max(a.body_lines, b.body_lines)
    return (
        WEIGHTS["name"] * jaccard(a.name_tokens, b.name_tokens)
        + WEIGHTS["doc"] * jaccard(a.doc_tokens, b.doc_tokens)
        + WEIGHTS["types"] * jaccard(a.type_tokens, b.type_tokens)
        + WEIGHTS["size"] * size
    )


def query_score(terms, f):
    hits = 0.0
    name_hits = 0
    for term in terms:
        if term in f.name_tokens:
            hits += 1.0
            name_hits += 1
        elif term in f.doc_tokens or term in f.path_tokens:
            hits += 0.5
    precision = name_hits / len(f.name_tokens) if f.name_tokens else 0.0
    return hits / len(terms) + NAME_PRECISION_WEIGHT * precision


def print_module_tree(functions, hits):
    counts = defaultdict(int)
    for f in functions:
        for depth in range(1, len(f.module) + 1):
            counts[f.module[:depth]] += 1
    hit_modules = {f.module for f in hits}
    shown = set()
    for module in hit_modules:
        for depth in range(1, len(module) + 1):
            shown.add(module[:depth])
        shown.update(m for m in counts if m[:-1] == module)
    print("module tree (functions with a body; * = holds a hit)")
    for module in sorted(shown):
        mark = " *" if module in hit_modules else ""
        print(f"{'  ' * (len(module) - 1)}{module[-1]}  [{counts[module]}]{mark}")
    print()


def print_ranked(ranked, limit):
    for score, f in ranked[:limit]:
        print(f"{score:5.2f}  {f.label()}  ({f.body_lines} lines)  {f.where()}")


def find_like(functions, path):
    matches = [f for f in functions if f.label().endswith(path)]
    if not matches:
        sys.exit(f"no function ends with {path}")
    if len(matches) > 1:
        sys.exit("ambiguous:\n" + "\n".join(f"  {f.label()}  {f.where()}" for f in matches))
    return matches[0]


def run_query(functions, args):
    if args.like:
        target = find_like(functions, args.like)
        scored = [(similarity(target, f), f) for f in functions if f is not target]
        print(f"functions like {target.label()}  {target.where()}\n")
    else:
        terms = sorted({stem(t) for q in args.query for t in re.split(r"[^a-zA-Z]+", q.lower()) if t} - STOP_WORDS)
        scored = [(query_score(terms, f), f) for f in functions]
        print(f"functions matching terms {terms}\n")
    ranked = [(s, f) for s, f in scored if s > 0]
    ranked.sort(key=lambda sf: (-sf[0], sf[1].file, sf[1].line))
    print_module_tree(functions, [f for _, f in ranked[: args.limit]])
    print_ranked(ranked, args.limit)


def groups(functions):
    candidates = [f for f in functions if not f.in_trait_impl and f.body_lines >= MIN_GROUP_BODY_LINES and f.name not in CONSTRUCTOR_NAMES]
    parent = list(range(len(candidates)))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    by_token = defaultdict(list)
    for i, f in enumerate(candidates):
        for token in f.name_tokens:
            by_token[token].append(i)
    pairs = {(i, j) for members in by_token.values() for i, j in itertools.combinations(members, 2)}
    for i, j in sorted(pairs):
        if similarity(candidates[i], candidates[j]) >= GROUP_THRESHOLD:
            parent[find(j)] = find(i)
    clusters = defaultdict(list)
    for i, f in enumerate(candidates):
        clusters[find(i)].append(f)
    return [c for c in clusters.values() if len(c) >= 2]


def run_groups(functions, args):
    clusters = sorted(groups(functions), key=lambda c: (-len(c), c[0].file, c[0].line))
    print(f"{len(clusters)} clusters of functions with similarity >= {GROUP_THRESHOLD} (trait impls, constructors named new/default and bodies under {MIN_GROUP_BODY_LINES} lines left out)\n")
    for cluster in clusters[: args.limit]:
        print(f"cluster of {len(cluster)}")
        for f in cluster:
            print(f"  {f.where()}  {f.label()}  ({f.body_lines} lines)")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("query", nargs="*", help="terms describing what is about to be added")
    parser.add_argument("--like", help="path suffix of an existing function, e.g. local_def::build_block_requires")
    parser.add_argument("--groups", action="store_true", help="list clusters of mutually similar functions")
    parser.add_argument("--list-inputs", action="store_true", help="print what would be read and exit")
    parser.add_argument("--json", default=DEFAULT_JSON, help=f"rustdoc JSON (default {DEFAULT_JSON})")
    parser.add_argument("--limit", type=int, default=15, help="rows or clusters to print")
    args = parser.parse_args()
    if not Path(args.json).exists():
        sys.exit(f"{args.json} not found; build it with the cargo rustdoc command in --help")
    data, functions = load_functions(args.json)
    if args.list_inputs:
        print(f"{args.json}: format_version {data['format_version']}, {len(functions)} functions with a body, "
              f"{len({f.file for f in functions})} files")
        return
    if args.groups:
        run_groups(functions, args)
    elif args.like or args.query:
        run_query(functions, args)
    else:
        parser.error("give query terms, --like, --groups or --list-inputs")


if __name__ == "__main__":
    main()
