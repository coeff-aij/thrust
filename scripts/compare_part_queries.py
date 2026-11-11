#!/usr/bin/env python3
"""Check that each part query one Thrust binary writes is the one another writes with some
declarations left out and its forall sorts and quantified variables renamed one-to-one: what
`src/chc/standalone.rs` claims, checked by a reading of its own.

usage: scripts/compare_part_queries.py [--parse-with-z3] <before dir> <after dir>

Each dir holds `thrust_output_part<i>.smt2` files (`THRUST_SPLIT` with `THRUST_OUTPUT_DIR`), at
any depth, paired by their path under the dir; thrust-research's `scripts/emission_diff.py`
writes such dirs for every ui test. For each pair:

- the commands after are matched to commands before, equal piece by piece (a symbol split at
  `<`, `-` and `>`) up to one one-to-one renaming that maps forall sorts `a<n>` to forall sorts,
  each `default_a<n>` as its `a<n>`, and quantified variables `q$<n>` to quantified variables;
- they keep their order, and every command that is not a declaration (an assertion) is matched;
- no command kept names a symbol that a command left out declares.

`--parse-with-z3` also gives each query after that has no forall sort, sequence or universal
function to `z3` without `(check-sat)`, which parses it and reports any error. Prints the pairs
that fail and the bytes before and after; exits 1 if any fails.
"""

import os, re, subprocess, sys

DECL = {"declare-sort", "declare-forall-sort", "define-sort", "declare-const", "define-const",
        "declare-fun", "declare-forall-fun", "declare-dep-exists-fun", "define-fun",
        "define-fun-rec"}
RENAMED = re.compile(r"^(default_)?(a\d+)$|^(q\$\d+)$")
TOKEN = re.compile(r'\s+|;[^\n]*|"(?:[^"]|"")*"|\|[^|]*\||[()]|[^\s()";|]+')
PIECE = re.compile(r"[<>-]")


def commands(text):
    """Top-level commands as (token list without comments and spaces, byte length)."""
    out, depth, cur, start = [], 0, [], 0
    for m in TOKEN.finditer(text):
        t = m.group()
        if t[0].isspace() or t[0] == ';':
            continue
        if t == '(':
            if depth == 0:
                cur, start = [], m.start()
            depth += 1
        cur.append(t)
        if t == ')':
            depth -= 1
            if depth == 0:
                out.append((cur, m.end() - start))
    return out


def parse(tokens):
    stack = [[]]
    for t in tokens:
        if t == '(':
            stack.append([])
        elif t == ')':
            x = stack.pop()
            stack[-1].append(x)
        else:
            stack[-1].append(t)
    return stack[0][0]


def declared(tokens):
    s = parse(tokens)
    head = s[0] if s and isinstance(s[0], str) else None
    if head in DECL and isinstance(s[1], str):
        return {s[1]}
    if head == "declare-datatypes":
        names = {d[0] for d in s[1]}
        for decl in s[2]:
            ctors = decl[2] if decl and decl[0] == "par" else decl
            for c in ctors:
                if isinstance(c, str):
                    names.add(c)
                else:
                    names.add(c[0])
                    names.update(sel[0] for sel in c[1:])
        return names
    return set()


def is_kept_always(tokens):
    s = parse(tokens)
    head = s[0] if s and isinstance(s[0], str) else None
    return head not in DECL and head != "declare-datatypes" and not (
        head == "set-info" and len(s) > 1 and s[1] == ":candidates")


def names(tokens):
    out = set()
    for t in tokens:
        if t in "()" or t.startswith('"'):
            continue
        out.add(t)
        out.update(p for p in PIECE.split(t) if p)
    return out


def pieces(tokens):
    out = []
    for t in tokens:
        out.extend(p for p in re.split(r"([<>-])", t) if p)
    return out


def renamed(piece):
    """(prefix, name) of a piece the renaming may change, or None."""
    m = RENAMED.match(piece)
    if not m:
        return None
    return (m.group(1) or "", m.group(2) or m.group(3))


def match(new, old, fwd, back):
    """Whether new equals old under fwd (new->old) extended consistently; extends fwd/back."""
    a, b = pieces(new), pieces(old)
    if len(a) != len(b):
        return False
    add = {}
    for x, y in zip(a, b):
        rx, ry = renamed(x), renamed(y)
        if rx is None or ry is None:
            if x != y:
                return False
            continue
        if rx[0] != ry[0] or rx[1][0] != ry[1][0]:
            return False
        x, y = rx[1], ry[1]
        m = fwd.get(x, add.get(x))
        if m is None:
            if y in back or y in add.values():
                return False
            add[x] = y
        elif m != y:
            return False
    fwd.update(add)
    back.update({v: k for k, v in add.items()})
    return True


Z3_UNREAD = re.compile(r"declare-forall-|declare-dep-exists-fun|\bSeq\b")


def z3_parse_error(text):
    if Z3_UNREAD.search(text):
        return None
    out = subprocess.run(["z3", "-in", "-smt2"], input=text, capture_output=True, text=True).stdout
    return out.strip() if "(error" in out else None


def check(old_text, new_text):
    old, new = commands(old_text), commands(new_text)
    fwd, back, matched = {}, {}, set()
    sorts = lambda cs: [t[2] for t, _ in cs if t[1] == "declare-forall-sort"]
    shape = lambda t: tuple("#" if RENAMED.match(p) else p for p in pieces(t))
    by_shape = {}
    for i, (t, _) in enumerate(old):
        if t[1] != "declare-forall-sort":
            by_shape.setdefault(shape(t), []).append(i)
    todo = [(k, t, by_shape.get(shape(t), [])) for k, (t, _) in enumerate(new)
            if t[1] != "declare-forall-sort"]
    to_old = {}
    for k, toks, cands in sorted(todo, key=lambda x: len(x[2])):
        for i in cands:
            if i not in matched and match(toks, old[i][0], fwd, back):
                matched.add(i)
                to_old[k] = i
                break
        else:
            return "a new command matches no old one: " + " ".join(toks[:3])
    olds = [to_old[k] for k in sorted(to_old)]
    if olds != sorted(olds):
        return "the commands kept are in another order"
    kept_sorts = [fwd[s] for s in sorts(new) if s in fwd]
    if len(kept_sorts) != len(sorts(new)):
        return "a new forall sort is named by no other command"
    matched.update(i for i, (t, _) in enumerate(old) if t[1] == "declare-forall-sort" and t[2] in kept_sorts)
    dropped = [i for i in range(len(old)) if i not in matched]
    for i in dropped:
        if is_kept_always(old[i][0]):
            return "an old command that is always kept is left out: " + " ".join(old[i][0][:4])
    gone = set().union(*(declared(old[i][0]) for i in dropped)) if dropped else set()
    for i in matched:
        hit = names(old[i][0]) & gone
        if hit:
            return "a kept command names a symbol left out: " + sorted(hit)[0]
    return None


def files(root):
    out = {}
    for d, _, fs in os.walk(root):
        for f in fs:
            if f.startswith("thrust_output_part") and f.endswith(".smt2"):
                p = os.path.join(d, f)
                out[os.path.relpath(p, root)] = p
    return out


def main():
    args = sys.argv[1:]
    parse = "--parse-with-z3" in args
    args = [a for a in args if a != "--parse-with-z3"]
    old, new = files(args[0]), files(args[1])
    bad = 0
    if set(old) != set(new):
        bad += 1
        print("different part files:", sorted(set(old) ^ set(new))[:5])
    ob = nb = parsed = 0
    for rel in sorted(set(old) & set(new)):
        o, n = open(old[rel]).read(), open(new[rel]).read()
        ob += len(o.encode())
        nb += len(n.encode())
        err = check(o, n)
        if err is None and parse:
            body = n.replace("(check-sat)", "")
            err = z3_parse_error(body)
            parsed += not Z3_UNREAD.search(body)
        if err:
            bad += 1
            print(rel, err)
    print(f"parts {len(set(old) & set(new))} failing {bad} parsed by z3 {parsed} "
          f"bytes {ob} -> {nb} ({nb / max(ob, 1):.1%})")
    sys.exit(1 if bad else 0)


main()
