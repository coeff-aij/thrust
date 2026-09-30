#!/usr/bin/env python3
"""Generates a struct with N fields and a derived PartialEq, and a main that asserts two
equal values are equal.

Usage: gen_wide_eq.py KIND N [--fail]

KIND is `mix` (fields cycle u64, usize, a 3-variant enum and a 2-field struct; at N = 30
this is fptprove's mix30_sat.rs) or `u64` (every field u64). With --fail the last field of
the second value differs, so the assertion fails.
"""
import sys

MIX = [('u64', '1', '9'), ('usize', '2', '9'), ('E', 'E::A', 'E::B'),
       ('Inner', 'Inner { x: 1, y: 2 }', 'Inner { x: 1, y: 9 }')]
U64 = [('u64', '1', '9')]


def field_kinds(kind, n):
    cycle = MIX if kind == 'mix' else U64
    return [cycle[i % len(cycle)] for i in range(n)]


def value(fields, broken):
    lines = []
    for i, (_, same, other) in enumerate(fields):
        v = other if broken and i == len(fields) - 1 else same
        lines.append(f'        f{i}: {v},')
    return '\n'.join(lines)


def program(kind, n, fail):
    fields = field_kinds(kind, n)
    out = []
    if kind == 'mix':
        out.append('#[derive(PartialEq)] pub enum E { A, B, C }')
        out.append('#[derive(PartialEq)] pub struct Inner { pub x: u64, pub y: u64 }')
    out.append('#[derive(PartialEq)]')
    out.append('pub struct S {')
    out.extend(f'    pub f{i}: {ty},' for i, (ty, _, _) in enumerate(fields))
    out.append('}')
    out.append('fn main() {')
    out.append('    let a: u64 = 1;')
    out.append('    let s = S {')
    out.append(value(fields, False))
    out.append('    };')
    out.append('    let t = S {')
    out.append(value(fields, fail))
    out.append('    };')
    out.append('    assert!(s == t);')
    out.append('    let _ = a;')
    out.append('}')
    return '\n'.join(out) + '\n'


def main(argv):
    kind, n = argv[0], int(argv[1])
    fail = '--fail' in argv[2:]
    sys.stdout.write(program(kind, n, fail))


if __name__ == '__main__':
    main(sys.argv[1:])
