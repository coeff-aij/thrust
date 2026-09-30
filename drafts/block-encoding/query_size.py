#!/usr/bin/env python3
"""Size measures of a CHC query emitted by Thrust (THRUST_OUTPUT_DIR/thrust_output.smt2).

For each file: bytes without comments, clauses (asserts), predicates (declare-fun and
declare-dep-exists-fun), predicate arity as declared and as scalar leaves once tuple
datatypes are flattened, and the variables each clause quantifies at its top-level forall,
again as declared and as scalar leaves.

A tuple datatype (one constructor) counts as the sum of its fields; an enum, a Seq, Int
and Bool count as one leaf.

--list prints the files and the measures it would compute, without reading them.
--preds FILE prints each predicate with its arity and leaves.
"""
import re
import sys

TOKEN = re.compile(r'\(|\)|\|[^|]*\||[^\s()]+')


def strip_comments(text):
    return '\n'.join(line for line in text.split('\n') if not line.lstrip().startswith(';'))


def parse_all(text):
    stack = [[]]
    for token in TOKEN.findall(text):
        if token == '(':
            stack.append([])
        elif token == ')':
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(token)
    assert len(stack) == 1
    return stack[0]


def datatype_fields(commands):
    fields = {}
    for cmd in commands:
        if cmd[0] != 'declare-datatypes':
            continue
        for (name, _), decl in zip(cmd[1], cmd[2]):
            ctors = decl[2] if decl[0] == 'par' else decl
            fields[name] = [sel[1] for sel in ctors[0][1:]] if len(ctors) == 1 else None
    return fields


def leaves(sort, fields, depth=0):
    if isinstance(sort, list) or depth > 50:
        return 1
    field_sorts = fields.get(sort)
    if not field_sorts:
        return 1
    return sum(leaves(s, fields, depth + 1) for s in field_sorts)


def predicates(commands):
    for cmd in commands:
        if cmd[0] == 'declare-fun':
            yield cmd[1], cmd[2]
        elif cmd[0] == 'declare-dep-exists-fun':
            yield cmd[1], cmd[3]


def clause_binders(cmd):
    body = cmd[1]
    if isinstance(body, list) and body and body[0] == 'forall':
        return [sort for _, sort in body[1]]
    return []


def stats(values):
    if not values:
        return 0, 0.0
    return max(values), sum(values) / len(values)


def measure(path):
    raw = open(path).read()
    text = strip_comments(raw)
    commands = parse_all(text)
    fields = datatype_fields(commands)
    preds = list(predicates(commands))
    asserts = [c for c in commands if c[0] == 'assert']
    arity = [len(args) for _, args in preds]
    arity_leaves = [sum(leaves(s, fields) for s in args) for _, args in preds]
    qvars = [len(clause_binders(c)) for c in asserts]
    qvar_leaves = [sum(leaves(s, fields) for s in clause_binders(c)) for c in asserts]
    return {
        'bytes': len(text.encode()),
        'bytes_raw': len(raw.encode()),
        'clauses': len(asserts),
        'preds': len(preds),
        'arity': stats(arity),
        'arity_leaves': stats(arity_leaves),
        'qvars': stats(qvars),
        'qvar_leaves': stats(qvar_leaves),
    }


HEADER = ('file', 'bytes', 'clauses', 'preds', 'arity max/avg', 'arity leaves max/avg',
          'qvars max/avg', 'qvar leaves max/avg')


def row(name, m):
    pair = lambda p: f'{p[0]} / {p[1]:.1f}'
    return (name, str(m['bytes']), str(m['clauses']), str(m['preds']), pair(m['arity']),
            pair(m['arity_leaves']), pair(m['qvars']), pair(m['qvar_leaves']))


def print_table(paths):
    print('| ' + ' | '.join(HEADER) + ' |')
    print('|' + ' --- |' * len(HEADER))
    for path in paths:
        print('| ' + ' | '.join(row(path, measure(path))) + ' |')


def print_preds(path):
    commands = parse_all(strip_comments(open(path).read()))
    fields = datatype_fields(commands)
    for name, args in predicates(commands):
        print(name, len(args), sum(leaves(s, fields) for s in args))


def main(argv):
    if argv[:1] == ['--list']:
        for path in argv[1:]:
            print(path, ':', ', '.join(HEADER[1:]))
        return
    if argv[:1] == ['--preds']:
        print_preds(argv[1])
        return
    print_table(argv)


if __name__ == '__main__':
    main(sys.argv[1:])
