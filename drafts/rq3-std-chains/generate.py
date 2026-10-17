#!/usr/bin/env python3
"""Generate the std-chain inputs of RQ3: one generic consumer over `I: IteratorSpec`, called at k
distinct std adapter chains.

usage: generate.py [-n] OUT CONSUMER K...

Each (CONSUMER, K) gives `OUT/<consumer>_k<K>_pass.rs` and its fail twin `..._fail.rs`, in which
the consumer's body is broken, and OUT/runs.csv lists both sides of every program verified once
(`generic`) and per instance (`per_instance`, `THRUST_PER_INSTANCE_GENERICS=1`), one row per run
with the columns id, setting, side, expect, file and env. Function `use_j` calls the consumer at the
j-th chain of `chains(K)`, so the K chains are K distinct types. -n prints the chains of every
program and writes nothing.
"""

import argparse
import os

INTS = ("i64", "i32", "i16", "i8", "isize", "u64", "u32", "u16", "u8", "usize")

HEADER = """//@{expectation}
//@compile-flags: -C debug-assertions=off -A unused-imports
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::{{Mut, Seq}};
use thrust_models::{{exists, Ghost, Model}};
"""

EXPECTATION = {"pass": "check-pass", "fail": "error-in-other-file: Unsat"}

COUNT_ENSURES = """#[thrust_macros::ensures(exists(|s: Seq<<I::Item as Model>::Ty>, last: I::Ty, fin: I::Ty|
    I::produces(it, s, last) && I::completed(Mut::new(last, fin)) && result == s.len()))]"""

COUNT_INVARIANT = """        thrust_macros::invariant!(|iter: I, iter_old: Ghost<I>, produced: Ghost<Seq<<I::Item as Model>::Ty>>, c: usize, it: thrust_models::FnParam<I>|
            iter_old == it.at_entry() && c == produced.len());
"""

# name: (result type, ensures, loop invariant, step, step of the fail twin)
CONSUMERS = {
    "count": ("usize", COUNT_ENSURES, COUNT_INVARIANT, "c += 1", "c += 2"),
    "count_inferred": ("i64", "#[thrust_macros::ensures(result >= 0)]", "", "c += 1", "c -= 1"),
}

# name: chain over the integer type {t}. Map and Filter, which take closures, are left out: they
# get no verdict on fptprove f7ddc51c0 at k = 1 under both settings.
SHAPES = {
    "range": "0..10{t}",
    "skip": "(0..10{t}).skip(2)",
    "take": "(0..10{t}).take(2)",
    "rev": "(0..10{t}).rev()",
    "by_ref": "(0..10{t}).by_ref()",
    "chain": "(0..10{t}).chain(3..5{t})",
    "zip": "std::iter::zip(0..10{t}, 3..5{t})",
    "enumerate": "(0..10{t}).enumerate()",
}


def chains(k):
    """The first k (shape, integer type): every shape at INTS[0], then every shape at INTS[1], ..."""
    every = [(shape, t) for t in INTS for shape in SHAPES]
    if k > len(every):
        raise SystemExit(f"only {len(every)} distinct chains")
    return every[:k]


def chain_expr(shape, t):
    return SHAPES[shape].format(t=t)


def consumer_fn(name, side):
    ret, ensures, invariant, step, fail_step = CONSUMERS[name]
    step = fail_step if side == "fail" else step
    return f"""
#[thrust_macros::context]
#[thrust_macros::requires(I::inv(it))]
{ensures}
fn {name}<I: IteratorSpec>(it: I) -> {ret}
where
    I::Item: Model,
{{
    let mut c = 0;
    for _x in it {{
{invariant}        {step};
    }}
    c
}}
"""


def caller_fn(name, j, shape, t):
    return f"""
fn use_{j}() {{
    {name}({chain_expr(shape, t)});
}}
"""


def program(name, k, side):
    cs = chains(k)
    body = "".join(caller_fn(name, j, *c) for j, c in enumerate(cs))
    calls = "".join(f"    use_{j}();\n" for j in range(k))
    return HEADER.format(expectation=EXPECTATION[side]) + consumer_fn(name, side) + body + f"\nfn main() {{\n{calls}}}\n"


def runs_rows(name, k):
    """Both sides in both settings; the fail side expects `unsat`."""
    rows = []
    for side, expect in (("pass", "sat"), ("fail", "unsat")):
        file = f"./{name}_k{k}_{side}.rs"
        rows += [f"{name}_k{k},generic,{side},{expect},{file},THRUST_PCSAT_MEMORY=6g",
                 f"{name}_k{k},per_instance,{side},{expect},{file},THRUST_PCSAT_MEMORY=6g THRUST_PER_INSTANCE_GENERICS=1"]
    return rows


def write(out, name, ks):
    os.makedirs(out, exist_ok=True)
    rows = ["id,setting,side,expect,file,env"]
    for k in ks:
        for side in ("pass", "fail"):
            with open(os.path.join(out, f"{name}_k{k}_{side}.rs"), "w") as f:
                f.write(program(name, k, side))
        rows += runs_rows(name, k)
    with open(os.path.join(out, "runs.csv"), "w") as f:
        f.write("\n".join(rows) + "\n")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("-n", action="store_true", help="print the chains and write nothing")
    ap.add_argument("out")
    ap.add_argument("consumer", choices=sorted(CONSUMERS))
    ap.add_argument("k", type=int, nargs="+")
    args = ap.parse_args()
    if args.n:
        for k in args.k:
            for j, (shape, t) in enumerate(chains(k)):
                print(f"{args.consumer}_k{k} use_{j}: {chain_expr(shape, t)}")
        return
    write(args.out, args.consumer, args.k)


if __name__ == "__main__":
    main()
