# Generic functions at their instances: reproducers

Small programs for three design questions about generic functions, run on fork commit ec539b84
(this branch's base): when a generic over a closure is analysed again at an instance (E1 to E6),
what a generic verified once assumes at its type parameters under `THRUST_VERIFY_ONLY` (V1 and
V1 with `t.m(1)`), and how a function without a contract is checked when code Thrust does not
analyse enters it (`tests/ui/fail/verify_only/uncontracted_under_unselected.rs`).

| file | program |
| --- | --- |
| `e1.rs` | `#[thrust::callable] fn apply<F: Fn(i32) -> i32>(f: F) -> i32 { f(1) }`, called with `\|x\| x + 1` |
| `e2.rs` | E1 with `requires(forall(\|x: i32\| pre!(f(x))))` |
| `e5.rs` | E2 with `ensures(result == 2)` |
| `e3.rs` | E1 with `F: FnMut` and the closure `\|x\| { n += 1; x + 1 }` |
| `e4.rs` | `apply_twice<F: FnMut(i32) -> i32>` calling `f` twice, `requires(forall(\|c: Closure<F>, y: i32\| pre!(c(y))))`, with E3's closure |
| `e6.rs` | E4 with `ensures(result == 3)` |
| `v1.rs` | a generic `g<T: Tr>` calling `t.m(0)`, where `S::m` requires `x > 0`; `caller` calls `g(&S)` |
| `v1_m1.rs` | V1 with `t.m(1)`, a program that does not panic |

## Running

From this directory, with `THRUST_RUSTC` a `thrust-rustc` built at ec539b84 and `COAR_IMAGE` a
CoAR image (`./run.sh -n` prints the commands):

```
THRUST_RUSTC=<target>/debug/thrust-rustc COAR_IMAGE=<image> ./run.sh
```

Each line gives the exit status, whether the solver answered `Unsat`, and how many log lines
"generic def at an instance" say `analyze_body=true`.

## Results

2026-11-11, fptprove develop 3535ddfa98 with cvc5 1.4.2, 8 GB and 2 CPUs per container:

| case | analysed at the instance | verdict |
| --- | --- | --- |
| E1 | no | `unsat` |
| E2 | yes | `sat` |
| E5 | yes | `unsat` |
| E3 | yes | `sat` |
| E4 | yes | `sat` |
| E6 | yes | `sat` |
| V1, whole crate | no | `unsat` |
| V1, `THRUST_VERIFY_ONLY=caller` | no | `sat` |
| V1, `THRUST_VERIFY_ONLY=g` | no | `sat` |
| V1 with `t.m(1)`, whole crate | no | `unsat` |
| V1 with `t.m(1)`, `THRUST_VERIFY_ONLY=caller` | no | `sat` |
| V1 with `t.m(1)`, `THRUST_VERIFY_ONLY=g` | no | `sat` |
| `uncontracted_under_unselected.rs`, whole crate | no | `sat` |
| `uncontracted_under_unselected.rs`, `THRUST_VERIFY_ONLY=main,g` | no | `unsat` |

## Listing the assumed total methods

`assumed_total_method.patch` adds one `eprintln!` to `abstract_callable_ty`
(`src/analyze/basic_block.rs`), which prints each trait method without a contract that a generic
body calls at a type parameter and so assumes to accept every argument. With it applied
(`git apply drafts/generic-instance-designs/assumed_total_method.patch` at the repository root,
then `cargo build`), V1 prints `assumed total method: Tr::m at [T/#0] in ... g`. Compiling the
roots `tests/ui/pass/rustc_coroutine/{values,index,hashes}.rs` with their own `//@` flags and
environment and `THRUST_SOLVER=true` (no query solved) prints none on 2026-11-11.
