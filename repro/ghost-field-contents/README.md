# `Ghost<T>` fields could not be used as their contents in specifications

## Status

Fixed in `main` (`ghost-field-model` 4fc9b1a, merged via dc43ee0; `main` db58667 contains it --
`git merge-base --is-ancestor 4fc9b1a main` succeeds). Kept here as a self-contained record of
the defect, since it was never filed upstream.

## Symptom

`Ghost<T>`'s own documentation states that in a specification it stands for its contents, the
same way a `Ghost<T>` **parameter** does: `lower_params`
(`thrust-macros/src/formula_fn_type_lowering.rs:38-67`) maps a lifted formula function's
parameter `x: T` to `x: <T as Model>::Ty`, and `Ghost<T>`'s `Model` impl resolves to
`<T as Model>::Ty`, so a `Ghost<Seq<Int>>` parameter behaves like a `Seq<Int>` in the formula.

That projection was applied only at the parameter, never recursively into a parameter's field
types. Where a struct's `Model::Ty` is the struct itself -- the shape every stateful adapter
uses to keep a history -- a `Ghost`-typed **field** kept its surface type, and `Ghost<T>` carried
nothing but `Clone`, `Copy` and `Model`:

```rust
struct Hist { produced: Ghost<Seq<Int>> }
impl Model for Hist { type Ty = Hist; }
```

`(*h).produced` in a formula was a `Ghost<Seq<Int>>` with no method and no `PartialEq`:

| what the formula does with the field | result before the fix |
| --- | --- |
| `(*h).produced.push(x)` | `E0599`, no method `push` on `Ghost<T>` |
| `(*h).produced.len()` | `E0599`, no method `len` on `Ghost<T>` |
| `(!h).produced == (*h).produced` | `E0369`, `==` not applicable to `Ghost<T>` |
| the same operation on an equivalent `Ghost<T>` **parameter** of a free function | verified |

The consequence: a ghost history could not live in the struct it described. It had to be
threaded through free functions taking a `Ghost<T>` parameter, or the struct's `Model::Ty` had
to be rewritten as a tuple so the history was reached positionally instead of by field name.

## Reproduction

Seven files, each a variation on the `Hist` struct above:

| file | where the history lives | formula |
| --- | --- | --- |
| `repro.rs` | `Ghost` field, `ghost!` body | `h.produced.push(x)` |
| `ctrl_spec.rs` | `Ghost` field, `ensures` (via a helper `push_produced`) | `(*h).produced.push(x)` |
| `len_only.rs` | `Ghost` field, `ensures` | `(*h).produced.len() >= 0` |
| `eq_only.rs` | `Ghost` field, `ensures` | `(!h).produced == (*h).produced` |
| `ctrl_local.rs` | local rebound from the field, `ghost!` body only | `p.push(x)` |
| `ctrl_local_spec.rs` | `ctrl_local.rs` plus an `ensures` naming the field directly | `(*h).produced.push(x)` |
| `ctrl_param.rs` | `Ghost` **parameter** of a free function (the decisive control) | `produced.push(x)` |

Invocation for every file:

```console
$ cargo build
$ export LD_LIBRARY_PATH="$(rustc --print sysroot)/lib"
$ ./target/debug/thrust-rustc -Adead_code -Aunused-variables -C debug-assertions=false <file>.rs
```

### Recorded (thrust `c702e41`, before the fix)

The `.out` files next to the five failing `.rs` files above are that run's transcripts,
verbatim.

Driver default solver (Z3 4.15.2, `fp.spacer.global=true fp.validate=true`,
`src/chc/solver.rs:117-132`); no `THRUST_SOLVER` override, so CoAR was not reached by any row.
Every failing row aborted in rustc type-check, before any solver was invoked.

| file | exit |
| --- | --- |
| `repro.rs` | 1 -- `E0599` |
| `ctrl_spec.rs` | 1 -- `E0599` |
| `len_only.rs` | 1 -- `E0599` |
| `eq_only.rs` | 1 -- `E0369` |
| `ctrl_local.rs` | 0 |
| `ctrl_local_spec.rs` | 1 -- `E0599` |
| `ctrl_param.rs` | 0 |

`ctrl_local.rs` rebinds the field to a local before use, which makes the local a `Ghost`
*parameter* of the lifted `ghost!` closure rather than a field access, so it already worked; adding
an `ensures` to the same function (`ctrl_local_spec.rs`) brings the field access straight back,
since a contract has no local to rebind through and can only name the field.

### Re-run on `main` (with the fix)

Same invocation, same solver (driver default, z3, no `THRUST_SOLVER`), run against this branch's
build of `main` db58667:

| file | exit |
| --- | --- |
| `repro.rs` | 101 -- driver panic, `src/rty/subtyping.rs:159`: "inconsistent types: got=`&mut (own Seq<int>,)`, expected=`(own Seq<int>,)`" |
| `ctrl_spec.rs` | 1 -- verification error, solver stage (below) |
| `len_only.rs` | 1 -- verification error, solver stage (below) |
| `eq_only.rs` | 1 -- verification error, solver stage (below) |
| `ctrl_local.rs` | 1 -- verification error, solver stage (below) |
| `ctrl_local_spec.rs` | 1 -- verification error, solver stage (below) |
| `ctrl_param.rs` | 1 -- verification error, solver stage (below) |

None of the six that reach the solver stage produce `E0599` or `E0369` any more: rustc
type-checking now accepts a `Ghost` field used as its contents, which is what the fix adds. All
six instead fail identically at the solver stage, with the emitted query's uses of `Seq`
rejected as `(error "unknown sort 'Seq'")` by the driver's default z3 invocation, ending in a
reported "verification error". That is `main`'s native-`Seq` encoding meeting a solver
configuration that does not declare the `Seq` sort for its Horn/`fp.spacer` solving path; it is
unrelated to the `Ghost`-field defect this bundle is about; a CoAR-based build is expected to
parse it.

`repro.rs` is the one file that still fails, but not with `E0599`: it now reaches MIR analysis
and the driver panics inside its own subtyping check on a `ghost!` closure that captures the
whole `Hist` struct by value (`|h: Hist, x: i64| -> Seq<Int> { h.produced.push(x) }`). That is a
distinct, separate defect from the field-projection gap this bundle documents; it is not analyzed
further here.

## Relation to the fix

`ghost-field-model` 4fc9b1a adds `Deref` and `PartialEq` for `Ghost<T>` in `std.rs` and an
identity arm plus index typing in `annot_fn.rs`, and panics if executable code (not a
specification) calls something whose where-clause needs `Ghost`'s `PartialEq`/`Deref`. It changed
emission on the evaluation set by DefId comments only (468/468 queries otherwise unchanged). It
merged into `main` via dc43ee0 and is present in `main` db58667.
