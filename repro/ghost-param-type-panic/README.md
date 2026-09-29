# A `ghost!` parameter typed differently from its live variable panics the driver

## Status

Reproduces on upstream `main` e112206 and on this fork's `main` 496e711. No fix yet. No open
upstream issue matches (searched for "ghost" and "inconsistent types", 2026-09-29).

## Symptom

`ghost!`'s parameters name the live variables the ghost term reads, with their types
(`thrust-macros/src/lib.rs`, the doc comment of `ghost`). When a parameter's type differs from
the variable's, here `c: Counter` for a `c: &mut Counter`, rustc accepts the program and the
driver panics in its subtyping check instead of reporting the mismatch:

```
thread 'rustc' panicked at src/rty/subtyping.rs:155:14:
inconsistent types: got=&mut (own int,
own Seq<int>), expected=(own int,
own Seq<int>)
```

## Reproduction

`repro.rs` is upstream's `tests/ui/pass/ghost_field.rs` with one change in the `ghost!` call:

```rust
c.seen = thrust_macros::ghost!(|c: &mut Counter, x: i64| -> Seq<Int> { (*c).1.push(x) });   // the test
c.seen = thrust_macros::ghost!(|c: Counter, x: i64| -> Seq<Int> { c.1.push(x) });           // repro.rs
```

No solver is needed; the panic is in the frontend:

```console
$ cargo build
$ export LD_LIBRARY_PATH="$(rustc --print sysroot)/lib"
$ THRUST_SOLVER=true ./target/debug/thrust-rustc -Adead_code -Aunused-variables -C debug-assertions=false --edition 2021 repro.rs
```

| tree | exit | transcript |
| --- | --- | --- |
| upstream `main` e112206 | 101, the panic above at `subtyping.rs:155` | `repro.upstream-e112206.out` |
| this fork's `main` 496e711 | 101, the same panic at `subtyping.rs:159` | `repro.fork-496e711.out` |
| upstream `tests/ui/pass/ghost_field.rs` itself, on either tree | reaches the solver | -- |

## Expected

A diagnostic at the `ghost!` call naming the parameter whose type does not match the live
variable's (`Counter` against `&mut Counter`), rather than a panic.

## Where it came from

`../ghost-field-contents/repro.rs` writes its `ghost!` parameter the same way
(`|h: Hist, ..|` for a `h: &mut Hist`); on this fork's `main` it stops at this panic after the
fork's Ghost-field fix lets it through rustc's type check. Written as `|h: &mut Hist, x: i64| ->
Seq<Int> { (*h).produced.push(x) }` it reaches the solver like the other files there.
