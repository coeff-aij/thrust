# Calls into std that no specification covers

Thrust does not analyze std bodies. A call into std is typed by an extern spec in `std.rs` or it
stops. This note explains why `v.extend(xs.iter().map(f))`, `Vec::from_iter` over a `map`, and a
`?` that converts its error stop with `unknown def (resolved)` since fork `main` 5acf1619. It also
describes what the branch `unknown-def-root` changes.

## How a call finds its contract

`basic_block::Analyzer::callable_ty` looks the callee up with `Analyzer::def_ty_with_args`, first
at the called def (a trait method), then at the instance `Instance::try_resolve` returns. An
extern spec is registered under the target of its tail call and covers a call only when
`bind_spec_args` matches the tail call's arguments against the call's and `spec_bounds_hold`
proves the spec's own trait bounds (`I: IteratorSpec`) at the call's types. A bound on a type
parameter or a projection is assumed. When no spec covers the call, the call panics.

The functions that stop are higher-order: their body runs user code, such as a closure, the
`next` of a local iterator, `From::from` or `Hasher::write`. A trusted contract for such a
function is sound only if it is stated in terms of the contracts of that code. Thrust can state
this in two ways. `pre!`/`post!` refer to a closure's contract. A spec trait's trait-level extern
spec is also the contract that every local impl is checked against, as `IteratorSpec::next` is.
5acf1619 limited `extend`/`from_iter` to `IteratorSpec` iterators and `from_residual` to `F = E`.
What is still missing:

- A model of the std types that own user code. `Map` and `Filter` have no `IteratorSpec`, and
  their `next` is foreign. So `next` can be total only because their constructor required
  something of the closure.
- A way to state `from_residual` through `F::from`. Creusot writes
  `F::from.postcondition((e,), f)`. Thrust has no `pre!`/`post!` for a trait method at a type
  parameter, so a spec trait has to stand in for it, as `TryIntoSpec` does.

Nothing else is needed on the analyzer side: `TypeBuilder` builds `Map`'s model from its `Model`
impl, and a closure in a model is its `Closure<F>`. The same survey found five neighbouring
defects:

1. `.collect()`, `.sum()` and `.count()` on a std iterator did not stop. They verified. The call
   resolves to the provided trait method itself, and that case fell into
   `abstract_callable_ty`, which gives `true`/`true`. At b3ed4f15 these verify:
   `xs.iter().map(|x| { assert!(*x > 100); *x }).collect::<Vec<_>>()`, and `collect()` over a
   local iterator whose `next` asserts.
2. A target kept only its first extern spec. A local wrapper for an instantiation std.rs does not
   cover was dropped without a warning.
3. In spec signatures, the macros lowered a closure parameter inside every path type. `Map<I, F>`
   became `(I::Ty, Closure<Closure<F>>)`. Repro: `ensures(result.0 == f)` on a function
   returning `Holder<F>` whose model is `(Closure<F>,)` gives E0308.
4. `<P as Model>::Ty` in a signature got a `<P as Model>::Ty: Model` bound. A `#[context]` method
   passes that bound on to its callers (E0277), and writing it into a spec's where clause makes
   `projection_holds` refuse the spec at an instance (`unknown def`).
5. Open: a fully annotated generic function is not re-analyzed at its instances, so two kinds of
   call inside it are unsound. Its call of a spec'd std function at a type parameter assumes the
   spec-trait bound (`Vec::from_iter(j)` with `J = Bad`, whose `next` asserts, verifies). Its
   call of an unspecified trait method at a type parameter gets `true`/`true`.

## Prior work

In creusot-std (3620de437, `src/std/iter/map.rs`, `filter.rs`, `iter.rs`, `vec.rs`, `ops.rs`):

- `Map`'s invariant is `next_precondition ∧ preservation ∧ reinitialize`. `produces` carries the
  chain of closure states with `hist_inv` and `postcondition_mut`, and `map` requires the three
  predicates.
- `filter` requires a closure without a precondition that captures immutably and has a precise
  postcondition.
- `collect`, `from_iter` and `extend` are stated through `FromIteratorSpec::from_iter_post`,
  `into_iter.postcondition` and `completed`.
- `from_residual` has a verified body, `Err(From::from(e))`. `From::from` has no trait contract,
  so every impl refines `requires(true)`.

The fork's evaluation 1 checks Creusot's `Map` as a local struct (`tests/ui/pass/creusot/map.rs`).
That needs a `produces_trans` lemma and PCSat at 120 s. `filter.rs` is a `Range` loop, not an
adapter. Evaluation 3's `layout.rs` at a8473cc3 models `Map`/`Filter` by item counts and asks the
closure's precondition at every closure state. The Creusot form on `layout-iter` (12e005b4,
unpushed) needed workarounds for defects 3 and 4. Its `Filter` with per-item closure answers made
PCSat time out on `produces_trans` at 300 s.

## Options

- A1: count-only std models. `map`/`filter` require the closure's precondition at every item
  the inner iterator can produce, in every closure state, as `Vec::retain` does. `produces` states
  counts. This is sound but incomplete: a precondition that reads a capture (`*x < k`) is a false
  alarm.
- A2: Creusot's `Map` in std.rs. It admits state-dependent preconditions and item values, but it
  carries map.rs's lemma and PCSat cost into every crate that uses it. For `Filter`, only
  Creusot's restricted closures or a `kept`-index form like `retain`'s are likely to be solvable.
- B1: a spec trait `IntoSpec<U>` on the source type (`converts`, `converts_to`). It specifies
  `From::from`, `Into::into` and `from_residual`, and `IntoSpec<T> for T` is the identity. A
  local `From` impl is checked against it. The cost is one `IntoSpec` impl per conversion.
- B2: `pre!`/`post!` over a trait method at a type parameter (Creusot's `F::from.precondition`),
  resolved at each call like a closure type. It needs no annotations, but it is a new formula
  form in `annot_fn` and in instantiation.
- C: report an unspecified call as a diagnostic instead of a panic. Soundness is unchanged, and a
  ui fail test can expect the stop.

## Soundness of the prototype

A `Map` value comes only from `map`, because its fields are private. It then changes only
through `next`, whose `produces` composes by `produces_trans`. Every item the closure receives is
therefore one that `map` required the precondition for, in some closure state. `Filter` follows
the same argument. Its `completed` allows items rejected before `None`. The local count-only
version said the inner iterator had not moved, which is false. The laws of both impls pass
`std_iterator_spec_laws.rs`. A local `From` impl is checked against `IntoSpec`: a body that asserts more than `converts`, or
returns other than `converts_to`, is Unsat. `requires`/`ensures` on the impl method do not
compile (E0407), so the impl has no other contract.

## Effect on the suites

Evaluation 1 uses local traits and is unaffected. In evaluation 3, the probes' local `Map`/`Filter`
impls now conflict with std.rs (E0119) and are removed, while their local `collect` specs stay.
`layout.rs` (not run on host) and `layout-iter` 12e005b4 carry the same impls, so they have to
drop them when this lands. Full-suite comparison: see the branch's report.

## Recommendation

Land the soundness fixes for defects 1 and 2, the macro fixes for defects 3 and 4, A1 and B1.
This follows the user's decision of 2026-10-01 that iterator specs are not yet stable enough for
std.rs additions: A1 adds only an item count, and `extend`/`from_iter`/`collect` keep their
postconditions. Next, add C. Move `Map` to A2 once layout-iter's form is stable, and keep
`Filter` count-only. Defect 5 and B2 are separate work.
