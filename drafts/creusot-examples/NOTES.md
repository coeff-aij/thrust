# Call-site examples of Creusot's iterator benchmark

Drafts of the `examples/` rows of `creusot-benchmark-status.md` (fse2027-notes), written on
`call-site-drafts` (base `creusot-adapters` a01f5be, plus the Creusot-form Skip commits e4eebf0 and
e9df3b0 cherry-picked as c483b8f and dade088). Stages, spec forms and blocker IDs are the status
note's. Every file here is self-contained: the iterator trait, its laws and the adapters are copied
from the tracked files named in each section, because Thrust has no cross-file specs.

Measured on `coar:develop-3d34b93de` = image `f63bb238c55e` (fptprove develop 3d34b93de), config
`pcsat_tbq_ar.json`, through `~/.claude/bin/coar-run` (2 CPUs, 8 GiB), driver built from this
branch. Walls are for single runs, `n/N` is how many of `N` runs gave the verdict.

Layout: `<name>.rs` is the pass file, `fail/<name>.rs` its twin. A file's hand-written SMT predicate
bodies name `q_*` symbols whose hash includes the crate name, i.e. the file stem, so a file keeps
working when moved but not when renamed.

Annotation counts are `law / logic-or-predicate / loop invariant`, counted as the status note counts
them. Creusot's examples themselves carry `0 / 0 / 0` (all of it is in `common.rs` and creusot-std;
closure contracts and `proof_assert!` are not counted), so the Thrust count is split into what the
copied iterator spec and adapters carry and what the example adds. Laws are the `next` ensures other
than `invariant(!self)` and `None ==> completed`, plus body-less callable laws.

Creusot's std specs cited below are in `~/Remotes/creusot/creusot-std/src/std/iter/` (3620de437);
the example sources are in `~/Remotes/artifact_creusot/benchmarks/src/examples/`.

## Summary

| example | file | stage | form | pass / twin (develop-3d34b93de) | blocker |
| --- | --- | --- | --- | --- | --- |
| decuple_range | `tests/ui/{pass,fail}/examples/decuple_range.rs` | S4 (position-free property) | `step` | sat 46-58 s 3/3 / unsat 1.8 s 3/3 | positional property needs history: the step form |
| decuple_range | `decuple_range_visited.rs` | S3 | `produces` + unary guard | unknown 0.8 s 3/3 / unsat 0.8 s 3/3 | call site of `collect` at `Map<Range, _>` (the form (c) call-site Unknown) |
| skip_take | `skip_take.rs` (generic `I`) | S2 | `produces` | parse: unification failure | B9/B11: no instance at a type-parameter call site |
| skip_take | `skip_take_range.rs` | S2 | `produces` | parse: `.. is not bound` | B9: nested instances emitted out of order; reordered by hand: unknown 3/3 / unknown 3/3 |
| counter | `counter.rs` | S3 | `step` + unary guard + ghost `produced` | timeout 120 s 3/3 / timeout 120 s 3/3 | not localized (the probe it is built from is Timeout on latest); `x == v`, `cnt == x.len()` not expressible in the step form; B20 for `v.iter()` |
| extend | `extend.rs` | S3 | `produces` | unknown 0.7 s 3/3 / unsat 0.8 s 3/3 | call site consuming `extend`'s `exists pre s` ensures |
| (extra) take_count | `take_count.rs` | S3 | `produces` | unknown 0.4 s 3/3 / unsat 0.4 s 3/3 | not localized |

## decuple_range

Creusot:

```rust
let v: Vec<_> = (0..10)
    .map_inv(#[requires(@x < 100)] #[ensures(@result == @x * 10)] |x: u32, _| x * 10)
    .collect();
proof_assert! { forall<i : Int> 0 <= i && i < (@v).len() ==> @(@v)[i] == i * 10 };
```

Creusot uses `map_inv`; its closure ignores the history argument, so both drafts use plain `map`
with an `Fn(i64) -> i64` closure. `u32` is `i64`; with `-C debug-assertions=off` there is no
overflow check, so `requires(x < 100)` is kept only as the partial precondition the adapter's guard
must discharge.

### tests/ui/pass/examples/decuple_range.rs: step form, position-free property

Stage: S4, tracked as `tests/ui/{pass,fail}/examples/decuple_range.rs`. Form: `step` (trait and `Map` from
`traits/map_call.rs`), `collect` + `FromIterator for Vec<i64>` rewritten for the step form.

Correspondence:

| Creusot | Thrust |
| --- | --- |
| `map_inv.rs` `next_precondition(iter, func, produced)`: `forall e i. iter.produces([e], i) ==> func.precondition((e, produced))` | `Map::invariant`: `iter.invariant() && forall e. iter.produces(e) ==> pre!(func(e))` (unary guard; `preservation` and `reinitialize` hold trivially for an `Fn` closure that ignores the history) |
| `map.rs` `produces(self, visited, succ)` | `Map::step(self, item, dist)` (one call) and `Map::produces(self, item)` (still producible) |
| `iter.rs` `collect`: `exists done prod. done.completed() && self.produces(prod, *done) && B::from_iter_post(prod, result)`, `vec.rs` `from_iter_post(prod, res) = prod == res@` | `collect` / `from_iter`: `forall k < result.len(). Self::produces(*self, result[k])` |
| `range.rs` `produces` | `Range::step`, `Range::produces(self, item) = start <= item < end` |

The step form has no history, so `collect` cannot say where an item sits in the result. The
checked property is therefore weaker than Creusot's: `0 <= v[k] <= 90` for every element, which
is what "each element is `10 * x` for a producible `x`" gives without the position. Creusot's `v[k] == 10 * k` is in `decuple_range_visited.rs`.

Annotations: copied spec 3 / 12 / 0 (laws: the `step`, `produces` and `produces`-monotone ensures
of `next`; predicates: 4 declared on the trait, 4 bodies each for `Map` and `Range`); the example
adds 0 / 0 / 1 (the loop invariant of `from_iter`, whose Creusot counterpart is a trusted std spec).

Verdicts (develop-3d34b93de): pass sat 58.3 / 47.0 / 45.8 s (3/3); fail twin `1 <= v[k]` (the
first element is `0`) unsat 1.8 / 1.9 / 1.8 s (3/3). Through the ui harness both files pass (header
timeout 120 s, since the pass is close to 60 s). A twin claiming `v[k] <= 80` gives no answer in 120 s
(1/1).

Blocker for Creusot's positional property: the step form itself (no history); see the next file.

### decuple_range_visited.rs: `produces` + unary guard, Creusot's property

Stage: S3. Form: `produces` + unary guard (trait and `Map` from the form (c) probe
`.experimental/map/creusot-guard/v3-bisect/B-unary/`, `collect` and `FromIterator for Vec<i64>`
from `traits/collect_visited_seq_i64.rs`). The call site states Creusot's `v[k] == 10 * k`.

Correspondence:

| Creusot | Thrust |
| --- | --- |
| `map.rs` `produces(self, visited, succ)`: `exists fs s. s.len() == visited.len() && self.iter().produces(s, succ.iter()) && forall i. postcondition_mut(fs[i], (s[i],), visited[i])` | `Map::produces`: `func == o.func && exists s. s.len() == visited.len() && iter.produces(s, o.iter) && forall k. post!(func(s[k]), visited[k])` (an `Fn` closure, so no closure-state chain `fs`) |
| `map.rs` `next_precondition`: `forall e i. iter.produces([e], i) ==> func.precondition((e,))` | `Map::invariant`: `iter.invariant() && forall e. iter.produces1(e) ==> pre!(func(e))` |
| `map.rs` `completed`: `exists inner. inner.completed() && func unchanged` | `Map::completed`: the same, with `inner` the projection |
| `iter.rs` `collect` + `vec.rs` `from_iter_post` | `collect` / `from_iter`: `exists pre. produces(*self, result, pre) && completed(Mut::new(pre, !self))` |
| `range.rs` `produces`, `produces_refl` law | `Range::produces`, `produces_refl` callable law; `produces_trans` as the one-step ensures of `next` |

Annotations: copied spec 6 / 12 / 0 (laws: empty, singleton, one-step-trans, `produces1` and
`produces1`-monotone ensures of `next`, and the callable `produces_refl`; predicates: 4 declared on
the trait, 4 bodies each for `Map` and `Range`); the example adds 0 / 0 / 1 (`from_iter`'s loop).

The hand-written bodies of `Map::invariant`, `Map::produces` and `Map::produces1` name `F`'s
contract `q_pre_produces_refl_*` / `q_post_produces_refl_*`, because that is the symbol the closure
call in `Map::next` is emitted with once the impl has a second method (see the findings at the end).

Verdicts (develop-3d34b93de): pass unknown 0.9 / 0.8 / 0.8 s (3/3), `coar:latest` unknown 63.4 s
(1/1); twin (`v[k] == 10 * k + 1`) unsat 0.8 / 0.8 / 0.8 s (3/3), `coar:latest` unsat 1.4 s (1/1).

Localized (develop-3d34b93de, 3/3 each): without the call site (trait, `Map`, `Range`, `collect`,
`from_iter`) sat 0.5-0.6 s (`coar:latest` sat 0.7 s); with the call site's ensures replaced by `true`
unknown 0.8-0.9 s (`coar:latest` unknown 1.3 s). The generic spec is consistent, the twin's unsat
comes from the positional property, and the Unknown is in the call site consuming `collect`'s
`exists pre. Map::produces(..) && ..` at `Map<Range, _>`.

Blocker: the form (c) call-site Unknown (B15/B12 in the status note, the `∃ Seq` witness family).

## skip_take

Creusot:

```rust
#[requires(iter.invariant())]
pub fn skip_take<I: Iterator>(iter: I, n: usize) {
    let res = iter.take(n).skip(n).next();
    proof_assert! { res == None };
}
```

Form: `produces`. The trait, `Take` and `Range` are `traits/take.rs`'s, `Skip` is `traits/skip.rs`'s
from `skip-produces` (e4eebf0 + e9df3b0, cherry-picked here as c483b8f + dade088). The only change
to the adapters is `Take`'s model, now `(<I as Model>::Ty, Int)` like `Skip`'s, so that
`Skip<Take<I>>` meets `Skip`'s `PartialEq` bound on its inner model. The adapter is built with struct
literals (`Skip { iter: Take { iter, n }, n }`); there is no `take`/`skip` constructor on the trait.

Correspondence (both adapters in Creusot's form):

| Creusot | Thrust |
| --- | --- |
| `take.rs` `produces`: `self.n() == o.n() + visited.len() && self.iter().produces(visited, o.iter())` | `Take::produces`, same |
| `take.rs` `completed`: `n == 0 && resolve(self) \|\| n > 0 && n == (^self).n() + 1 && iter.completed()` | `Take::completed`, same |
| `skip.rs` `produces`: `visited == [] && self == o \|\| o.n() == 0 && visited.len() > 0 && exists s. s.len() == self.n() && self.iter().produces(s.concat(visited), o.iter())` | `Skip::produces`, with `s.concat(visited)` as one array `t` indexed with an offset |
| `skip.rs` `completed` | `Skip::completed`, same |
| `Invariant for Take/Skip`: `inv(self.iter())` | `invariant`: the inner invariant and `n >= 0` |

Why `res == None` follows: a `Some(i)` from `Skip::next` gives `Skip::produces(s0, [i], s1)`, whose
second disjunct asks `Take::produces(t0, t, t1)` with `t.len() == n + 1`, i.e. `n == t1.n + n + 1`,
and `t1.n >= 0` is `Take`'s invariant at the returned state.

Annotations: copied spec 4 / 12 / 1 (laws: the empty, singleton and one-step-trans ensures of
`next` and the callable `produces_refl`; predicates: 3 declared on the trait, 3 bodies each for
`Take`, `Skip`, `Range`; the invariant is `Skip::next`'s drain loop, Creusot's 4 invariants in one);
the example adds 0 / 0 / 0.

### skip_take.rs: generic `I`, as Creusot writes it

Stage: S2 (the query Thrust emits is ill-sorted and rejected at parse). Verdict (develop-3d34b93de,
1/1, 0.3 s): `unification failure: A8_Tuple<a2-Int> = A4_Tuple<Tuple<a4-Int>-Int>`. At a call site
generic in `I`, Thrust emits no instance of `Skip`'s and `Take`'s predicates for `Skip<Take<I>>` and
applies `Skip`'s generic definitions (over `Skip`'s own forall-sort `a2`) to the call site's
`Skip<Take<a4>>`; inside that generic definition the inner `produces` is the abstract forall-fun, not
`Take`'s. Blocker: B9 (811e6b6 emits an instance per concrete instantiation only) and B11. Fail twin
(`Take { iter, n: n + 1 }`) is written, unmeasured beyond the same parse failure.

### skip_take_range.rs: `Skip<Take<Range>>`

Stage: S2 (the emitted query refers to a definition before it). Verdict (0.3 s; develop-3d34b93de
pass and twin, `coar:latest` pass): `p_invariant_…<Tuple<Box<Int>-
Box<Int>>> is not bound`. The instance of `Skip`'s predicates at `Take<Range>` is emitted before the
instance of `Take`'s predicates at `Range` that its bodies call (instances come out in discovery
order, not dependency order). Blocker: B9 (emission order of nested instances); no ID in the status
note yet.

With the `define-fun`s of the dump reordered by hand (diagnostic only, `toposort.py` in the session
scratchpad): pass unknown 1.0 / 0.8 / 0.8 s (3/3), twin unknown 0.8 / 0.8 / 0.8 s (3/3); `coar:latest`
unknown 1.3 s (1/1). Spelling `next`'s singleton ensures as `s == Seq::singleton(i)` instead of by
length and index gives the same (pass unknown 0.8 s, twin unknown 0.9 s). This is the Skip call-site
Unknown the status note records (the `∃ Seq` witness under `Skip::produces`'s second disjunct).

## counter

Creusot:

```rust
pub fn counter(v: Vec<u32>) {
    let mut cnt = 0;
    let x: Vec<u32> = v.iter().map_inv(
        #[requires(@cnt == (*_prod).len() && cnt < usize::MAX)]
        #[ensures(@cnt == @old(cnt) + 1 && result == *x)]
        |x, _prod| { cnt += 1; *x }).collect();
    proof_assert! { (@x).ext_eq(@v) };
    proof_assert! { @cnt == (@x).len() };
}
```

Form: `step` with a unary `produces1` guard and `MapInv`'s ghost `produced` (trait and adapter from
the FnMut probe `.experimental/map/mapinv/v5_counter/`, which needs `fnmut-capture-deref` 474a333,
on the base), `collect` from `tests/ui/pass/examples/decuple_range.rs` with `produces1`. The source is `Range { start, end }`
instead of `v.iter()`: a local `Iterator` impl for `slice::Iter` has `Item = &'a T`, which is B20 on
this base (`predicate-assoc-bound` 19a98ca is not on it).

Correspondence:

| Creusot | Thrust |
| --- | --- |
| `map_inv.rs` `MapInv { iter, func, produced: Snapshot<Seq<I::Item>> }` | `Map { iter, func, produced: Ghost<Seq<Int>> }`, `F: FnMut(i64, Ghost<Seq<Int>>) -> i64` |
| `next_precondition(iter, func, produced)` | `Map::invariant` first conjunct: `forall e. iter.produces1(e) ==> pre!(func(e, produced))` |
| `preservation_inv(iter, func, produced)`: after a call on `e1` with history `h`, the closure accepts `e2` with history `h ++ [e1]` | `Map::invariant` second conjunct, over producible `e1`, `e2` and any `h` (not over the inner iterator's reachable states) |
| `produces_one(self, visited, succ)` | `Map::step`: `exists i. iter.step(i, dist.iter) && pre && post && dist.produced == self.produced.push(i)` |
| `completed`: `(^self).produced == [] && iter.completed() && func unchanged` | `Map::completed`: `iter.completed()`, `func` and `produced` unchanged (the history is not reset) |

What is checked: the closure's history-dependent precondition `cnt == produced.len()` is discharged
at every call inside `collect`, and each element is one the range produces. Creusot's two
assertions are not stated: `x == v` needs the position of each element and `cnt == x.len()` needs the
final closure state after `collect`, and the step form's `collect` gives neither.

Annotations: copied spec 3 / 12 / 0 (laws: `step`, `produces1` and `produces1`-monotone ensures of
`next`; predicates: 4 declared on the trait, 4 bodies each for `Map` and `Range`); the example adds
0 / 0 / 1 (`from_iter`'s loop).

Stage: S3. Verdicts (develop-3d34b93de): pass no answer in 120 s (3/3), twin (`start < v[k]`) no
answer in 120 s (3/3). With the call site's ensures replaced by `true` it is still no answer in 60 s
(1/1), so the time goes to the adapter, `from_iter` or the closure's precondition, not the element
property. The probe this is built from (one `next` call) is recorded as Timeout on `coar:latest`.

Blockers: the Timeout (not localized further); Creusot's two assertions need the `produces` form of
`MapInv`, which is the Creusot-form Map that does not verify on any image (status note, map row); B20
for the `v.iter()` source.

## extend

Creusot:

```rust
pub fn extend_index(mut v1: Vec<u32>, v2: Vec<u32>) {
    let oldv1: Ghost<Vec<u32>> = ghost! { v1 };
    let oldv2: Ghost<Vec<u32>> = ghost! { v2 };
    v1.extend(v2.into_iter());
    proof_assert! { (@v1).ext_eq((@oldv1).concat(@oldv2)) };
}
```

Form: `produces` (trait from `traits/collect_visited_seq_i64.rs`). The iterator is std's
`vec::IntoIter<i64>` with its std.rs model `(sequence, cursor)`, given the local trait's spec by a
local impl whose `next` is std's (`std::iter::Iterator::next(self)`, through the extern spec of
std-iter-models). `Extend<A>` is a local trait whose `extend<I: Iterator<Item = A>>(&mut self,
iter: &mut I)` is generic; the call site uses it at `I = vec::IntoIter<i64>`. `v1` is returned
instead of asserted on through ghosts, and the call is spelled `<Vec<i64> as Extend<i64>>::extend`
because `v1.extend(..)` is ambiguous with std's `Extend` (E0034).

Correspondence:

| Creusot | Thrust |
| --- | --- |
| `vec.rs` `IteratorSpec for IntoIter`: `produces(self, visited, rhs) = self@ == visited.concat(rhs@)`, `completed = resolve(self) && self@ == []` | `IntoIter::produces`: same sequence, cursor advanced by `visited.len()`, `visited[k] == seq[cursor + k]`; `completed`: resolved and cursor at the end. The model is the whole sequence plus a cursor, not the remaining sequence |
| `vec.rs` `Extend for Vec`: `exists start_ done prod. into_iter.postcondition((iter,), start_) && done.completed() && start_.produces(prod, *done) && (^self)@ == self@.concat(prod)` | `Extend::extend`: `exists pre s. produces(*iter, s, pre) && completed(Mut::new(pre, !iter))` and `!self` is `*self` followed by `s`, index by index |
| `(@oldv1).concat(@oldv2)` | `result.len() == v1.len() + v2.len()` and the two index ranges |

Annotations: copied spec 3 / 6 / 0 (laws: the singleton and one-step-trans ensures of `next` and
the callable `produces_refl`; predicates: 3 declared on the trait, 3 bodies for `IntoIter`); the
example adds 0 / 0 / 1 (the loop invariant of `extend`, whose Creusot counterpart is a trusted std
spec).

Stage: S3. Verdicts (develop-3d34b93de): pass unknown 0.7 / 0.8 / 0.7 s (3/3), `coar:latest`
unknown 0.7 s (1/1); twin (`result.len() == v1.len() + v2.len() + 1`) unsat 0.7 / 0.9 / 0.8 s (3/3).

Localized (1/1 each): the `IntoIter` impl alone is sat (0.3 s); the impl plus the generic `extend`
with its full ensures and no call site is sat (0.4 s); the call site with its ensures replaced by
`true` is unknown (0.8 s). The Unknown is therefore in consuming `extend`'s `exists pre s. ..`
ensures at `I = vec::IntoIter<i64>` together with `IntoIter::produces`'s quantified body, the same
residual family as the other call-site Unknowns.

Two things the draft needed that are not in Creusot's: `pushed.len() >= 0` in `extend`'s loop
invariant and `requires(v2.len() >= 0)` at the call site, because Thrust's `Vec` model does not know
that a length is non-negative (the tracked `iterators/` tests carry the same requires); and a local
`Vec` `pushed` in `extend`'s body that records what was produced, so the loop invariant names the
history instead of quantifying it existentially (with the existential the generic `extend` was
unknown).

## take_count (extra call site, no Creusot counterpart)

`take_count(start, end, n)` drains `Take { iter: Range { start, end }, n }` in a `while let` loop
and proves that at most `n` items come out. Form: `produces`; trait, `Take` and `Range` from
`traits/take.rs`, with `Take`'s model changed to `(<I as Model>::Ty, Int)` so the loop invariant can
read the counter as `t.1`. The loop invariant is `cnt + t.1 == n && t.1 >= 0 &&
Take::<Range>::invariant(t)`; the counting comes from `Take::produces` applied to `next`'s singleton
ensures. Fail twin: `result < n`.

Stage: S3. Verdicts: pass unknown 0.4 s (3/3 develop-3d34b93de; 1/1 `coar:latest`, 0.5 s), twin
unsat 0.4 s (3/3). Not localized further; the tracked `traits/take.rs` call site (two `next` calls,
no loop) verifies.

Annotations: copied spec 4 / 9 / 0; the example adds 0 / 0 / 1.

## Findings that are not one example's

- No frontend panic or ICE was hit. The two emission defects (B9 family) are the `skip_take` rows:
  nested generic-impl predicate instances are emitted in discovery order, so `Skip<Take<Range>>`'s
  instance names `Take<Range>`'s before its `define-fun` (`is not bound`); and a call site generic in
  its type parameter gets no instance at all and applies the generic definition to the instantiated
  sort (`unification failure`).
- Hand-written SMT predicate bodies name forall-sorts by number, and the numbering is per file:
  the inner item sort that `traits/map_call.rs` spells `a3` is `a8` in `decuple_range.rs` and `a5` in
  `decuple_range_visited.rs`, and removing an item from a file renumbers them again. A wrong number is
  not a parse error: the instance substitution silently maps it to another sort. Check every binder
  sort against the `declare-forall-fun` signatures of the file's own dump.
- The forall-fun that stands for an impl's closure parameter `F` is named `q_pre_<method>_<hash>`
  after one method of the impl, and which one depends on the impl's other methods: with
  `produces_refl` (or any second method, even an empty one without a contract) next to `next`, the
  closure call in `next` is emitted as `q_pre_produces_refl_*` while `q_pre_next_*` is still declared.
  A hand-written body that names `q_pre_next_*` then speaks about an unrelated forall-fun, and since
  `q_pre_produces_refl_*` occurs in no clause body, the call's precondition clause is refuted
  (`unsat`, not a solver fault). Minimal: `Map` with `next`, an empty second method and the unary
  guard naming `q_pre_next_*` is unsat (develop-3d34b93de 3/3, `coar:latest` 1/1); naming the other
  method's symbol, or dropping the second method, is sat (3/3, 1/1). Take the closure symbols from the
  file's own dump, and re-take them when a method is added.
- Thrust's `Vec` model does not know `len() >= 0`. It shows up as an unsat call site (a negative
  length makes a length equation false) and as an Unknown loop (a `push` at `len1 + pushed.len()`
  cannot be told apart from an index below `len1`).
- An adapter used as the inner iterator of another adapter needs a model whose `Model::Ty` is its own
  model and `PartialEq` (`(<I as Model>::Ty, Int)`, `(<I as Model>::Ty, Closure<F>)`); `Take<I>` and
  `Map<I, F>` as their own model do not meet `Skip`'s and `collect`'s bounds.
- `v1.extend(..)` on a `Vec` is ambiguous between a local `Extend` and std's (E0034): std's trait
  stays in scope for method calls although the local trait takes its name. The draft calls
  `<Vec<i64> as Extend<i64>>::extend`.
