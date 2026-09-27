# A false claim about a `&mut` argument verifies

`alias_mono.rs` proves `*s == v` -- that `s` already held `v` when the function was entered --
after a body that only writes `v` through a handle taken from `s`. No execution satisfies that
postcondition. The solution that verifies it passes every clause of the solution check.

These files are reproduction inputs rather than test cases: each states the verdict that is
correct for its claim, which for four of them is not the verdict the driver gives, so adding
them to `tests/ui/` would pin the current behaviour. They need no change to `src/` or `std.rs`;
each defines its own `Model` impls and extern specs.

## What the files contain

Three state a false claim, four are controls, two state the matching true claim.

`alias_mono.rs` is the smallest. `W`'s model is a bare `Mut<Int>`. `wrap` states that this pair
is the one belonging to the caller's `&mut i64`; `elem` hands the same pair out as a real borrow
and states that `W` does not change, so writing through the borrow constrains the final half
only. `w` then goes out of scope at the end of the function. Nothing here involves iterators,
`Seq`, or generics.

`alias_mono_ctrl.rs` is the same false claim with the write done through a borrow of `s`
directly, and `alias_mono_true.rs` is the same program stating `!s == v`, which does hold.

`alias_generic.rs` and `alias_generic_ctrl.rs` are those two at a type parameter.

`iter_mut_i64.rs` is the shape this was met in. It gives `core::slice::IterMut<'_, i64>` the
model `(Mut<Seq<Int>>, Int)` -- the sequence the iterator was made from, paired with the cursor
-- and extern specs for `iter_mut` and `next`. `iter_mut` states `result.0 == slice`; `next`
hands the element at the cursor out as the `Mut` of the two arrays and states that the first
component does not change. `set_head` writes one element and claims the entry slice already held
it. `iter_mut_i64_true.rs` states the true claim, `iter_mut_generic_ctrl.rs` writes by indexing
instead, and `iter_mut_generic.rs` is the file at a type parameter.

## Measured

Driver `main` 2bf022d built from this tree; solver image `coar:latest` = `d547097023f5` with
`-c ./config/solver/pcsat_tbq_ar.json -p pcsp`. Three runs each, all in agreement. The
sat-check column is a second solve under a config with `check_solution: true`.

| file | correct | measured | sat-check |
| --- | --- | --- | --- |
| `alias_mono.rs` | unsat | **sat** 0.3 s | passed 8, unchecked 0, failed 0 |
| `alias_mono_ctrl.rs` | unsat | unsat 0.3 s | -- |
| `alias_mono_true.rs` | sat | sat 0.3 s | passed 8, unchecked 0, failed 0 |
| `alias_generic.rs` | unsat | **sat** 0.3 s | passed 8, unchecked 0, failed 0 |
| `alias_generic_ctrl.rs` | unsat | unsat 0.3 s | -- |
| `iter_mut_i64.rs` | unsat | **sat** 34 s | unchecked 1, "Z3 undecided" |
| `iter_mut_i64_true.rs` | sat | sat 34 s | unchecked 1, "Z3 undecided" |
| `iter_mut_generic.rs` | unsat | **sat** 0.7 s | unchecked 1, "Z3 undecided" |
| `iter_mut_generic_ctrl.rs` | unsat | unsat 0.3 s | -- |

The two `alias_*.rs` rows are the ones to read: a false claim verifies and its solution is
fully checked. The three `iter_mut_*.rs` rows each leave one clause undecided, which is a known
class for generated queries of this shape, so they do not establish a verdict on their own.

## Running them

    cargo build
    export LD_LIBRARY_PATH="$(rustc --print sysroot)/lib"
    for f in repro/itermut-alias/*.rs; do
      echo "== $f"
      THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest \
        ./target/debug/thrust-rustc -Adead_code -C debug-assertions=false "$f"
    done

The driver exits 0 when the query comes back `sat`, and reports a verification error
otherwise, so the four files whose claim is false are the ones that should fail and do not.

## Three things the files work around

A generic function's body reaches the solver only when a concrete call site instantiates it.
`#[thrust::callable]` together with `requires` and `ensures` is not enough: the query then
contains `main` alone. Each generic file therefore ends with a `main` that calls it at `i64`.

A monomorphic model is written over model types. The model of `i64` is
`thrust_models::model::Int`, so `Mut<Int>`; `Mut<i64>` is an E0271.

`iter_mut_generic.rs` takes its slice from a trusted provider rather than from an array,
because `&mut a[..]` reaches an unmodelled `core::array::index_mut` and panics the driver at
`src/analyze/basic_block.rs:954`. That is unrelated to the defect these files are about.

## Related upstream issues

`alias_mono.rs` and `iter_mut_i64.rs` need no conditional control flow, no closure, no
user-written `Drop` impl, and no `==` between two `&mut` references: `w`/`it` is bound once,
aliased once through a `#[thrust::trusted]` extern function's `ensures`, written through the
alias, and then goes out of scope unconditionally at the end of the function. Checked against
four open upstream issues that also involve a `&mut` prophecy resolving wrongly, none match that
shape:

- **#250** (a conditionally-moved value's drop-flag edge still gets a liveness-derived implicit
  drop) needs a branch (`if cond { f(); }`) and a move that happens on only one path. Neither
  file here branches or moves anything conditionally.
- **#207** (moving a `&mut`-capturing closure out of an aggregate drops its prophecy) needs a
  closure captured by `&mut` and stored in a tuple/struct/enum. Neither file here has a closure;
  `W` and `IterMut`'s models are plain data with no closure field.
- **#215** (a user `Drop` impl's destructor body is never checked) needs a type with a
  hand-written `impl Drop`. Neither `W` nor `core::slice::IterMut` has one; the driver's default,
  implicit end-of-scope handling is what runs here, not `<T as Drop>::drop`.
- **#210** (`==` on two `&mut` references compares the prophecy component too) needs a runtime
  `==` between two independent `&mut` bindings. `elem`'s `ensures` uses `!w == *w` inside a
  trusted function's own postcondition to state that `w`'s prophecy equals its current value; it
  is not a comparison the program executes between two references.

The shared thread across all five is prophecy/drop-point resolution, but the trigger differs in
each case, so this is a fifth, independent way to make the resolution wrong, not a duplicate of
any of the four above.
