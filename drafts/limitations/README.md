# Open limitations re-run on main 3ac8d3f5

Five open issues re-run on a `thrust-rustc` built at 3ac8d3f5 (`CARGO_INCREMENTAL=0 cargo build`),
with the solver fptprove develop 3535ddfa98 with cvc5 1.4.2 through `tests/thrust-pcsat-wrapper`
(8 GB, 2 CPUs per container), a solver timeout of 300 s, one run each. Times are wall times of the
whole `thrust-rustc` run.

Each program is run from the tree root with

```sh
run() {  # run <file.rs> [VAR=value ...]
    f=$1; shift
    env COAR_IMAGE=<image of fptprove develop 3535ddfa98 with cvc5 1.4.2> \
        THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 \
        LD_LIBRARY_PATH=$(rustc --print sysroot)/lib "$@" \
        timeout 360 target/debug/thrust-rustc -Awarnings -C debug-assertions=off --edition 2021 \
        -o /dev/null "$f"
}
```

## #52: `produces_trans` of std's `Filter` and `Chain` (still reproduces)

With `#[thrust::trusted]` removed from the two laws in std.rs, PCSat gives no answer on either:
`Filter::produces_trans` times out at 300 s, and `Chain::produces_trans` answers `unknown` after
67 s. The program is std.rs compiled as a source file (`laws_filter_chain.rs`) with only the law in
question selected; `std_untrusted.rs` is made from std.rs by deleting the `#[thrust::trusted]` line
directly above each `fn produces_trans(`, which matches exactly these two laws:

```sh
awk '/^    #\[thrust::trusted\]$/ { held=$0; next }
     held != "" { if ($0 !~ /^    fn produces_trans\($/) print held; held="" } { print }' \
    std.rs > drafts/limitations/std_untrusted.rs
run drafts/limitations/laws_filter_chain.rs THRUST_NO_INJECT_STD=1 THRUST_VERIFY_ONLY=Filter::produces_trans
run drafts/limitations/laws_filter_chain.rs THRUST_NO_INJECT_STD=1 THRUST_VERIFY_ONLY=Chain::produces_trans
```

## #53: a function returning `impl FnMut` (no longer reproduces)

std's form of `find`, whose closure is built by a nested `fn check<T>(predicate: impl FnMut(&T) ->
bool) -> impl FnMut((), T) -> ControlFlow<T>`, is accepted and verified: `find_nested_check.rs`
(`tests/ui/pass/creusot/generic/std/find.rs` with `check` written so, `check`'s contract left to
inference) answers `sat` in 6 s, and its fail twin `find_nested_check_fail.rs` (`main` claims
`v >= 6`) `unsat` in 4 s. The frontend no longer panics in subtyping. One difference from std's
source remains: `find` must state `<I as Model>::Ty: PartialEq` and
`<<I as Iterator>::Item as Model>::Ty: PartialEq`, which rustc asks for (E0277 at the call of
`try_fold`) once `try_fold`'s closure type is the opaque type. No contract form relates a returned
closure's `pre!`, `post!` and `hist_inv!` to the arguments; inference covers this case.

```sh
run drafts/limitations/find_nested_check.rs
run drafts/limitations/find_nested_check_fail.rs
```

## #51: `for` over std's `Map` with `produced` in the invariant (still reproduces)

`map_for_produced.rs` is `tests/ui/pass/iterators/std_map.rs` with `n == produced.len()` added to
the loop invariant, which then names `iter_old` and `produced`. It times out at 300 s, while
`std_map.rs` itself answers `sat` in 37 s on the same build. Keeping the conjunct needs
`Map::produces_trans` across an iteration, which the `for` desugaring does not supply.

```sh
run drafts/limitations/map_for_produced.rs
run tests/ui/pass/iterators/std_map.rs
```

## #54: Creusot's `Filter` in its own form (no longer reproduces, with one change)

`drafts/creusot/filter_creusot.rs` is now rejected before solving: `produces_trans` calls
`produces_trans_at`, which is not a lemma, and a law's proof may call only lemmas. Marked
`#[thrust_macros::lemma]` (`filter_creusot.rs` here; that line is the only change), the pass side
answers `sat` in 54 s with `Filter::produces_trans` checked through the lemma. The fail twin in
`drafts/creusot/fail/` claims that the first item is below 4, which holds (it is 0), and also
answers `sat` (54 s); `filter_creusot_fail.rs` here claims `v >= 1` instead and answers `unsat` in
6 s.

```sh
run drafts/limitations/filter_creusot.rs
run drafts/limitations/filter_creusot_fail.rs
```

## #28: trait objects (three of the four cases still reproduce)

- Forwarding impl at `T = dyn Tr` (`dyn_forwarding_ref_mut.rs`: `g::<&mut dyn Counter>` through
  `impl<T: ?Sized + Counter> Counter for &mut T`): `sat` in 2 s, and the twin
  `dyn_forwarding_ref_mut_fail.rs` `unsat` in 2 s. No longer reproduces.
- `Box<T>` packed in a generic function with a written contract, at a type with an invariant
  (`dyn_box_generic_written.rs`): `unsat` in 2 s, a correct program rejected; packing
  `Box::new(C { n: 2 })` directly in `main` answers `sat`. Still reproduces.
- A `&mut C` parameter, `C` with an invariant, passed on as `&mut dyn Counter`
  (`dyn_ref_mut_param.rs`): `unsat` in 2 s; calling `x.bump()` directly instead answers `sat`.
  Still reproduces.
- A contract that mentions the receiver, called through `dyn` (`dyn_receiver_contract.rs`):
  rejected before solving, "`Tick::tick` is called through `dyn Tick` in `f`, but its contract
  mentions `self` or `Self`, whose model a trait object does not have". Still reproduces.

```sh
for f in dyn_forwarding_ref_mut dyn_forwarding_ref_mut_fail dyn_box_generic_written \
         dyn_ref_mut_param dyn_receiver_contract; do run drafts/limitations/$f.rs; done
```
