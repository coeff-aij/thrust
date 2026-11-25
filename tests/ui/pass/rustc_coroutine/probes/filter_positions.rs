//@ignore-on-host: the loop and the lemma `entry_enumerates` verify; the entry, the lemma instantiated at `collect`'s witnesses, gets no answer from the solver (README.md)
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=take_per_accepted,entry_enumerates
// The second pass of `layout()` over a variant's fields (stage 7, `combined_offsets`): the items a
// `Filter` collects are as many as the entries its closure accepts, so a pass that takes one item
// per accepted entry never runs out. The count follows from Creusot's index map of the case
// study's `Filter`, which the pass walks with the number taken so far, without a count function.
#![feature(new_range_api)]

#[path = "../../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

use thrust_models::model::{Array, Int, Mut, Seq};
use case_study::USize;
use thrust_models::{exists, forall};

use case_study::iter::{Filter, collect_index_vec};
use rustc_index::IndexVec;

// `f` lists in increasing order the positions below `fields.len()` whose entry `flags` accepts,
// and `m` of them.
#[thrust_macros::predicate]
fn enumerates(f: Array<Int, Int>, m: USize, fields: &[usize], flags: &[bool]) -> bool {
    forall(|j: Int| !(0 <= j && j < m) || (0 <= f[j] && f[j] < fields.len()))
        && forall(|i: Int, j: Int| !(0 <= i && i < j && j < m) || f[i] < f[j])
        && forall(|k: Int| !(0 <= k && k < fields.len())
            || ((!exists(|j: Int| 0 <= j && j < m && f[j] == k) || flags[fields[k]])
                && (exists(|j: Int| 0 <= j && j < m && f[j] == k) || !flags[fields[k]])))
}

// The entry, from `collect`'s postcondition: the index map that `Filter::produces` gives
// enumerates the accepted positions, since `completed` gives the rest of `fields` as rejected.
// The witnesses are universally quantified here, so the caller instantiates them with those of
// `collect`'s postcondition.
#[thrust_macros::context]
#[thrust_macros::requires((*it).0.0 == *fields && (*it).0.1 == 0)]
#[thrust_macros::requires(forall(|s: Seq<&USize>, k: Int, r: bool|
    !(0 <= k && k < s.len() && Filter::<core::slice::Iter<'a, usize>, P>::answers((*it).1, s, k, r))
        || r == flags[*s[k]]))]
#[thrust_macros::ensures(forall(|v: Seq<&USize>, mid: <Filter<core::slice::Iter<'a, usize>, P> as thrust_models::Model>::Ty,
        fin: <Filter<core::slice::Iter<'a, usize>, P> as thrust_models::Model>::Ty, s: Seq<&USize>, f: Array<Int, Int>|
    !(Filter::<core::slice::Iter<'a, usize>, P>::produces_at(*it, v, mid, s, f)
        && <Filter<core::slice::Iter<'a, usize>, P> as IteratorSpec>::completed(Mut::new(mid, fin)))
        || enumerates(f, v.len(), fields, flags)))]
#[thrust_macros::lemma]
fn entry_enumerates<'a, P: Fn(&&'a usize) -> bool>(it: &Filter<core::slice::Iter<'a, usize>, P>, fields: &'a [usize], flags: &[bool]) {}

#[thrust_macros::context]
#[thrust_macros::requires(forall(|k: Int| !(0 <= k && k < fields.len()) || fields[k] < flags.len()))]
#[thrust_macros::ensures(true)]
fn take_per_accepted(fields: &[usize], flags: &[bool]) {
    let filter = Filter::new(
        fields.iter(),
        thrust_macros::closure!(
            captures(flags: &[bool]),
            requires(**l < flags.len()),
            ensures(result == flags[**l]),
            move |l: &&usize| -> bool { flags[**l] },
        ),
    );
    entry_enumerates(&filter, fields, flags);
    let accepted: IndexVec<u32, &usize> = collect_index_vec(filter);
    let mut taken: usize = 0;
    let mut i: usize = 0;
    while i < fields.len() {
        thrust_macros::invariant!(
            |i: usize, taken: usize, fields: &[usize], flags: &[bool], accepted: IndexVec<u32, &usize>|
                forall(|k: Int| !(0 <= k && k < fields.len()) || fields[k] < flags.len())
                    && i <= fields.len()
                    && taken <= accepted.len()
                    && exists(|f: Array<Int, Int>| enumerates(f, accepted.len(), fields, flags))
                    && forall(|f: Array<Int, Int>| !enumerates(f, accepted.len(), fields, flags)
                        || ((taken == accepted.len() || f[taken] >= i)
                            && (taken == 0 || f[taken - 1] < i)))
        );
        if flags[fields[i]] {
            // In place of `offsets_and_memory_index.next().unwrap()`.
            assert!(taken < accepted.len());
            taken += 1;
        }
        i += 1;
    }
}

fn main() {}
