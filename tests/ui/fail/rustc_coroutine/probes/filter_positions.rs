//@error-in-other-file: Unsat
//@ignore-on-host: the pass twin's entry gets no answer from the solver (README.md); the loop is refuted
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=take_per_accepted
// The fail twin of probes/filter_positions.rs: the pass takes an item at every entry, accepted or
// not, so it can run out.
#![feature(new_range_api)]

#[path = "../../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

use thrust_models::model::{Array, Int};
use case_study::USize;
use thrust_models::{exists, forall};

use case_study::iter::{Filter, collect_index_vec};
use rustc_index::{IndexVec, SliceIter};

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

#[thrust_macros::context]
#[thrust_macros::requires(forall(|k: Int| !(0 <= k && k < fields.len()) || fields[k] < flags.len()))]
#[thrust_macros::ensures(true)]
fn take_per_accepted(fields: &[usize], flags: &[bool]) {
    let accepted: IndexVec<u32, &usize> = collect_index_vec(Filter::new(
        SliceIter::new(fields),
        thrust_macros::closure!(
            captures(flags: &[bool]),
            requires(**l < flags.len()),
            ensures(result == flags[**l]),
            move |l: &&usize| -> bool { flags[**l] },
        ),
    ));
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
        if flags[fields[i]] || !flags[fields[i]] {
            // In place of `offsets_and_memory_index.next().unwrap()`.
            assert!(taken < accepted.len());
            taken += 1;
        }
        i += 1;
    }
}

fn main() {}
