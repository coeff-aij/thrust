//! The trusted lemma skeleton of stage 7 (README.md of the stage files), not yet called from
//! `layout()`.

use crate::thrust_models;
use thrust_models::forall;

use crate::rustc_index::{Idx, IndexVec};
use crate::case_study::USize;

// If `order` is a permutation of `0..n` (an `IndexVec<u32, FieldIdx>` of
// length `n`, injective, all values `< n`), then the sub-sequence of it at or
// above `b_start` (`order_b`, built the same way `layout()` builds
// `in_memory_order_b`: `order[k] - b_start` for each `order[k] >= b_start`)
// has exactly `n - b_start` entries, and those entries are themselves a
// permutation of `0..n - b_start`.
// An element of the shared `(array, length)` model is
// `<FieldIdx as Model>::Ty`, not a real `FieldIdx`, so `Idx::index()` is not
// callable on it; `Idx::index_is` carries the same fact.
#[thrust::trusted]
#[thrust_macros::requires(
    order.len() == n
        && forall(|k: usize, i: USize|
            !(0 <= k && k < n && <FieldIdx as Idx>::index_is(order[k], i))
                || i < n)
        && forall(|k: usize, k2: usize, i: USize|
            !(0 <= k && k < n && 0 <= k2 && k2 < n && !(k == k2)
                && <FieldIdx as Idx>::index_is(order[k], i))
                || !<FieldIdx as Idx>::index_is(order[k2], i))
        && b_start <= n
)]
#[thrust_macros::ensures(
    result.len() == n - b_start
        && forall(|k: usize, i: USize|
            !(0 <= k && k < result.len() && <FieldIdx as Idx>::index_is(result[k], i))
                || i < n - b_start)
        && forall(|k: usize, k2: usize, i: USize|
            !(0 <= k && k < result.len() && 0 <= k2 && k2 < result.len() && !(k == k2)
                && <FieldIdx as Idx>::index_is(result[k], i))
                || !<FieldIdx as Idx>::index_is(result[k2], i))
)]
fn lemma_permutation_split<FieldIdx: Idx>(
    order: IndexVec<u32, FieldIdx>,
    n: usize,
    b_start: usize,
) -> IndexVec<u32, FieldIdx> {
    unimplemented!()
}
