//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@no-rustfix
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=crate
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1 THRUST_CALL_RESULT_DIRECT=1
// Stage 6 of the rustc-coroutine verification target: `LayoutCalculator::univariant` of rustc_abi's
// layout.rs, with `univariant_biased` trusted on its contract (its body is the univariant_biased
// root's).
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage and
// drives it. This twin verifies only `drive`, against `univariant`'s contract, which the pass twin
// verifies.
// Each goal is solved with the clauses it depends on (`THRUST_SPLIT_GOALS`), and a call's result is
// typed by the callee's contract at its arguments (`THRUST_CALL_RESULT_DIRECT`, opt-in; without
// it the goal of `Primitive::size`'s requires for the alternative niche does not answer reliably). The predicates the
// contracts pass on unchanged are `#[thrust::opaque]`, so the solver reads them through the
// contracts instead of unfolding them; `layout_pre` and `dl_of` keep their definitions.
#![feature(new_range_api)]

#[path = "../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

use rustc_abi::{HasDataLayout, LayoutCalculator, LayoutData, ReprOptions, StructKind};
use rustc_index::{Idx, IndexSlice};

// The fail twin: the caller of `univariant` does not establish that `F`'s `deref` is a function
// (`deref_functional`), which `univariant`'s `requires` demands.
#[thrust_macros::context]
#[thrust_macros::requires(
    LayoutCalculator::<Cx>::layout_pre::<FieldIdx, VariantIdx, F>(*calc, fields, kind)
        && LayoutCalculator::<Cx>::fits_in_any_order::<FieldIdx, VariantIdx, F>(*calc, fields, repr, kind)
)]
#[thrust_macros::ensures(true)]
fn drive< //~ ERROR: Unsat
    'a,
    Cx: HasDataLayout,
    FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
    VariantIdx: Idx,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + core::fmt::Debug + Copy + thrust_models::Model<Ty: PartialEq>,
>(
    calc: &LayoutCalculator<Cx>,
    fields: &IndexSlice<FieldIdx, F>,
    repr: &ReprOptions,
    kind: StructKind,
) {
    let _ = calc.univariant(fields, repr, kind);
}

fn main() {}
