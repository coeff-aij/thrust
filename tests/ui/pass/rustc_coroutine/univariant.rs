//@ignore-on-host: no answer at 300 s, also with the postcondition replaced by `true`: PCSat stalls in preprocessing, eliminating loop-head unknowns (see README.md)
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
// Stage 6 of the rustc-coroutine verification target: `LayoutCalculator::univariant` of rustc_abi's
// layout.rs, with `univariant_biased` trusted on its contract (its body is the univariant_biased
// root's).
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage and
// drives it.
#![feature(custom_inner_attributes)]
#![feature(new_range_api)]
#![thrust::verify_only("rustc_abi::layout::LayoutCalculator::univariant", "crate")]

#[path = "../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

use rustc_abi::{HasDataLayout, LayoutCalculator, LayoutRef, ReprOptions, StructKind};
use rustc_index::{Idx, IndexSlice};

// A caller of `univariant` that establishes its precondition, the size bound included.
#[thrust_macros::context]
#[thrust_macros::requires(
    LayoutCalculator::<Cx>::layout_pre::<FieldIdx, VariantIdx, F>(*calc, fields, kind)
        && LayoutCalculator::<Cx>::fits_in_any_order::<FieldIdx, VariantIdx, F>(*calc, fields, repr, kind)
)]
#[thrust_macros::ensures(true)]
fn drive<
    'a,
    Cx: HasDataLayout,
    FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
    VariantIdx: Idx,
    F: LayoutRef<'a, FieldIdx, VariantIdx> + thrust_models::Model<Ty: PartialEq>,
>(
    calc: &LayoutCalculator<Cx>,
    fields: &IndexSlice<FieldIdx, F>,
    repr: &ReprOptions,
    kind: StructKind,
) {
    let _ = calc.univariant(fields, repr, kind);
}

fn main() {}
