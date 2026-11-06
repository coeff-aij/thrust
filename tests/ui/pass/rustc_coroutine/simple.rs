//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=crate,rustc_abi::Size::add_assign,rustc_abi::TargetDataLayout::obj_size_bound,rustc_abi::Size::align_to
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// `LayoutData::scalar_pair` of rustc_abi's layout/simple.rs, assumed on its contract (the
// `scalar_pair` root checks its body), read as `univariant_biased` reads it: `drive` is that code,
// which the `ensures` keeps from panicking.
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage and
// drives it.
#![feature(new_range_api)]

#[path = "../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

use case_study::USize;
use rustc_abi::{FieldsShape, HasDataLayout, LayoutData, Scalar, TargetDataLayout};
use rustc_index::Idx;
use thrust_models::forall;

#[thrust_macros::context]
#[thrust_macros::requires(forall(|dl: TargetDataLayout| Cx::dl_of(*cx, dl) ==> (Scalar::wf_in(a, dl) && Scalar::wf_in(b, dl))))]
#[thrust_macros::requires(forall(|z: USize| z == 0usize ==> <VariantIdx as Idx>::can_new(z)))]
#[thrust_macros::requires(forall(|k: USize| k == 0usize || k == 1usize ==> <FieldIdx as Idx>::can_new(k)))]
#[thrust_macros::ensures(true)]
fn drive<
    Cx: HasDataLayout + thrust_models::Model<Ty: PartialEq>,
    FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
    VariantIdx: Idx + thrust_models::Model<Ty: PartialEq>,
>(
    cx: &Cx,
    a: Scalar,
    b: Scalar,
) {
    let pair = LayoutData::<FieldIdx, VariantIdx>::scalar_pair(cx, a, b);
    let pair_offsets = match pair.fields {
        FieldsShape::Arbitrary {
            ref offsets,
            ref in_memory_order,
        } => {
            assert_eq!(
                in_memory_order.raw,
                [FieldIdx::new(0), FieldIdx::new(1)]
            );
            offsets
        }
        FieldsShape::Primitive
        | FieldsShape::Array { .. }
        | FieldsShape::Union(..) => {
            panic!("encountered a non-arbitrary layout during enum layout")
        }
    };
    assert!(pair_offsets[FieldIdx::new(0)].bytes() == 0);
    let _ = pair_offsets[FieldIdx::new(1)];
}

fn main() {}
