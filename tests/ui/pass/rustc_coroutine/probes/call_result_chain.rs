//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=crate

// The field-placement path of layout.rs's `LayoutCalculator::univariant_biased`, from
// `self.cx.data_layout()` to `dl.obj_size_bound()`, in rustc's order: the alignment chosen by
// `pack`, then per field (in memory order, here the slice's) the `pack` clamp, `align_to`, the
// two maxima and `checked_add(.., dl)` with its `ok_or(..)?`, then `repr.align`'s maximum,
// `align_to` and the bound. A field is its size, alignment and `max_repr_align`.
// `checked_add` and `obj_size_bound` require the default pointer size of `dl` to be 2, 4 or 8
// bytes, which follows from the caller's `requires` and `data_layout`'s `ensures`. Each call's
// result gets an unknown over every variable in scope, so the fact has to pass through the
// unknowns of every call before the requirement. The loop's invariant states it, and the loop
// body is `place_field`, a function with a checked contract, so that the loop's back edge applies
// one call's unknown.
#![feature(new_range_api)]

#[path = "../../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

use rustc_abi::{
    AbiAlign, Align, HasDataLayout, LayoutCalculator, LayoutCalculatorError, ReprOptions, Size,
    TargetDataLayout,
};
use thrust_models::forall;

#[thrust_macros::requires((*dl).default_address_space_pointer_spec.pointer_size.raw == 2
    || (*dl).default_address_space_pointer_spec.pointer_size.raw == 4
    || (*dl).default_address_space_pointer_spec.pointer_size.raw == 8)]
#[thrust_macros::ensures(true)]
fn place_field(
    offset: Size,
    align: Align,
    max_repr_align: Option<Align>,
    field: (Size, AbiAlign, Option<Align>),
    pack: Option<Align>,
    dl: &TargetDataLayout,
) -> Result<(Size, Align, Option<Align>), LayoutCalculatorError<Size>> {
    let (field_size, field_align, field_max_repr_align) = field;
    let field_align = if let Some(pack) = pack {
        field_align.min(AbiAlign::new(pack))
    } else {
        field_align
    };
    let offset = offset.align_to(field_align.abi);
    let align = align.max(field_align.abi);
    let max_repr_align = max_repr_align.max(field_max_repr_align);
    let offset = offset
        .checked_add(field_size, dl)
        .ok_or(LayoutCalculatorError::SizeOverflow)?;
    Ok((offset, align, max_repr_align))
}

#[thrust_macros::requires(forall(|dl: TargetDataLayout| C::dl_of(*calc, dl)
    ==> dl.default_address_space_pointer_spec.pointer_size.raw == 2
    || dl.default_address_space_pointer_spec.pointer_size.raw == 4
    || dl.default_address_space_pointer_spec.pointer_size.raw == 8))]
#[thrust_macros::ensures(true)]
fn place_fields<C: HasDataLayout>(
    calc: &LayoutCalculator<C>,
    fields: &[(Size, AbiAlign, Option<Align>)],
    repr: &ReprOptions,
) -> Result<Size, LayoutCalculatorError<Size>> {
    let dl = calc.cx.data_layout();
    let pack = repr.pack;
    let mut align = if pack.is_some() {
        dl.i8_align
    } else {
        dl.aggregate_align
    };
    let mut max_repr_align = repr.align;
    let mut offset = Size::ZERO;
    let mut i = 0;
    while i < fields.len() {
        thrust_macros::invariant!(|dl: &TargetDataLayout| (*dl).default_address_space_pointer_spec.pointer_size.raw == 2
            || (*dl).default_address_space_pointer_spec.pointer_size.raw == 4
            || (*dl).default_address_space_pointer_spec.pointer_size.raw == 8);
        (offset, align, max_repr_align) =
            place_field(offset, align, max_repr_align, fields[i], pack, dl)?;
        i += 1;
    }
    if let Some(repr_align) = repr.align {
        align = align.max(repr_align);
    }
    let size = offset.align_to(align);
    if size.bytes() >= dl.obj_size_bound() {
        return Err(LayoutCalculatorError::SizeOverflow);
    }
    Ok(size)
}

fn main() {}
