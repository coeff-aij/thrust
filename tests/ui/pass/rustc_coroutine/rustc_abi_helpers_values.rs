//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::ReprFlags::bits,rustc_abi::ReprFlags::contains,rustc_abi::ReprFlags::intersects,rustc_abi::_extern_spec_repr_options_default,rustc_abi::ReprOptions::transparent,rustc_abi::ReprOptions::inhibit_newtype_abi_optimization,rustc_abi::ReprOptions::inhibit_struct_field_reordering,rustc_abi::ReprOptions::can_randomize_type_layout,rustc_abi::TargetDataLayout::obj_size_bound,rustc_abi::TargetDataLayout::pointer_size,rustc_abi::TargetDataLayout::pointer_size_in,rustc_abi::TargetDataLayout::pointer_align_in,rustc_abi::round_up,rustc_abi::TargetDataLayout::data_layout,rustc_abi::{impl}::data_layout,rustc_abi::Size::from_bits,rustc_abi::Size::from_bytes,rustc_abi::Size::bytes,rustc_abi::Size::bits,rustc_abi::Size::align_to,rustc_abi::Size::checked_add,rustc_abi::Size::unsigned_int_max,rustc_abi::Size::add,rustc_abi::Size::add_assign,rustc_abi::Align::bytes,rustc_abi::AbiAlign::new,rustc_abi::AbiAlign::min,rustc_abi::Integer::size,rustc_abi::Integer::align,rustc_abi::Integer::fit_unsigned,rustc_abi::Float::size,rustc_abi::Float::align,rustc_abi::first_entry,rustc_abi::size_in_total,rustc_abi::Primitive::size,rustc_abi::Primitive::align,rustc_abi::Scalar::primitive,rustc_abi::Scalar::align,rustc_abi::Scalar::size,rustc_abi::BackendRepr::is_unsized,rustc_abi::Niche::from_scalar,rustc_abi::LayoutData::is_unsized,rustc_abi::VariantLayout::from_layout,rustc_abi::Size::compares_functional,rustc_abi::Align::compares_functional,rustc_abi::Niche::available
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// Generated root: the call graph of `layout()` reaches the functions of row rustc_abi in module(s) listed below; see README.md.
#![feature(new_range_api)]

#[path = "../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

fn main() {}
