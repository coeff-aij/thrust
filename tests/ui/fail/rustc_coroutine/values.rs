//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@no-rustfix
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
// Stage 1 of the rustc-coroutine verification target: the value types of rustc_abi's lib.rs
// (Size/Align/Integer/Float/Primitive/Scalar/Niche/TargetDataLayout) and rustc_hashes, with the
// slice iterator and `find` that `pointer_size_in` uses (rewrites.md R9).
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage and
// drives it.
#![feature(custom_inner_attributes)]
#![feature(new_range_api)]
#![thrust::verify_only("rustc_hashes", "rustc_abi", "rustc_index::slice::SliceIter", "case_study::iter::SliceIter")]

#[path = "../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

use rustc_abi::*;

fn main() {
    // `Align::ONE` / `Align::EIGHT` / `Size::ZERO` are spelled out as struct
    // literals: reading an associated constant of a newtype ADT makes Thrust
    // panic with "not implemented: const: Scalar(0x03), ty: Align"
    // (src/analyze/basic_block.rs:445).
    let dl = TargetDataLayout {
        endian: Endian::Little,
        i1_align: Align { pow2: 0 },
        i8_align: Align { pow2: 0 },
        i16_align: Align { pow2: 0 },
        i32_align: Align { pow2: 0 },
        i64_align: Align { pow2: 3 },
        i128_align: Align { pow2: 3 },
        f16_align: Align { pow2: 0 },
        f32_align: Align { pow2: 0 },
        f64_align: Align { pow2: 3 },
        f128_align: Align { pow2: 3 },
        aggregate_align: Align { pow2: 0 },
        vector_align: Vec::new(),
        default_address_space: AddressSpace(0),
        default_address_space_pointer_spec: PointerSpec {
            pointer_size: Size { raw: 8 },
            pointer_align: Align { pow2: 3 },
            pointer_offset: Size { raw: 0 },
            _is_fat: false,
        },
        address_space_info: Vec::new(),
        instruction_address_space: AddressSpace(0),
        c_enum_min_size: Integer::I32,
    };

    // `obj_size_bound` checks the inlined `dl_wf` requires, `pointer_size_in`
    // checks the address-space requires, and `Align::bytes` / `Size::bits`
    // check their `ensures`.
    assert!(dl.obj_size_bound() >= 1);
    // The fail twin: `AddressSpace(1)` is neither `dl.default_address_space` nor listed in
    // `dl.address_space_info`, so the lookup of `pointer_size_in` falls through to its `panic!`.
    let ptr = dl.pointer_size_in(AddressSpace(1));
    assert!(ptr.bits() == ptr.bytes() * 8);
    assert!(dl.i64_align.bytes() >= 1);
    let _ = Integer::I32.size();
    let _ = Integer::I32.align(&dl);
    let _ = Primitive::Int(Integer::I32, true).size(&dl);
}
