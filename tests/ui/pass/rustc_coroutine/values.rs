//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// Stage 1 of the rustc-coroutine verification target: the value types of rustc_abi's lib.rs
// (Size/Align/Integer/Float/Primitive/Scalar/Niche/TargetDataLayout); rustc_hashes is the
// `hashes.rs` root's.
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage and
// drives it.
// Each goal is solved with the clauses it depends on (`THRUST_SPLIT_GOALS`).
#![feature(new_range_api)]

#[path = "../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

use rustc_abi::*;

#[thrust::reveal(rustc_abi::TargetDataLayout::pointer_space_ok, rustc_abi::TargetDataLayout::pointer_size_is)]
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

    // The calls check that `dl` meets what `obj_size_bound` and `pointer_size_in`
    // require; the asserts, what those functions, `Align::bytes` and `Size::bits`
    // return.
    assert!(dl.obj_size_bound() >= 1);
    let ptr = dl.pointer_size_in(AddressSpace(0));
    assert!(ptr.bits() == ptr.bytes() * 8);
    assert!(dl.i64_align.bytes() >= 1);
    let _ = Integer::I32.size();
    let _ = Integer::I32.align(&dl);
    let _ = Primitive::Int(Integer::I32, true).size(&dl);
}
