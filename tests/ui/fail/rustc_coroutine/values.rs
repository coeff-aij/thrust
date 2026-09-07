//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
// Adapted from rust-lang/rust
// commit: 89a99936d9e76a50e8df622e7242190841fd871b
// Licensed under MIT OR Apache-2.0
//
// Stage 1 of the rustc-coroutine verification target: the value types
// (Size/Align/Integer/Float/Primitive/Scalar/Niche/TargetDataLayout).
// The items are extracted verbatim from tests/ui/pass/traits/rustc-coroutine.rs;
// only attributes and `Model` impls are added.

use std::convert::TryInto;
use std::ops::{Add, AddAssign, Deref};
use thrust_models::forall;

#[derive(Copy, Clone, /*Debug,*/ PartialEq, Eq)]
pub struct PointerSpec {
    pointer_size: Size,

    pointer_align: Align,

    pointer_offset: Size,

    _is_fat: bool,
}

// `PartialEq, Eq` commented out: the derived `eq` for this 18-field struct
// makes the backend solver diverge -- with the derive in place, even a file
// that contains nothing but these type declarations and an empty `main` hits
// `verification error: Timeout(60s)` (and `Unknown` once specs are added).
// Removing the two `Vec` fields does not help, so it is the width of the
// derived `&&` chain, not the `Vec` model.
#[derive(/*Debug,*/ /*PartialEq, Eq*/)]
pub struct TargetDataLayout {
    pub endian: Endian,
    pub i1_align: Align,
    pub i8_align: Align,
    pub i16_align: Align,
    pub i32_align: Align,
    pub i64_align: Align,
    pub i128_align: Align,
    pub f16_align: Align,
    pub f32_align: Align,
    pub f64_align: Align,
    pub f128_align: Align,
    pub aggregate_align: Align,

    pub vector_align: Vec<(Size, Align)>,

    pub default_address_space: AddressSpace,
    pub default_address_space_pointer_spec: PointerSpec,

    address_space_info: Vec<(AddressSpace, PointerSpec)>,

    pub instruction_address_space: AddressSpace,

    pub c_enum_min_size: Integer,
}

// The intended specs use two predicates, `dl_wf(dl)` (the default pointer size
// is 2, 4 or 8 bytes, so `obj_size_bound` cannot hit its `panic!` arm) and
// `prim_wf(p, dl)` (a `Primitive::Pointer(a)` only names the default address
// space, so `pointer_size_in` / `pointer_align_in` cannot panic).
//
// They are written out inline in the `requires` below instead of as
// `#[thrust_macros::predicate]`s: a predicate body must be a raw SMT-LIB2
// string literal (`thrust-macros/src/spec.rs:18-21`, and
// `src/analyze/local_def.rs:152` panics with "invalid predicate definition: no
// string literal was found." otherwise), and writing these out in SMT needs the
// generated projector names for an 18-field datatype. `requires` / `ensures`
// are formula expressions, so the same conditions can be written in Rust there.
//
// The second half of the intended `dl_wf` -- every entry of
// `address_space_info` has a pointer size of at most 8 bytes -- is NOT
// expressible at all: the model of `TargetDataLayout` is the struct itself, so
// `dl.address_space_info` has the ordinary Rust type `Vec<..>` in a formula and
// the `Seq` accessors are rejected by rustc ("no field `length` on type
// `std::vec::Vec<..>`", likewise `array`). Only the default pointer spec is
// constrained; the other entries are never read because `pointer_size_in` /
// `pointer_align_in` require the default address space.

#[thrust_macros::context]
impl TargetDataLayout {
    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(((*self).default_address_space_pointer_spec.pointer_size.raw == 2
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 4
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 8))]
    #[thrust_macros::ensures(result >= 1)]
    pub fn obj_size_bound(&self) -> u64 {
        match self.pointer_size().bits() {
            16 => 1 << 15,
            32 => 1 << 31,
            64 => 1 << 61,
            bits => panic!("obj_size_bound: unknown pointer bit size {bits}"),
        }
    }

    #[inline]
    pub fn pointer_size(&self) -> Size {
        self.default_address_space_pointer_spec.pointer_size
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(((*self).default_address_space_pointer_spec.pointer_size.raw == 2
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 4
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 8)
        && c == (*self).default_address_space)]
    #[thrust_macros::ensures(true)]
    pub fn pointer_size_in(&self, c: AddressSpace) -> Size {
        if c == self.default_address_space {
            return self.default_address_space_pointer_spec.pointer_size;
        }

        if let Some(e) = self.address_space_info.iter().find(|(a, _)| a == &c) {
            e.1.pointer_size
        } else {
            panic!("Use of unknown address space");
        }
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(((*self).default_address_space_pointer_spec.pointer_size.raw == 2
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 4
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 8)
        && c == (*self).default_address_space)]
    #[thrust_macros::ensures(true)]
    pub fn pointer_align_in(&self, c: AddressSpace) -> AbiAlign {
        AbiAlign::new(if c == self.default_address_space {
            self.default_address_space_pointer_spec.pointer_align
        } else if let Some(e) = self.address_space_info.iter().find(|(a, _)| a == &c) {
            e.1.pointer_align
        } else {
            panic!("Use of unknown address space");
        })
    }
}

// `ensures(*result == *self)` (the spec the `TargetDataLayout` impl wants)
// does not typecheck at the trait level -- `*self` has the opaque type
// `<Self as Model>::Ty` there, so rustc reports "expected `TargetDataLayout`,
// found associated type `<Self as thrust_models::Model>::Ty`". The same spec
// would be ill-typed for the `&TargetDataLayout` impl anyway, so the two
// impls cannot share it.
//
// The by-value trait predicate below sidesteps that: `dl_of`'s own arguments
// are lowered per its own (fresh) signature, so `Self::dl_of(*self, *result)`
// typechecks for both impls, and each defines it as `"(= self_ dl)"`. Calling
// `dl_of` directly (as `data_layout`'s own `ensures` does) verifies.
//
// Relating a *generic* `cx: &C` to the layout `dl_of` names needs quantifying
// over it, e.g.
//   requires(forall(|dl: TargetDataLayout| C::dl_of(*cx, dl) ==> prim_wf(self, dl)))
// This typechecks and does not crash the backend (an earlier note here about
// a hard SMT2 parser failure came from a stale local `coar:latest` tag and
// does not reproduce with the pinned image), but it does not verify either:
// isolated to a minimal repro with the same shape (a trusted, `requires`-only
// pointer-size lookup called from a generic `size` guarded by exactly this
// forall), pcsat answers `verification error: Unknown { stdout: "unknown" }`
// once the callee's precondition actually has to be discharged through the
// quantifier (as opposed to a body that ignores `dl` -- see `dl_of`'s
// standalone use above, which has no such quantifier and does verify). So
// this stays out of reach for `Primitive::size`/`align` in practice, which
// remain trusted below.
#[thrust_macros::context]
pub trait HasDataLayout {
    #[thrust_macros::predicate]
    fn dl_of(self, dl: TargetDataLayout) -> bool;

    #[thrust_macros::ensures(Self::dl_of(*self, *result))]
    fn data_layout(&self) -> &TargetDataLayout;
}

#[thrust_macros::context]
impl HasDataLayout for TargetDataLayout {
    #[thrust_macros::predicate]
    fn dl_of(self, dl: TargetDataLayout) -> bool {
        "(= self_ dl)"; true
    }

    #[inline]
    fn data_layout(&self) -> &TargetDataLayout {
        self
    }
}

#[thrust_macros::context]
impl HasDataLayout for &TargetDataLayout {
    #[thrust_macros::predicate]
    fn dl_of(self, dl: TargetDataLayout) -> bool {
        "(= self_ dl)"; true
    }

    #[inline]
    fn data_layout(&self) -> &TargetDataLayout {
        (**self).data_layout()
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Endian {
    Little,
    Big,
}

// `PartialOrd, Ord` commented out: the derived `partial_cmp` returns
// `Option<std::cmp::Ordering>`, whose i8 discriminants make rustc ICE inside
// Thrust with "expected int of size 4, but got size 1"
// (rustc_middle/src/ty/consts/int.rs:276).
#[derive(Copy, Clone, PartialEq, Eq, /*PartialOrd, Ord,*/ Hash)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub struct Size {
    raw: u64,
}

#[thrust_macros::context]
impl Size {
    pub const ZERO: Size = Size { raw: 0 };

    #[thrust::trusted]
    #[thrust::callable]
    pub fn from_bits(bits: impl TryInto<u64>) -> Size {
        let bits = bits.try_into().ok().unwrap();
        Size {
            raw: bits.div_ceil(8),
        }
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn from_bytes(bytes: impl TryInto<u64>) -> Size {
        let bytes: u64 = bytes.try_into().ok().unwrap();
        Size { raw: bytes }
    }

    #[inline]
    pub fn bytes(self) -> u64 {
        self.raw
    }

    // Trusted: the body's `checked_mul` panics on overflow. Overflow is out of
    // scope (see the stage plan), so the spec states the no-overflow result.
    #[inline]
    #[thrust::trusted]
    #[thrust_macros::ensures(result == self.raw * 8)]
    pub fn bits(self) -> u64 {
        #[cold]
        #[thrust::trusted]
        #[thrust::callable]
        fn overflow(bytes: u64) -> ! {
            panic!("Size::bits: {bytes} bytes in bits doesn't fit in u64")
        }

        self.bytes()
            .checked_mul(8)
            .unwrap_or_else(|| overflow(self.bytes()))
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn align_to(self, align: Align) -> Size {
        let mask = align.bytes() - 1;
        Size::from_bytes((self.bytes() + mask) & !mask)
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn checked_add<C: HasDataLayout>(self, offset: Size, cx: &C) -> Option<Size> {
        let dl = cx.data_layout();

        let bytes = self.bytes().checked_add(offset.bytes())?;

        if bytes < dl.obj_size_bound() {
            Some(Size::from_bytes(bytes))
        } else {
            None
        }
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn unsigned_int_max(&self) -> u128 {
        u128::MAX >> (128 - self.bits())
    }
}

impl Add for Size {
    type Output = Size;
    // Trusted. The intended spec is `result.raw == self.raw + other.raw` (the
    // body panics on overflow, which is out of scope), but Thrust cannot put a
    // spec on an impl of an external trait: `#[thrust_macros::ensures]` here
    // expands to `_thrust_ensures_add`, which is "not a member of trait `Add`".
    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    fn add(self, other: Size) -> Size {
        Size::from_bytes(self.bytes().checked_add(other.bytes()).unwrap_or_else(|| {
            panic!(
                "Size::add: {} + {} doesn't fit in u64",
                self.bytes(),
                other.bytes()
            )
        }))
    }
}

impl AddAssign for Size {
    #[inline]
    fn add_assign(&mut self, other: Size) {
        *self = *self + other;
    }
}

// `PartialOrd, Ord` commented out: the derived `partial_cmp` returns
// `Option<std::cmp::Ordering>`, whose i8 discriminants make rustc ICE inside
// Thrust with "expected int of size 4, but got size 1"
// (rustc_middle/src/ty/consts/int.rs:276).
#[derive(Copy, Clone, PartialEq, Eq, /*PartialOrd, Ord,*/ Hash)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub struct Align {
    pow2: u8,
}

#[thrust_macros::context]
impl Align {
    pub const ONE: Align = Align { pow2: 0 };
    pub const EIGHT: Align = Align { pow2: 3 };

    pub const MAX: Align = Align { pow2: 29 };

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::ensures(result >= 1)]
    pub const fn bytes(self) -> u64 {
        1 << self.pow2
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub struct AbiAlign {
    pub abi: Align,
}

impl AbiAlign {
    #[inline]
    pub fn new(align: Align) -> AbiAlign {
        AbiAlign { abi: align }
    }

    // `min` / `max` commented out: they call `Ord::min` / `Ord::max` on
    // `Align`, whose `Ord` derive had to be dropped (see the note on `Align`),
    // so they no longer compile. They are not needed by this stage.
    // #[inline]
    // pub fn min(self, other: AbiAlign) -> AbiAlign {
    //     AbiAlign {
    //         abi: self.abi.min(other.abi),
    //     }
    // }
    //
    // #[inline]
    // pub fn max(self, other: AbiAlign) -> AbiAlign {
    //     AbiAlign {
    //         abi: self.abi.max(other.abi),
    //     }
    // }
}

impl Deref for AbiAlign {
    type Target = Align;

    fn deref(&self) -> &Self::Target {
        &self.abi
    }
}

// `PartialOrd, Ord` commented out: the derived `partial_cmp` returns
// `Option<std::cmp::Ordering>`, whose i8 discriminants make rustc ICE inside
// Thrust with "expected int of size 4, but got size 1"
// (rustc_middle/src/ty/consts/int.rs:276).
#[derive(Copy, Clone, PartialEq, Eq, /*PartialOrd, Ord,*/ Hash /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub enum Integer {
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[thrust_macros::context]
impl Integer {
    #[inline]
    pub fn size(self) -> Size {
        use Integer::*;
        match self {
            I8 => Size::from_bytes(1),
            I16 => Size::from_bytes(2),
            I32 => Size::from_bytes(4),
            I64 => Size::from_bytes(8),
            I128 => Size::from_bytes(16),
        }
    }

    pub fn align<C: HasDataLayout>(self, cx: &C) -> AbiAlign {
        use Integer::*;
        let dl = cx.data_layout();

        AbiAlign::new(match self {
            I8 => dl.i8_align,
            I16 => dl.i16_align,
            I32 => dl.i32_align,
            I64 => dl.i64_align,
            I128 => dl.i128_align,
        })
    }

    // Trusted: the match arms use u128 constants, which exceed the i64 range
    // Thrust models integer literals with.
    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn fit_unsigned(x: u128) -> Integer {
        use Integer::*;
        match x {
            0..=0x0000_0000_0000_00ff => I8,
            0..=0x0000_0000_0000_ffff => I16,
            0..=0x0000_0000_ffff_ffff => I32,
            0..=0xffff_ffff_ffff_ffff => I64,
            _ => I128,
        }
    }
}

// `PartialOrd, Ord` commented out: the derived `partial_cmp` returns
// `Option<std::cmp::Ordering>`, whose i8 discriminants make rustc ICE inside
// Thrust with "expected int of size 4, but got size 1"
// (rustc_middle/src/ty/consts/int.rs:276).
#[derive(Copy, Clone, PartialEq, Eq, /*PartialOrd, Ord,*/ Hash /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub enum Float {
    F16,
    F32,
    F64,
    F128,
}

#[thrust_macros::context]
impl Float {
    pub fn size(self) -> Size {
        use Float::*;

        match self {
            F16 => Size::from_bits(16),
            F32 => Size::from_bits(32),
            F64 => Size::from_bits(64),
            F128 => Size::from_bits(128),
        }
    }

    pub fn align<C: HasDataLayout>(self, cx: &C) -> AbiAlign {
        use Float::*;
        let dl = cx.data_layout();

        AbiAlign::new(match self {
            F16 => dl.f16_align,
            F32 => dl.f32_align,
            F64 => dl.f64_align,
            F128 => dl.f128_align,
        })
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub enum Primitive {
    Int(Integer, bool),
    Float(Float),
    Pointer(AddressSpace),
}

#[thrust_macros::context]
impl Primitive {
    // Trusted. The body's `dl.pointer_size_in(a)` needs
    // `a == (*dl).default_address_space`, and `dl` comes out of the generic
    // `cx.data_layout()`. `data_layout` now has a trait-level postcondition
    // (`Self::dl_of(*self, *result)`, see the note on `HasDataLayout`), but
    // relating a generic `cx: &C` to the layout `dl_of` names needs a
    // `requires(forall(|dl: TargetDataLayout| C::dl_of(*cx, dl) ==> ..))`.
    // That typechecks, but a minimal repro of the same shape (a trusted,
    // `requires`-only callee gated by exactly this forall, called from a
    // generic function) gets `verification error: Unknown { stdout: "unknown"
    // }` from pcsat once the callee's precondition actually needs discharging
    // through the quantifier -- see the note on `HasDataLayout` for the
    // repro. So this stays unprovable in practice.
    #[thrust::trusted]
    #[thrust::callable]
    pub fn size<C: HasDataLayout>(self, cx: &C) -> Size {
        use Primitive::*;
        let dl = cx.data_layout();

        match self {
            Int(i, _) => i.size(),
            Float(f) => f.size(),
            Pointer(a) => dl.pointer_size_in(a),
        }
    }

    // Trusted for the same reason as `size` above.
    #[thrust::trusted]
    #[thrust::callable]
    pub fn align<C: HasDataLayout>(self, cx: &C) -> AbiAlign {
        use Primitive::*;
        let dl = cx.data_layout();

        match self {
            Int(i, _) => i.align(dl),
            Float(f) => f.align(dl),
            Pointer(a) => dl.pointer_align_in(a),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub struct WrappingRange {
    pub start: u128,
    pub end: u128,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub enum Scalar {
    Initialized {
        value: Primitive,

        valid_range: WrappingRange,
    },
    Union {
        value: Primitive,
    },
}

#[thrust_macros::context]
impl Scalar {
    pub fn primitive(&self) -> Primitive {
        match *self {
            Scalar::Initialized { value, .. } | Scalar::Union { value } => value,
        }
    }

    pub fn align(self, cx: &impl HasDataLayout) -> AbiAlign {
        self.primitive().align(cx)
    }

    pub fn size(self, cx: &impl HasDataLayout) -> Size {
        self.primitive().size(cx)
    }
}

// `Debug` commented out: the derived `fmt` reaches `std::fmt::Formatter`, whose
// `dyn std::fmt::Write` field makes Thrust panic with
// "not implemented: ty: dyn [Binder { value: Trait(std::fmt::Write), .. }]"
// (src/refine/template.rs:823). Dropping it forces the two `{c:?}` panic
// messages below to lose their argument, the same rewrite the target file
// already applies elsewhere ("dropped panic messages").
#[derive(Copy, Clone, /*Debug,*/ PartialEq, Eq, /*PartialOrd, Ord,*/ Hash)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub struct AddressSpace(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub struct Niche {
    pub offset: Size,
    pub value: Primitive,
    pub valid_range: WrappingRange,
}

#[thrust_macros::context]
impl Niche {
    pub fn from_scalar<C: HasDataLayout>(cx: &C, offset: Size, scalar: Scalar) -> Option<Self> {
        let Scalar::Initialized { value, valid_range } = scalar else {
            return None;
        };
        let niche = Niche {
            offset,
            value,
            valid_range,
        };
        if niche.available(cx) > 0 {
            Some(niche)
        } else {
            None
        }
    }

    // Trusted; the intended `requires` is `prim_wf(self.value, *cx.data_layout())`,
    // which is not expressible for a generic `cx` (see `HasDataLayout`).
    #[thrust::trusted]
    #[thrust::callable]
    pub fn available<C: HasDataLayout>(&self, cx: &C) -> u128 {
        let Self {
            value,
            valid_range: v,
            ..
        } = *self;
        let size = value.size(cx);
        assert!(size.bits() <= 128);
        let max_value = size.unsigned_int_max();

        let niche = v.end.wrapping_add(1)..v.start;
        niche.end.wrapping_sub(niche.start) & max_value
    }
}

impl thrust_models::Model for PointerSpec {
    type Ty = Self;
}
impl thrust_models::Model for TargetDataLayout {
    type Ty = Self;
}
impl thrust_models::Model for Endian {
    type Ty = Self;
}
impl thrust_models::Model for Size {
    type Ty = Self;
}
impl thrust_models::Model for Align {
    type Ty = Self;
}
impl thrust_models::Model for AbiAlign {
    type Ty = Self;
}
impl thrust_models::Model for Integer {
    type Ty = Self;
}
impl thrust_models::Model for Float {
    type Ty = Self;
}
impl thrust_models::Model for Primitive {
    type Ty = Self;
}
impl thrust_models::Model for WrappingRange {
    type Ty = Self;
}
impl thrust_models::Model for Scalar {
    type Ty = Self;
}
impl thrust_models::Model for AddressSpace {
    type Ty = Self;
}
impl thrust_models::Model for Niche {
    type Ty = Self;
}

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
    // The fail twin: `AddressSpace(1)` is not `dl.default_address_space`, so
    // the `requires` of `pointer_size_in` (the address space must be the
    // default one, otherwise the lookup falls through to its `panic!`) fails.
    let ptr = dl.pointer_size_in(AddressSpace(1));
    assert!(ptr.bits() == ptr.bytes() * 8);
    assert!(dl.i64_align.bytes() >= 1);
    let _ = Integer::I32.size();
    let _ = Integer::I32.align(&dl);
    let _ = Primitive::Int(Integer::I32, true).size(&dl);
}
