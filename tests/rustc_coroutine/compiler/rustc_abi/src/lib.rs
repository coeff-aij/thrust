// #![cfg_attr(feature = "nightly", allow(internal_features))]
// #![cfg_attr(feature = "nightly", feature(rustc_attrs))]
// #![cfg_attr(feature = "nightly", feature(step_trait))]

use crate::thrust_models;
use std::fmt;
use std::num::NonZeroUsize;
use std::ops::{Add, AddAssign, Deref};
use std::range::RangeInclusive;

use thrust_models::model::{BitVec, Int, Seq};
use thrust_models::{exists, forall};

use crate::rustc_hashes::Hash64;
use crate::rustc_index::{Idx, IndexVec};
use crate::case_study::USize;
use crate::{PartialOrdSpec, TryIntoSpec};

mod layout;

pub use layout::{LayoutCalculator, LayoutCalculatorError};

#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub struct ReprFlags(u8);

// Hand-written replacement for the `bitflags!` invocation in rustc_abi, since
// external crates are not available under ui_test.
impl ReprFlags {
    pub const IS_C: ReprFlags = ReprFlags(1 << 0);
    pub const IS_SIMD: ReprFlags = ReprFlags(1 << 1);
    pub const IS_TRANSPARENT: ReprFlags = ReprFlags(1 << 2);

    pub const IS_LINEAR: ReprFlags = ReprFlags(1 << 3);

    pub const RANDOMIZE_LAYOUT: ReprFlags = ReprFlags(1 << 4);

    pub const PASS_INDIRECTLY_IN_NON_RUSTIC_ABIS: ReprFlags = ReprFlags(1 << 5);
    pub const IS_SCALABLE: ReprFlags = ReprFlags(1 << 6);

    pub const FIELD_ORDER_UNOPTIMIZABLE: ReprFlags = ReprFlags(
        ReprFlags::IS_C.bits()
            | ReprFlags::IS_SIMD.bits()
            | ReprFlags::IS_SCALABLE.bits()
            | ReprFlags::IS_LINEAR.bits(),
    );
    pub const ABI_UNOPTIMIZABLE: ReprFlags =
        ReprFlags(ReprFlags::IS_C.bits() | ReprFlags::IS_SIMD.bits());

    pub const fn bits(&self) -> u8 {
        self.0
    }

    #[thrust::callable]
    pub const fn contains(&self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[thrust::callable]
    pub const fn intersects(&self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub enum IntegerType {
    Pointer(bool),

    Fixed(Integer, bool),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub enum ScalableElt {
    ElementCount(u16),

    Container,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Default)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub struct ReprOptions {
    pub int: Option<IntegerType>,
    pub align: Option<Align>,
    pub pack: Option<Align>,
    pub flags: ReprFlags,

    pub scalable: Option<ScalableElt>,

    pub field_shuffle_seed: Hash64,
}

// `derive(Default)` gives `ReprOptions` no `repr` alignment and no `pack`, which `layout()`'s
// `variant_fits_wf` and `univariant`'s `prefix_fits` read. Without a spec, a derived `default`
// is trusted on std.rs's `ensures(true)`; with this one, its body is analyzed against it where it
// is selected, and reads std.rs's `Option::default`.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.align == None && result.pack == None)]
fn _extern_spec_repr_options_default() -> ReprOptions {
    <ReprOptions as Default>::default()
}

impl ReprOptions {
    #[inline]
    #[thrust::callable]
    pub fn transparent(&self) -> bool {
        self.flags.contains(ReprFlags::IS_TRANSPARENT)
    }

    #[thrust::callable]
    pub fn inhibit_newtype_abi_optimization(&self) -> bool {
        self.flags.intersects(ReprFlags::ABI_UNOPTIMIZABLE)
    }

    #[thrust::callable]
    pub fn inhibit_struct_field_reordering(&self) -> bool {
        self.flags.intersects(ReprFlags::FIELD_ORDER_UNOPTIMIZABLE) || self.int.is_some()
    }

    #[thrust::callable]
    pub fn can_randomize_type_layout(&self) -> bool {
        !self.inhibit_struct_field_reordering() && self.flags.contains(ReprFlags::RANDOMIZE_LAYOUT)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct PointerSpec {
    pub(crate) pointer_size: Size,

    pub(crate) pointer_align: Align,

    pub(crate) pointer_offset: Size,

    pub(crate) _is_fat: bool,
}

#[derive(Debug, PartialEq, Eq)]
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

    pub(crate) address_space_info: Vec<(AddressSpace, PointerSpec)>,

    pub instruction_address_space: AddressSpace,

    pub c_enum_min_size: Integer,
}

// `address_space_info` is a `Vec` field of a struct whose model is the struct itself, so a
// formula reaches its entries through a sequence `s` equal to it (`Seq`'s `PartialEq` with a type
// whose model is that sequence). rustc's parser adds an address space to it at most once.

#[thrust_macros::context]
impl TargetDataLayout {
    // What `pointer_size_in` and `pointer_align_in` require of the address space `c`: it is the
    // default one or has an entry in `address_space_info`.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub(crate) fn pointer_space_ok(self, c: AddressSpace) -> bool {
        c == self.default_address_space
            || exists(|s: Seq<(AddressSpace, PointerSpec)>, i: Int|
                s == self.address_space_info && 0 <= i && i < s.len() && s[i].0 == c)
    }

    // `n` is the pointer size of the address space `c`: the default one's, or that of the first
    // entry of `address_space_info` for `c`.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub(crate) fn pointer_size_is(self, c: AddressSpace, n: Size) -> bool {
        (c == self.default_address_space && n == self.default_address_space_pointer_spec.pointer_size)
            || (!(c == self.default_address_space)
                && exists(|s: Seq<(AddressSpace, PointerSpec)>, i: Int|
                    s == self.address_space_info
                        && 0 <= i
                        && i < s.len()
                        && s[i].0 == c
                        && n == s[i].1.pointer_size
                        && forall(|j: Int| !(0 <= j && j < i) || !(s[j].0 == c))))
    }

    #[inline]
    #[thrust_macros::requires(((*self).default_address_space_pointer_spec.pointer_size.raw == 2
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 4
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 8))]
    #[thrust_macros::ensures(result >= 1)]
    #[thrust_macros::ensures(result == obj_bound(*self))]
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
    #[thrust_macros::requires(Self::pointer_space_ok(*self, c))]
    #[thrust_macros::ensures(Self::pointer_size_is(*self, c, result))]
    #[thrust::reveal(TargetDataLayout::pointer_space_ok, TargetDataLayout::pointer_size_is)]
    pub fn pointer_size_in(&self, c: AddressSpace) -> Size {
        if c == self.default_address_space {
            return self.default_address_space_pointer_spec.pointer_size;
        }

        // The closure's contract is written: inferred, its postcondition sits under the `forall` of
        // `find`'s contract over the rejected items (tests/ui/pass/closure_find_first_unannotated.rs).
        if let Some(e) = self.address_space_info.iter().find(thrust_macros::closure!(
            captures(c: &mut &AddressSpace),
            requires(true),
            ensures(result == ((**p).0 == **c)),
            |p: &&(AddressSpace, PointerSpec)| -> bool { p.0 == c },
        )) {
            e.1.pointer_size
        } else {
            panic!("Use of unknown address space {c:?}");
        }
    }

    #[inline]
    #[thrust_macros::requires(Self::pointer_space_ok(*self, c))]
    #[thrust_macros::ensures(true)]
    #[thrust::reveal(TargetDataLayout::pointer_space_ok)]
    pub fn pointer_align_in(&self, c: AddressSpace) -> AbiAlign {
        AbiAlign::new(if c == self.default_address_space {
            self.default_address_space_pointer_spec.pointer_align
        } else if let Some(e) = self.address_space_info.iter().find(thrust_macros::closure!(
            captures(c: &mut &AddressSpace),
            requires(true),
            ensures(result == ((**p).0 == **c)),
            |p: &&(AddressSpace, PointerSpec)| -> bool { p.0 == c },
        )) {
            e.1.pointer_align
        } else {
            panic!("Use of unknown address space {c:?}");
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
// typechecks for both impls, and each defines it as `self == dl` (the
// reference impl as `*self == dl`). Calling `dl_of` directly (as
// `data_layout`'s own `ensures` does) verifies.
//
// Relating a *generic* `cx: &C` to the layout `dl_of` names needs quantifying over it, as the
// `requires` of `Primitive::size` / `align` does; that verifies.
/// Rounding `x` up with the mask `m` of a power of two: unless `x + m` wraps, `(x + m) & !m`
/// lies in `[x, x + m]`.
#[thrust_macros::lemma]
#[thrust_macros::ensures((m + 1 == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(q) & BitVec::from_int(63))).to_int()
        && x + m <= u64::MAX)
    ==> (x <= (BitVec::<64, false>::from_int(x + m) & !BitVec::<64, false>::from_int(m)).to_int()
        && (BitVec::<64, false>::from_int(x + m) & !BitVec::<64, false>::from_int(m)).to_int() <= x + m))]
fn round_up(x: u64, m: u64, q: u64) {}

/// `obj_size_bound` of a layout whose default pointer has 2, 4 or 8 bytes.
#[thrust_macros::logic]
pub(crate) fn obj_bound(dl: TargetDataLayout) -> u64 {
    if dl.default_address_space_pointer_spec.pointer_size.raw == 2 {
        32768
    } else if dl.default_address_space_pointer_spec.pointer_size.raw == 4 {
        2147483648
    } else {
        2305843009213693952
    }
}

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
        self == dl
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
        *self == dl
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

impl Endian {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Little => "little",
            Self::Big => "big",
        }
    }
}

impl fmt::Debug for Endian {
    #[thrust::ignored]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub struct Size {
    pub(crate) raw: u64,
}

impl fmt::Debug for Size {
    #[thrust::ignored]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Size({} bytes)", self.bytes())
    }
}

#[thrust_macros::context]
impl Size {
    pub const ZERO: Size = Size { raw: 0 };

    // Here and in `from_bytes`, the `impl TryInto<u64>` parameter is a named `T: TryIntoSpec<u64>`:
    // `TryInto` says nothing about the converted value, and a formula cannot name the type of an
    // `impl Trait` parameter to call `TryIntoSpec`'s predicates on.
    pub fn from_bits<T: TryIntoSpec<u64>>(bits: T) -> Size {
        let bits = bits.try_into().ok().unwrap();
        Size {
            raw: bits.div_ceil(8),
        }
    }

    #[inline]
    #[thrust_macros::requires(T::fits(bytes))]
    #[thrust_macros::ensures(thrust_models::exists(|b| T::converts_to(bytes, b) && result.raw == b))]
    pub fn from_bytes<T: TryIntoSpec<u64>>(bytes: T) -> Size {
        let bytes: u64 = bytes.try_into().ok().unwrap();
        Size { raw: bytes }
    }

    #[inline]
    pub fn bytes(self) -> u64 {
        self.raw
    }

    // The body panics exactly when `raw * 8` overflows `u64`, which the `requires` excludes.
    #[inline]
    #[thrust_macros::requires(self.raw * 8 <= u64::MAX)]
    #[thrust_macros::ensures(result == self.raw * 8)]
    pub fn bits(self) -> u64 {
        #[cold]
        #[thrust_macros::requires(false)]
        fn overflow(bytes: u64) -> ! {
            panic!("Size::bits: {bytes} bytes in bits doesn't fit in u64")
        }

        self.bytes()
            .checked_mul(8)
            .unwrap_or_else(|| overflow(self.bytes()))
    }

    /// The least multiple of the alignment at or above `self`, when `self` plus its mask does not
    /// wrap: `b` is the alignment's bytes as `Align::bytes` gives them.
    #[inline]
    #[thrust_macros::ensures(forall(|b: USize| b == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(align.pow2) & BitVec::from_int(63))).to_int()
        && self.raw + b - 1 <= u64::MAX
        ==> (self.raw <= result.raw && result.raw < self.raw + b)))]
    pub fn align_to(self, align: Align) -> Size {
        let mask = align.bytes() - 1;
        thrust_macros::proof!(round_up(self.bytes(), mask, align.pow2 as u64));
        Size::from_bytes((self.bytes() + mask) & !mask)
    }

    #[inline]
    // The `requires` is that of `obj_size_bound` for the layout `cx` names.
    #[thrust_macros::requires(forall(|dl: TargetDataLayout| C::dl_of(*cx, dl) ==> dl.default_address_space_pointer_spec.pointer_size.raw == 2
        || dl.default_address_space_pointer_spec.pointer_size.raw == 4
        || dl.default_address_space_pointer_spec.pointer_size.raw == 8))]
    // The sum when it is below the object size bound of the layout `cx` names. A generic `C` may
    // name several layouts, so the bound is stated of one of them: the one `data_layout` returns.
    #[thrust_macros::ensures(forall(|z: Size| result == Some(z)
        ==> (z.raw == self.raw + offset.raw
            && exists(|dl: TargetDataLayout| C::dl_of(*cx, dl) && z.raw < obj_bound(dl)))))]
    #[thrust_macros::ensures(result == None
        ==> exists(|dl: TargetDataLayout| C::dl_of(*cx, dl) && self.raw + offset.raw >= obj_bound(dl)))]
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
    pub fn unsigned_int_max(&self) -> u128 {
        u128::MAX >> (128 - self.bits())
    }
}

#[thrust_macros::context]
impl Add for Size {
    type Output = Size;
    #[inline]
    #[thrust_macros::requires(self.raw + other.raw <= u64::MAX)]
    #[thrust_macros::ensures(result.raw == self.raw + other.raw)]
    fn add(self, other: Size) -> Size {
        Size::from_bytes(self.bytes().checked_add(other.bytes()).unwrap_or_else(|| {
            panic!("Size::add: {} + {} doesn't fit in u64", self.bytes(), other.bytes())
        }))
    }
}

#[thrust_macros::context]
impl AddAssign for Size {
    #[inline]
    #[thrust_macros::requires((*self).raw + other.raw <= u64::MAX)]
    #[thrust_macros::ensures((!self).raw == (*self).raw + other.raw)]
    fn add_assign(&mut self, other: Size) {
        *self = *self + other;
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub struct Align {
    pub(crate) pow2: u8,
}

impl fmt::Debug for Align {
    #[thrust::ignored]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Align({} bytes)", self.bytes())
    }
}

#[thrust_macros::context]
impl Align {
    pub const ONE: Align = Align { pow2: 0 };
    pub const EIGHT: Align = Align { pow2: 3 };

    pub const MAX: Align = Align { pow2: 29 };

    // `1 << pow2`, the shift amount masked to the width; layout.rs's `shl_is_pow2` makes it
    // `2^pow2` below 64.
    #[inline]
    #[thrust_macros::ensures(result >= 1)]
    #[thrust_macros::ensures(result
        == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(self.pow2) & BitVec::from_int(63))).to_int())]
    pub const fn bytes(self) -> u64 {
        1 << self.pow2
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub struct AbiAlign {
    pub abi: Align,
}

#[thrust_macros::context]
impl AbiAlign {
    #[inline]
    #[thrust_macros::ensures(result.abi == align)]
    pub fn new(align: Align) -> AbiAlign {
        AbiAlign { abi: align }
    }

    #[inline]
    #[thrust_macros::ensures(result.abi.pow2 <= self.abi.pow2 && result.abi.pow2 <= other.abi.pow2)]
    pub fn min(self, other: AbiAlign) -> AbiAlign {
        AbiAlign {
            abi: self.abi.min(other.abi),
        }
    }

    #[inline]
    pub fn max(self, other: AbiAlign) -> AbiAlign {
        AbiAlign {
            abi: self.abi.max(other.abi),
        }
    }
}

impl Deref for AbiAlign {
    type Target = Align;

    fn deref(&self) -> &Self::Target {
        &self.abi
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
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
    /// `n` is the size of `self`, in bytes.
    #[thrust_macros::predicate]
    pub(crate) fn bytes_are(self, n: Size) -> bool {
        (self == Integer::I8 && n.raw == 1)
            || (self == Integer::I16 && n.raw == 2)
            || (self == Integer::I32 && n.raw == 4)
            || (self == Integer::I64 && n.raw == 8)
            || (self == Integer::I128 && n.raw == 16)
    }

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

    #[inline]
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

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub enum Float {
    F16,
    F32,
    F64,
    F128,
}

#[thrust_macros::context]
impl Float {
    /// `n` is the size of `self`, in bytes.
    #[thrust_macros::predicate]
    pub(crate) fn bytes_are(self, n: Size) -> bool {
        (self == Float::F16 && n.raw == 2)
            || (self == Float::F32 && n.raw == 4)
            || (self == Float::F64 && n.raw == 8)
            || (self == Float::F128 && n.raw == 16)
    }

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

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub enum Primitive {
    Int(Integer, bool),
    Float(Float),
    Pointer(AddressSpace),
}

/// Among the first `k` entries of `address_space_info`, `c` has none or a first one.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(forall(|s: Seq<(AddressSpace, PointerSpec)>| (s == (*dl).address_space_info && k <= s.len())
    ==> (forall(|i: Int| (0 <= i && i < k) ==> !(s[i].0 == c))
        || exists(|i: Int| 0 <= i && i < k && s[i].0 == c
            && forall(|j: Int| (0 <= j && j < i) ==> !(s[j].0 == c))))))]
fn first_entry(dl: &TargetDataLayout, c: AddressSpace, k: usize) {
    if k > 0 {
        first_entry(dl, c, k - 1);
    }
}

/// Every primitive has a size under a layout that has an entry for its address space: an
/// integer and a float by their kind, a pointer by the first entry for its address space. `n` is
/// the number of entries of `address_space_info`.
#[thrust_macros::lemma]
#[thrust_macros::requires(forall(|a: AddressSpace| p == Primitive::Pointer(a)
    ==> TargetDataLayout::pointer_space_ok(*dl, a)))]
#[thrust_macros::requires(forall(|s: Seq<(AddressSpace, PointerSpec)>| s == (*dl).address_space_info ==> s.len() == n))]
#[thrust_macros::ensures(exists(|s: Size| Primitive::size_in(p, *dl, s)))]
#[thrust::reveal(
    Primitive::size_in,
    TargetDataLayout::pointer_space_ok,
    TargetDataLayout::pointer_size_is
)]
pub(crate) fn size_in_total(p: Primitive, dl: &TargetDataLayout, n: usize) {
    if let Primitive::Pointer(a) = p {
        first_entry(dl, a, n);
    }
}

#[thrust_macros::context]
impl Primitive {
    /// `s` is the size of `self` under the data layout `dl`.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub(crate) fn size_in(self, dl: TargetDataLayout, s: Size) -> bool {
        exists(|i: Integer, b: bool| self == Primitive::Int(i, b) && Integer::bytes_are(i, s))
            || exists(|f: Float| self == Primitive::Float(f) && Float::bytes_are(f, s))
            || exists(|a: AddressSpace| self == Primitive::Pointer(a)
                && TargetDataLayout::pointer_size_is(dl, a, s))
    }

    // A pointer's size and alignment are looked up in the layout `cx` names: the `requires` of
    // `pointer_size_in` / `pointer_align_in` must hold for every layout `dl` with `dl_of(*cx, dl)`.
    #[thrust_macros::requires(forall(|dl: TargetDataLayout, a: AddressSpace|
        C::dl_of(*cx, dl) && self == Primitive::Pointer(a) ==> TargetDataLayout::pointer_space_ok(dl, a)))]
    // An integer or a float has at most 16 bytes; a pointer has the size the layout `cx` names.
    #[thrust_macros::ensures(result.raw <= 16
        || exists(|dl: TargetDataLayout, a: AddressSpace| C::dl_of(*cx, dl)
            && self == Primitive::Pointer(a) && TargetDataLayout::pointer_size_is(dl, a, result)))]
    #[thrust_macros::ensures(exists(|dl: TargetDataLayout| C::dl_of(*cx, dl) && Self::size_in(self, dl, result)))]
    #[thrust::reveal(Primitive::size_in)]
    pub fn size<C: HasDataLayout>(self, cx: &C) -> Size {
        use Primitive::*;
        let dl = cx.data_layout();

        match self {
            Int(i, _) => i.size(),
            Float(f) => f.size(),
            Pointer(a) => dl.pointer_size_in(a),
        }
    }

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

impl fmt::Debug for WrappingRange {
    #[thrust::ignored]
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.start > self.end {
            write!(fmt, "(..={}) | ({}..)", self.end, self.start)?;
        } else {
            write!(fmt, "{}..={}", self.start, self.end)?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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

    // `scalar_wf`: what `size`, `align` and `Niche::from_scalar` require of the scalar under the
    // data layout `dl`, as `Niche::wf_in` of a niche. `from_scalar` asserts the 128-bit bound for
    // an `Initialized` scalar only; for a `Union` (the pointer scalars of `MaybeUninit` locals) it
    // is the invariant that rustc makes pointer scalars only in the default and the instruction
    // address space, which the data layout parser always lists and whose sizes are those of real
    // targets. The bound keeps `scalar_pair`'s `b_offset + b.size(dl)` from overflowing.
    #[thrust_macros::predicate]
    pub(crate) fn wf_in(self, dl: TargetDataLayout) -> bool {
        forall(|p: Primitive, r: WrappingRange, a: AddressSpace|
            !((self == Scalar::Initialized { value: p, valid_range: r } || self == Scalar::Union { value: p })
                && p == Primitive::Pointer(a))
                || (TargetDataLayout::pointer_space_ok(dl, a)
                    && forall(|n: Size| !TargetDataLayout::pointer_size_is(dl, a, n) || n.raw * 8 <= 128)))
    }

    #[thrust_macros::impl_trait_names(C)]
    pub fn align(self, cx: &impl HasDataLayout) -> AbiAlign {
        self.primitive().align(cx)
    }

    #[thrust_macros::impl_trait_names(C)]
    #[thrust_macros::requires(forall(|dl: TargetDataLayout, p: Primitive, r: WrappingRange, a: AddressSpace|
        C::dl_of(*cx, dl)
            && (self == Scalar::Initialized { value: p, valid_range: r } || self == Scalar::Union { value: p })
            && p == Primitive::Pointer(a) ==> TargetDataLayout::pointer_space_ok(dl, a)))]
    // `Primitive::size`'s bound: an integer or a float has at most 16 bytes, a pointer the size the
    // layout `cx` names.
    #[thrust_macros::ensures(result.raw <= 16
        || exists(|dl: TargetDataLayout, p: Primitive, r: WrappingRange, a: AddressSpace| C::dl_of(*cx, dl)
            && (self == Scalar::Initialized { value: p, valid_range: r } || self == Scalar::Union { value: p })
            && p == Primitive::Pointer(a)
            && TargetDataLayout::pointer_size_is(dl, a, result)))]
    pub fn size(self, cx: &impl HasDataLayout) -> Size {
        self.primitive().size(cx)
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum FieldsShape<FieldIdx: Idx> {
    Primitive,

    Union(NonZeroUsize),

    Array {
        stride: Size,
        count: u64,
    },

    Arbitrary {
        offsets: IndexVec<FieldIdx, Size>,

        in_memory_order: IndexVec<u32, FieldIdx>,
    },
}

// `offsets` and `in_memory_order` are `IndexVec`s, whose model is a sequence, inside a
// `Model = Self` enum, so a formula reaches the sequences through `Seq`'s `PartialEq` with a
// type whose model it is.
#[thrust_macros::context]
impl<FieldIdx: Idx + thrust_models::Model> FieldsShape<FieldIdx> {
    /// `self` is `Arbitrary` over `n` fields: `n` offsets, and a memory order listing each
    /// field below `n` exactly once.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    fn arbitrary_of(self, n: USize) -> bool {
        exists(|o: IndexVec<FieldIdx, Size>, m: IndexVec<u32, FieldIdx>,
                os: Seq<Size>, ms: Seq<<FieldIdx as thrust_models::Model>::Ty>|
            self == FieldsShape::Arbitrary { offsets: o, in_memory_order: m }
                && os == o
                && ms == m
                && os.len() == n
                && ms.len() == n
                && forall(|k: USize, i: USize|
                    !(0 <= k && k < n && <FieldIdx as Idx>::index_is(ms[k], i)) || (0 <= i && i < n))
                && forall(|k: USize, k2: USize, i: USize|
                    !(0 <= k && k < n && 0 <= k2 && k2 < n && !(k == k2)
                        && <FieldIdx as Idx>::index_is(ms[k], i))
                        || !<FieldIdx as Idx>::index_is(ms[k2], i)))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub struct AddressSpace(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct NumScalableVectors(pub u8);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BackendRepr {
    Scalar(Scalar),
    ScalarPair(Scalar, Scalar),
    SimdScalableVector {
        element: Scalar,
        count: u64,
        number_of_vectors: NumScalableVectors,
    },
    SimdVector {
        element: Scalar,
        count: u64,
    },

    Memory {
        sized: bool,
    },
}

#[thrust_macros::context]
impl BackendRepr {
    // The contract states the body, so that a caller reads it rather than inferring it.
    #[inline]
    #[thrust_macros::ensures(result == (*self == BackendRepr::Memory { sized: false }))]
    pub fn is_unsized(&self) -> bool {
        match *self {
            BackendRepr::Scalar(_)
            | BackendRepr::ScalarPair(..)
            | BackendRepr::SimdScalableVector { .. }
            | BackendRepr::SimdVector { .. } => false,
            BackendRepr::Memory { sized } => !sized,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Variants<FieldIdx: Idx, VariantIdx: Idx> {
    Empty,

    Single {
        index: VariantIdx,
    },

    Multiple {
        tag: Scalar,
        tag_encoding: TagEncoding<VariantIdx>,
        tag_field: FieldIdx,
        variants: IndexVec<VariantIdx, VariantLayout<FieldIdx>>,
    },
}

#[derive(PartialEq, Eq, Hash, Copy, Clone, Debug)]
pub enum TagEncoding<VariantIdx: Idx> {
    Direct,

    Niche {
        untagged_variant: VariantIdx,

        niche_variants: RangeInclusive<VariantIdx>,

        niche_start: u128,
    },
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub struct Niche {
    pub offset: Size,
    pub value: Primitive,
    pub valid_range: WrappingRange,
}

#[thrust_macros::context]
impl Niche {
    // `niche_wf`: what `available` requires of the niche under the data layout `dl`.
    #[thrust_macros::predicate]
    fn wf_in(self, dl: TargetDataLayout) -> bool {
        forall(|a: AddressSpace| !(self.value == Primitive::Pointer(a))
            || (TargetDataLayout::pointer_space_ok(dl, a)
                && forall(|n: Size| !TargetDataLayout::pointer_size_is(dl, a, n) || n.raw * 8 <= 128)))
    }

    #[thrust_macros::requires(forall(|dl: TargetDataLayout, r: WrappingRange, a: AddressSpace|
        C::dl_of(*cx, dl) && scalar == Scalar::Initialized { value: Primitive::Pointer(a), valid_range: r } ==> (TargetDataLayout::pointer_space_ok(dl, a)
                && forall(|n: Size| TargetDataLayout::pointer_size_is(dl, a, n) ==> n.raw * 8 <= 128))))]
    #[thrust_macros::ensures(forall(|n: Niche| result != Some(n)
        || (scalar == Scalar::Initialized { value: n.value, valid_range: n.valid_range } && n.offset == offset)))]
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

    // The `requires` is that of `value.size(cx)` and the `assert!`'s bound on a pointer's size.
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

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct LayoutData<FieldIdx: Idx, VariantIdx: Idx> {
    pub fields: FieldsShape<FieldIdx>,

    pub variants: Variants<FieldIdx, VariantIdx>,

    pub backend_repr: BackendRepr,

    pub largest_niche: Option<Niche>,

    pub uninhabited: bool,

    pub align: AbiAlign,
    pub size: Size,

    pub max_repr_align: Option<Align>,

    pub unadjusted_abi_align: Align,

    pub randomization_seed: Hash64,
}

impl<FieldIdx: Idx, VariantIdx: Idx> LayoutData<FieldIdx, VariantIdx> {
    pub fn is_uninhabited(&self) -> bool {
        self.uninhabited
    }
}

#[thrust_macros::context]
impl<FieldIdx: Idx, VariantIdx: Idx> LayoutData<FieldIdx, VariantIdx> {
    // The contract states the body, as `BackendRepr::is_unsized`'s does.
    #[inline]
    #[thrust_macros::ensures(result == ((*self).backend_repr == BackendRepr::Memory { sized: false }))]
    pub fn is_unsized(&self) -> bool {
        self.backend_repr.is_unsized()
    }

    pub fn is_zst(&self) -> bool {
        match self.backend_repr {
            BackendRepr::Scalar(_)
            | BackendRepr::ScalarPair(..)
            | BackendRepr::SimdScalableVector { .. }
            | BackendRepr::SimdVector { .. } => false,
            BackendRepr::Memory { sized } => sized && self.size.bytes() == 0,
        }
    }
}

// `PartialEq` is not rustc's: `univariant`'s contract compares the kind (rewrites.md S1).
#[derive(Copy, Clone, PartialEq, Debug)]
pub enum StructKind {
    AlwaysSized,

    MaybeUnsized,

    Prefixed(Size, Align),
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct VariantLayout<FieldIdx: Idx> {
    pub size: Size,
    pub backend_repr: BackendRepr,
    pub field_offsets: IndexVec<FieldIdx, Size>,
    fields_in_memory_order: IndexVec<u32, FieldIdx>,
    largest_niche: Option<Niche>,
    uninhabited: bool,
}

#[thrust_macros::context]
impl<FieldIdx: Idx> VariantLayout<FieldIdx> {
    pub fn from_layout(layout: LayoutData<FieldIdx, impl Idx>) -> Self {
        let FieldsShape::Arbitrary {
            offsets,
            in_memory_order,
        } = layout.fields
        else {
            panic!("Layout of fields should be Arbitrary for variants");
        };

        Self {
            size: layout.size,
            backend_repr: layout.backend_repr,
            field_offsets: offsets,
            fields_in_memory_order: in_memory_order,
            largest_niche: layout.largest_niche,
            uninhabited: layout.uninhabited,
        }
    }

    pub fn is_uninhabited(&self) -> bool {
        self.uninhabited
    }
}

// The derived `PartialOrd` and `Ord` of `Size` and `Align` compare the single field, so `max` and
// `min` are specified through the field's order, as std.rs does for the integers. `Size`
// compares `raw: u64`, `Align` compares `pow2: u8`.
#[thrust_macros::context]
impl PartialOrdSpec for Size {
    #[thrust_macros::predicate]
    fn compares(self, other: Self, ord: Option<std::cmp::Ordering>) -> bool {
        (self.raw < other.raw && ord == Some(std::cmp::Ordering::Less))
            || (self.raw == other.raw && ord == Some(std::cmp::Ordering::Equal))
            || (self.raw > other.raw && ord == Some(std::cmp::Ordering::Greater))
    }

    fn compares_functional(
        a: &Self,
        b: &Self,
        x: Option<std::cmp::Ordering>,
        y: Option<std::cmp::Ordering>,
    ) {
    }
}

#[thrust_macros::context]
impl PartialOrdSpec for Align {
    #[thrust_macros::predicate]
    fn compares(self, other: Self, ord: Option<std::cmp::Ordering>) -> bool {
        (self.pow2 < other.pow2 && ord == Some(std::cmp::Ordering::Less))
            || (self.pow2 == other.pow2 && ord == Some(std::cmp::Ordering::Equal))
            || (self.pow2 > other.pow2 && ord == Some(std::cmp::Ordering::Greater))
    }

    fn compares_functional(
        a: &Self,
        b: &Self,
        x: Option<std::cmp::Ordering>,
        y: Option<std::cmp::Ordering>,
    ) {
    }
}
