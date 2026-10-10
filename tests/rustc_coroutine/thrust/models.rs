//! The `Model` of each rustc type, as the stage files declared it. Every type modeled by itself is
//! read field by field; the others name the model a contract reads.

use crate::thrust_models;
use thrust_models::model::Seq;

use crate::rustc_abi::*;
use crate::rustc_hashes::Hash64;
use crate::rustc_index::bit_set::{BitIter, BitMatrix, DenseBitSet, WordIter};
use crate::rustc_index::{Idx, IdxRange, IndexSlice, IndexVec, IterEnumerated, SliceIter};
use crate::case_study::USize;

impl thrust_models::Model for Hash64 {
    type Ty = Self;
}

// `(domain_size, words, marker, card)`.
impl<T> thrust_models::Model for DenseBitSet<T> {
    type Ty = (USize, Seq<USize>, (), USize);
}
// `(words, pos)`.
impl<'a> thrust_models::Model for WordIter<'a> {
    type Ty = (&'a Seq<USize>, USize);
}
// `(word, offset, iter, marker)`.
impl<'a, T: Idx> thrust_models::Model for BitIter<'a, T> {
    type Ty = (USize, USize, <WordIter<'a> as thrust_models::Model>::Ty, ());
}
impl<R: Idx, C: Idx> thrust_models::Model for BitMatrix<R, C> {
    type Ty = Self;
}
impl<I: Idx> thrust_models::Model for IdxRange<I> {
    type Ty = Self;
}
// The `(raw, pos)` shape of the structs, as `WordIter`'s and `core::slice::Iter`'s in std.rs;
// `IterEnumerated` adds the unit of its `PhantomData`.
impl<'a, T: thrust_models::Model> thrust_models::Model for SliceIter<'a, T> {
    type Ty = (&'a Seq<<T as thrust_models::Model>::Ty>, USize);
}
impl<'a, I: Idx, T: thrust_models::Model> thrust_models::Model for IterEnumerated<'a, I, T> {
    type Ty = (&'a Seq<<T as thrust_models::Model>::Ty>, USize, ());
}
// `IndexVec` takes the model of the `Vec` it wraps.
impl<I: Idx, T: thrust_models::Model> thrust_models::Model for IndexVec<I, T> {
    type Ty = <Vec<T> as thrust_models::Model>::Ty;
}
// `IndexSlice<I, T>` cannot get `type Ty = Self`: its `raw: [T]` field makes it unsized, and
// `Model::Ty` carries an implicit `Sized` bound. It takes the model of its slice, as `IndexVec`
// takes its vector's, dropping the phantom `I` marker.
impl<I: Idx, T: thrust_models::Model> thrust_models::Model for IndexSlice<I, T> {
    type Ty = <[T] as thrust_models::Model>::Ty;
}

impl<F: thrust_models::Model> thrust_models::Model for LayoutCalculatorError<F> {
    type Ty = LayoutCalculatorError<<F as thrust_models::Model>::Ty>;
}
// The calculator's model is its one field's, so that a contract names `self.cx`'s data layout
// through `Cx::dl_of(*self, dl)` (probes/calculator_dl.rs).
impl<Cx: thrust_models::Model> thrust_models::Model for LayoutCalculator<Cx> {
    type Ty = <Cx as thrust_models::Model>::Ty;
}
impl thrust_models::Model for ReprFlags {
    type Ty = Self;
}
impl thrust_models::Model for IntegerType {
    type Ty = Self;
}
impl thrust_models::Model for ScalableElt {
    type Ty = Self;
}
impl thrust_models::Model for ReprOptions {
    type Ty = Self;
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
impl<FieldIdx: Idx> thrust_models::Model for FieldsShape<FieldIdx> {
    type Ty = Self;
}
impl thrust_models::Model for AddressSpace {
    type Ty = Self;
}
impl thrust_models::Model for NumScalableVectors {
    type Ty = Self;
}
impl thrust_models::Model for BackendRepr {
    type Ty = Self;
}
impl<FieldIdx: Idx, VariantIdx: Idx> thrust_models::Model for Variants<FieldIdx, VariantIdx> {
    type Ty = Self;
}
impl<VariantIdx: Idx> thrust_models::Model for TagEncoding<VariantIdx> {
    type Ty = Self;
}
impl thrust_models::Model for Niche {
    type Ty = Self;
}
impl<FieldIdx: Idx, VariantIdx: Idx> thrust_models::Model for LayoutData<FieldIdx, VariantIdx> {
    type Ty = Self;
}
impl thrust_models::Model for StructKind {
    type Ty = Self;
}
impl<FieldIdx: Idx> thrust_models::Model for VariantLayout<FieldIdx> {
    type Ty = Self;
}
