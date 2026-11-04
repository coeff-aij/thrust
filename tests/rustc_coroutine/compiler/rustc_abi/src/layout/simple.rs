use crate::thrust_models;
use thrust_models::model::Seq;
use thrust_models::{exists, forall};

use crate::rustc_hashes::Hash64;
use crate::rustc_index::{Idx, IndexVec};
use crate::case_study::USize;
use crate::rustc_abi::{
    AbiAlign, BackendRepr, FieldsShape, HasDataLayout, LayoutData, Niche, Scalar, Size,
    TargetDataLayout, Variants,
};

#[thrust_macros::context]
impl<FieldIdx: Idx, VariantIdx: Idx> LayoutData<FieldIdx, VariantIdx> {
    // Trusted: `chain`'s specification is a draft. The `requires` is the body's panic condition.
    // `size` and `align` of a pointer scalar look its address space up, and `Niche::from_scalar`
    // asserts that its size is at most 128 bits (`Scalar::wf_in`); with both sizes at most 16
    // bytes, `b_offset` is at most 2^63 and `b_offset + b.size(dl)` does not overflow. `new` builds
    // the indices 0 of `VariantIdx` and 0 and 1 of `FieldIdx`. The `ensures` is what
    // `univariant_biased` reads of the pair's fields: `Arbitrary`, two offsets, the first 0, and
    // the memory order 0, 1.
    #[thrust::trusted]
    #[thrust_macros::requires(forall(|dl: TargetDataLayout| C::dl_of(*cx, dl) ==> (Scalar::wf_in(a, dl) && Scalar::wf_in(b, dl))))]
    #[thrust_macros::requires(forall(|z: USize| z == 0usize ==> <VariantIdx as Idx>::can_new(z)))]
    #[thrust_macros::requires(forall(|k: USize| k == 0usize || k == 1usize ==> <FieldIdx as Idx>::can_new(k)))]
    #[thrust_macros::ensures(exists(|o: IndexVec<FieldIdx, Size>, m: IndexVec<u32, FieldIdx>,
            os: Seq<Size>, ms: Seq<<FieldIdx as thrust_models::Model>::Ty>, i0: USize, i1: USize|
        result.fields == FieldsShape::Arbitrary { offsets: o, in_memory_order: m }
            && os == o
            && ms == m
            && os.len() == 2
            && ms.len() == 2
            && os[0].raw == 0
            && i0 == 0usize
            && i1 == 1usize
            && <FieldIdx as Idx>::index_is(ms[0], i0)
            && <FieldIdx as Idx>::index_is(ms[1], i1)))]
    pub fn scalar_pair<C: HasDataLayout>(cx: &C, a: Scalar, b: Scalar) -> Self {
        let dl = cx.data_layout();
        let b_align = b.align(dl).abi;
        let align = a.align(dl).abi.max(b_align).max(dl.aggregate_align);
        let b_offset = a.size(dl).align_to(b_align);
        let size = (b_offset + b.size(dl)).align_to(align);

        let largest_niche = Niche::from_scalar(dl, b_offset, b)
            .into_iter()
            .chain(Niche::from_scalar(dl, Size::ZERO, a))
            .max_by_key(|niche| niche.available(dl));

        let combined_seed = a.size(dl).bytes().wrapping_add(b.size(dl).bytes());

        LayoutData {
            variants: Variants::Single {
                index: VariantIdx::new(0),
            },
            fields: FieldsShape::Arbitrary {
                offsets: [Size::ZERO, b_offset].into(),
                in_memory_order: [FieldIdx::new(0), FieldIdx::new(1)].into(),
            },
            backend_repr: BackendRepr::ScalarPair(a, b),
            largest_niche,
            uninhabited: false,
            align: AbiAlign::new(align),
            size,
            max_repr_align: None,
            unadjusted_abi_align: align,
            randomization_seed: Hash64::new(combined_seed),
        }
    }
}
