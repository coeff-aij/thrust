#[derive(Copy, Clone, PartialEq, Eq)] pub struct Size { raw: u64 }
#[derive(Copy, Clone, PartialEq, Eq)] pub struct Align { pow2: u8 }
#[derive(Copy, Clone, PartialEq, Eq)] pub struct AddressSpace(pub u32);
#[derive(Copy, Clone, PartialEq, Eq)] pub enum Endian { Little, Big }
#[derive(Copy, Clone, PartialEq, Eq)] pub enum Integer { I8, I16, I32, I64, I128 }
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct PointerSpec { pointer_size: Size, pointer_align: Align, pointer_offset: Size, _is_fat: bool }
#[derive(PartialEq, Eq)]
pub struct L {
    pub endian: Endian,
    pub a0: Align,
    pub a1: Align,
    pub a2: Align,
    pub a3: Align,
    pub a4: Align,
    pub a5: Align,
    pub a6: Align,
    pub a7: Align,
    pub a8: Align,
    pub a9: Align,
    pub a10: Align,
    pub vector_align: Vec<(Size, Align)>,
    pub das: AddressSpace,
    pub dasps: PointerSpec,
    address_space_info: Vec<(AddressSpace, PointerSpec)>,
    pub ias: AddressSpace,
    pub c: Integer,
}
fn main() {
    let s = L { endian: Endian::Little, a0: Align { pow2: 0 }, a1: Align { pow2: 0 }, a2: Align { pow2: 0 }, a3: Align { pow2: 0 }, a4: Align { pow2: 0 }, a5: Align { pow2: 0 }, a6: Align { pow2: 0 }, a7: Align { pow2: 0 }, a8: Align { pow2: 0 }, a9: Align { pow2: 0 }, a10: Align { pow2: 0 }, vector_align: Vec::new(), das: AddressSpace(0), dasps: PointerSpec { pointer_size: Size { raw: 8 }, pointer_align: Align { pow2: 3 }, pointer_offset: Size { raw: 0 }, _is_fat: false }, address_space_info: Vec::new(), ias: AddressSpace(0), c: Integer::I8 };
    let t = L { endian: Endian::Little, a0: Align { pow2: 0 }, a1: Align { pow2: 0 }, a2: Align { pow2: 0 }, a3: Align { pow2: 0 }, a4: Align { pow2: 0 }, a5: Align { pow2: 0 }, a6: Align { pow2: 0 }, a7: Align { pow2: 0 }, a8: Align { pow2: 0 }, a9: Align { pow2: 0 }, a10: Align { pow2: 0 }, vector_align: Vec::new(), das: AddressSpace(0), dasps: PointerSpec { pointer_size: Size { raw: 8 }, pointer_align: Align { pow2: 3 }, pointer_offset: Size { raw: 0 }, _is_fat: false }, address_space_info: Vec::new(), ias: AddressSpace(0), c: Integer::I8 };
    assert!(s == t);
}
