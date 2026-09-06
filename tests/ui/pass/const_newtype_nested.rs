//@check-pass
//@compile-flags: -C debug-assertions=off

#[derive(Clone, Copy)]
pub struct Align {
    pow2: u32,
}

impl Align {
    pub const EIGHT: Align = Align { pow2: 3 };
}

#[derive(Clone, Copy)]
pub struct AbiAlign {
    abi: Align,
}

impl AbiAlign {
    pub const X: AbiAlign = AbiAlign { abi: Align::EIGHT };
}

impl thrust_models::Model for Align {
    type Ty = Self;
}

impl thrust_models::Model for AbiAlign {
    type Ty = Self;
}

fn main() {
    assert!(AbiAlign::X.abi.pow2 == 3);
}
