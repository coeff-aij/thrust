//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An extern spec of a derived `Default::default` is checked against the derived body, which
// builds each `Option` field by `Option`'s `default`, `None`.

#[derive(Clone, Copy, PartialEq, Default)]
struct Repr {
    align: Option<u32>,
    pack: Option<u32>,
}

impl thrust_models::Model for Repr {
    type Ty = Self;
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.align == None && result.pack == None)]
fn _extern_spec_repr_default() -> Repr {
    <Repr as Default>::default()
}

fn main() {
    let r = Repr::default();
    assert!(r.align.is_none());
}
