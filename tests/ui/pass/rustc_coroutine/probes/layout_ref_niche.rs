//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:bd27e3fc4 THRUST_TRY_SPECS=1

// layout.rs's `layout()` and `univariant` reduced to how a contract names the layout an `F`
// dereferences to: `LayoutRef::layout_is(f, l)`, a predicate of a bound with `Deref` as its
// supertrait. `univariant` requires a property of every field's layout; `layout()` gets it for
// a given layout from its own `requires` and for `tag_to_layout`'s result from the closure's
// postcondition.

use std::ops::Deref;
use thrust_models::forall;

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct LayoutData {
    pub niche: i64,
}

impl thrust_models::Model for LayoutData {
    type Ty = Self;
}

#[thrust_macros::context]
pub trait LayoutRef<'a>: Deref<Target = &'a LayoutData> + Copy + thrust_models::Model {
    #[thrust_macros::predicate]
    fn layout_is(self, l: LayoutData) -> bool;
}

#[thrust::trusted]
#[thrust_macros::requires(forall(|i: usize, l: LayoutData|
    !(0 <= i && i < (*fields).len() && F::layout_is((*fields)[i], l)) || l.niche >= 0))]
#[thrust_macros::ensures(true)]
fn univariant<'a, F: LayoutRef<'a>>(fields: &Vec<F>) -> i64 {
    unimplemented!()
}

#[thrust_macros::requires(forall(|l: LayoutData| !F::layout_is(local, l) || l.niche >= 0))]
#[thrust_macros::requires(forall(|s: i64| thrust_macros::pre!(tag_to_layout(s))))]
#[thrust_macros::requires(forall(|s: i64, r: <F as thrust_models::Model>::Ty|
    !thrust_macros::post!(tag_to_layout(s), r)
        || forall(|l: LayoutData| !F::layout_is(r, l) || l.niche >= 0)))]
#[thrust_macros::ensures(true)]
fn layout<'a, F: LayoutRef<'a>, T: Fn(i64) -> F>(local: F, tag_to_layout: T) -> i64 {
    let mut fields = Vec::new();
    fields.push(local);
    fields.push(tag_to_layout(0));
    univariant(&fields)
}

fn main() {}
