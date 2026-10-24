//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1

// layout.rs's `layout()` and `univariant` reduced to how a contract names the layout an `F`
// dereferences to: `post!(<F as Deref>::deref(&f), d)`, the postcondition of `Deref::deref` at the
// type parameter. `univariant` requires a property of every field's layout; `layout()` gets it
// for a given layout from its own `requires` and for `tag_to_layout`'s result from the closure's
// postcondition.
// The fail twin: nothing is required of `tag_to_layout`'s result.

use std::ops::Deref;
use thrust_models::forall;

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct LayoutData {
    pub niche: i64,
}

impl thrust_models::Model for LayoutData {
    type Ty = Self;
}

#[thrust::trusted]
#[thrust_macros::requires(forall(|i: usize, d: &&LayoutData|
    !(0 <= i && i < (*fields).len()
        && thrust_macros::post!(<F as Deref>::deref(&(*fields)[i]), d)) || (**d).niche >= 0))]
#[thrust_macros::ensures(true)]
fn univariant<'a, F: Deref<Target = &'a LayoutData> + Copy>(fields: &Vec<F>) -> i64 {
    unimplemented!()
}

#[thrust_macros::requires(forall(|d: &&LayoutData|
    !thrust_macros::post!(<F as Deref>::deref(&local), d) || (**d).niche >= 0))]
#[thrust_macros::requires(forall(|s: i64| thrust_macros::pre!(tag_to_layout(s))))]
#[thrust_macros::ensures(true)]
fn layout<'a, F: Deref<Target = &'a LayoutData> + Copy, T: Fn(i64) -> F>(local: F, tag_to_layout: T) -> i64 {
    let mut fields = Vec::new();
    fields.push(local);
    fields.push(tag_to_layout(0));
    univariant(&fields)
}

fn main() {}
