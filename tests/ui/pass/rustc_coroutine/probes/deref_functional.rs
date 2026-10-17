//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// layout.rs's `deref_functional` reduced: `post!` of a generic `Deref::deref` is a relation, so
// a contract that concludes from some layout it allows (`univariant_biased`'s `End` niche) holds
// of a body that dereferences once only when `deref` is a function. `end` is verified under that
// requirement, which the fail twin drops; `start` concludes towards some allowed layout and needs
// nothing. A newtype over an interned pointer, as rustc's `Layout`, discharges the requirement.

use std::ops::Deref;
use thrust_models::{exists, forall};

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct LayoutData {
    pub niche: i64,
}

impl thrust_models::Model for LayoutData {
    type Ty = Self;
}

#[derive(Copy, Clone)]
pub struct Interned<'a, T>(&'a T);

#[derive(Copy, Clone)]
pub struct Layout<'a>(Interned<'a, LayoutData>);

impl<'a, T> thrust_models::Model for Interned<'a, T> {
    type Ty = Self;
}

impl<'a> thrust_models::Model for Layout<'a> {
    type Ty = Self;
}

impl<'a> Deref for Layout<'a> {
    type Target = &'a LayoutData;

    fn deref(&self) -> &&'a LayoutData {
        &self.0.0
    }
}

#[thrust_macros::predicate]
fn deref_functional<'a, F: Deref<Target = &'a LayoutData> + Copy>() -> bool {
    forall(|x: F, d1: &&LayoutData, d2: &&LayoutData|
        !(thrust_macros::post!(<F as Deref>::deref(&x), d1)
            && thrust_macros::post!(<F as Deref>::deref(&x), d2))
            || **d1 == **d2)
}

#[thrust_macros::predicate]
fn has_niche<'a, F: Deref<Target = &'a LayoutData> + Copy>(f: F) -> bool {
    exists(|d: &&LayoutData| thrust_macros::post!(<F as Deref>::deref(&f), d) && (**d).niche >= 0)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!result || has_niche::<F>(f))]
fn start<'a, F: Deref<Target = &'a LayoutData> + Copy>(f: F) -> bool {
    (**f).niche >= 0
}

#[thrust_macros::requires(deref_functional::<F>())]
#[thrust_macros::ensures(!has_niche::<F>(f) || result)]
fn end<'a, F: Deref<Target = &'a LayoutData> + Copy>(f: F) -> bool {
    (**f).niche >= 0
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn calculate(l: Layout) -> bool {
    end(l)
}

fn main() {}
