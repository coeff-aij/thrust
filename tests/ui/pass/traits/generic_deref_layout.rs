//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use std::ops::Deref;
use thrust_models::forall;

#[derive(Clone, Copy, PartialEq)]
pub struct Niche {
    pub start: u64,
    pub end: u64,
}

impl thrust_models::Model for Niche {
    type Ty = Self;
}

#[derive(Clone, Copy, PartialEq)]
pub struct LayoutData {
    pub size: u64,
    pub largest_niche: Option<Niche>,
}

impl thrust_models::Model for LayoutData {
    type Ty = Self;
}

#[thrust_macros::requires(forall(|f: F, r: &&LayoutData, n: Niche|
    thrust_macros::post!(<F as Deref>::deref(&f), r) && (**r).largest_niche == Some(n)
        ==> n.start <= n.end))]
#[thrust_macros::ensures(true)]
fn niche_len<'a, F: Deref<Target = &'a LayoutData> + Copy>(field: F) -> u64 {
    match field.largest_niche {
        Some(niche) => {
            assert!(niche.start <= niche.end);
            niche.end - niche.start
        }
        None => 0,
    }
}

fn main() {}
