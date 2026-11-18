//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A block contract in a method of a generic impl names a predicate of the impl by `Self::`. The
// receiver keeps its model, `C`'s (the `Model` impl below), in the method: a formula relates it
// to the receiver's field, of type `C`. The block's `ensures` at `n - 1` is refuted.
#[derive(Clone, Copy)]
pub struct Calc<C> {
    c: C,
}

impl<C: thrust_models::Model> thrust_models::Model for Calc<C> {
    type Ty = <C as thrust_models::Model>::Ty;
}

#[thrust_macros::predicate]
fn either<C: thrust_models::Model<Ty: PartialEq>>(a: C, b: C) -> bool {
    a == b || b == b
}

#[thrust_macros::context]
impl<C: Copy + thrust_models::Model<Ty: PartialEq>> Calc<C> {
    #[thrust_macros::predicate]
    fn below(calc: Calc<C>, n: i64) -> bool {
        0 <= n
    }

    #[thrust_macros::requires(0 <= n)]
    #[thrust_macros::ensures(0 <= result)]
    fn step(&self, n: i64) -> i64 {
        thrust_macros::block_requires!(|self: &Calc<C>, n: i64| Self::below(*self, n));
        let c = self.c;
        let m = n - 1;
        thrust_macros::block_ensures!(|self: &Calc<C>, m: i64| Self::below(*self, m));
        thrust_macros::proof_assert!(|self: &Calc<C>, c: C| either::<C>(*self, c));
        m
    }
}

fn main() {}
