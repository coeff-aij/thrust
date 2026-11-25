//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::Model;
// A block contract in a method of a generic impl names a predicate of the impl by `Self::`. The
// receiver keeps its model, `C`'s (the `Model` impl below), in the method: a formula relates it
// to the receiver's field, of type `C`.
#[derive(Clone, Copy)]
pub struct Calc<C> {
    c: C,
}

impl<C: Model> Model for Calc<C> {
    type Ty = <C as Model>::Ty;
}

#[thrust_macros::predicate]
fn either<C: Model<Ty: PartialEq>>(a: C, b: C) -> bool {
    a == b || b == b
}

#[thrust_macros::context]
impl<C: Copy + Model<Ty: PartialEq>> Calc<C> {
    #[thrust_macros::predicate]
    fn below(calc: Calc<C>, n: i64) -> bool {
        0 <= n
    }

    #[thrust_macros::requires(0 <= n)]
    #[thrust_macros::ensures(0 <= result)]
    fn step(&self, n: i64) -> i64 {
        let (c, m) = thrust_macros::block_contract!(
            requires(|self: &Calc<C>, n: i64| Self::below(*self, n)),
            ensures(|self: &Calc<C>, result: (C, i64)| Self::below(*self, result.1)),
            {
                let c = self.c;
                let m = n;
                (c, m)
            }
        );
        thrust_macros::proof_assert!(|self: &Calc<C>, c: C| either::<C>(*self, c));
        m
    }
}

fn main() {}
