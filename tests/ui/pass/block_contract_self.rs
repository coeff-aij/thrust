//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A block in a method of a generic impl names a predicate of the impl by `Self::`. The receiver
// keeps its model, `C`'s (the `Model` impl below), in the method: a formula relates it to the
// receiver's field, of type `C`.
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
        let me = self;
        let (c, m) = thrust_macros::block_contract!(
            |me: &Self, n: i64| -> (C, i64)
            requires(Self::below(*me, n)),
            ensures(Self::below(*me, result.1)),
            {
                let c = me.c;
                let m = n;
                (c, m)
            }
        );
        thrust_macros::proof_assert!(|self: &Calc<C>, c: C| either::<C>(*self, c));
        m
    }
}
fn main() {}
