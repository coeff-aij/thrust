//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
#[derive(Clone, Copy)]
pub struct Calc<C> {
    c: C,
    n: i64,
}

impl<C: thrust_models::Model> thrust_models::Model for Calc<C> {
    type Ty = (<C as thrust_models::Model>::Ty, thrust_models::model::Int);
}

#[thrust_macros::context]
impl<C: Copy + thrust_models::Model> Calc<C> {
    #[thrust_macros::ensures(result.1 == (*self).1)]
    fn read(&self, c: C) -> (C, i64) {
        let me = self;
        thrust_macros::block_contract_fn!(
            |me: &Self, c: C| -> (C, i64)
            ensures(result.1 == (*me).1 && (*me).1 == (*me).1),
            { (c, me.n) }
        )
    }
}

fn main() {
    let c = Calc { c: 1i64, n: 3 };
    assert!(c.read(2).1 == 3);
}
