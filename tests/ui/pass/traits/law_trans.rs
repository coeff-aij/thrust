//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-2493045c3
use thrust_models::Model;

// A trait law: `le_trans` has no body in the trait, each impl proves it with an empty body,
// and wherever the trait's predicates are used through a type parameter the law is a premise.
// `chain` is generic and needs transitivity, which nothing but the law supplies.
#[thrust_macros::context]
trait Le
where
    Self: Model,
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::predicate]
    fn le(self, o: Self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::le(*a, *b) && Self::le(*b, *c))]
    #[thrust_macros::ensures(Self::le(*a, *c))]
    fn le_trans(a: &Self, b: &Self, c: &Self);
}

#[thrust_macros::context]
#[thrust_macros::requires(T::le(*x, *y) && T::le(*y, *z))]
#[thrust_macros::ensures(T::le(*x, *z))]
fn chain<T: Le + Model>(x: &T, y: &T, z: &T)
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty> + PartialEq,
{
}

#[derive(PartialEq)]
struct V {
    v: i64,
}

impl Model for V {
    type Ty = V;
}

#[thrust_macros::context]
impl Le for V {
    #[thrust_macros::predicate]
    fn le(self, o: Self) -> bool {
        self.v <= o.v
    }

    fn le_trans(a: &V, b: &V, c: &V) {}
}

fn main() {
    let a = V { v: 1 };
    let b = V { v: 2 };
    let c = V { v: 3 };
    chain(&a, &b, &c);
}
