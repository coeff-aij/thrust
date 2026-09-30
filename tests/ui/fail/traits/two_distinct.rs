//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:804d76744
use thrust_models::Model;

// A law that bounds the size of a type from below. A universal sort ranges over every non-empty
// type, singletons included, so `other` cannot promise a value different from its argument
// unless the trait says the type has two distinguishable values: `is_a` and `is_b` never hold
// of the same value. The law is proved by each impl and assumed in `other`; without it the
// query is unsatisfiable (fail/traits/two_distinct.rs), and an impl whose two predicates
// coincide is refuted (fail/traits/two_distinct_impl.rs).
#[thrust_macros::context]
trait Two
where
    Self: Model + Sized,
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::predicate]
    fn is_a(self) -> bool;

    #[thrust_macros::predicate]
    fn is_b(self) -> bool;

    #[thrust_macros::ensures(Self::is_b(result))]
    fn b(&self) -> Self;

}

#[thrust_macros::context]
#[thrust_macros::requires(T::is_a(*x))]
#[thrust_macros::ensures(result != *x)]
fn other<T: Two + Model>(x: &T) -> T
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty> + PartialEq,
{
    x.b()
}

#[derive(PartialEq)]
struct V {
    v: i64,
}

impl Model for V {
    type Ty = V;
}

#[thrust_macros::context]
impl Two for V {
    #[thrust_macros::predicate]
    fn is_a(self) -> bool {
        self.v == 0
    }

    #[thrust_macros::predicate]
    fn is_b(self) -> bool {
        self.v == 1
    }

    fn b(&self) -> V {
        V { v: 1 }
    }

}

fn main() {
    let a = V { v: 0 };
    let o = other(&a);
    assert!(o.v != a.v);
}
