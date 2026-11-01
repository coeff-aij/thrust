//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_VERIFY_ONLY=main,g
// The twin of `fail/iterators/adapter_closure_generic_field.rs`: `main` runs `g` at a `Q` that
// holds no closure, so the field of type `P` is the one value of the closure type, whose `pre!`
// `inv` states.

use thrust_models::model::Int;

pub struct Keep2<P, Q> {
    cur: i64,
    end: i64,
    pred: P,
    other: Q,
}

impl<P, Q: thrust_models::Model> thrust_models::Model for Keep2<P, Q> {
    type Ty = (i64, i64, thrust_models::model::Closure<P>, <Q as thrust_models::Model>::Ty);
}

pub struct Wr<F>(F);

pub struct Noop;

impl thrust_models::Model for Noop {
    type Ty = ();
}

impl<F> thrust_models::Model for Wr<F> {
    type Ty = thrust_models::model::Closure<F>;
}

pub trait Call {
    fn call(&self, x: &i64) -> bool;
}

impl Call for Noop {
    #[thrust::trusted]
    #[thrust::callable]
    fn call(&self, _x: &i64) -> bool {
        true
    }
}

impl<F: Fn(&i64) -> bool> Call for Wr<F> {
    #[thrust::trusted]
    #[thrust::callable]
    fn call(&self, x: &i64) -> bool {
        (self.0)(x)
    }
}

impl<P: Fn(&i64) -> bool, Q: Call + thrust_models::Model> Iterator for Keep2<P, Q> {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        let x = self.cur;
        self.other.call(&x);
        if (self.pred)(&x) { Some(x) } else { None }
    }
}

#[thrust_macros::context]
impl<P: Fn(&i64) -> bool, Q: Call + thrust_models::Model> IteratorSpec for Keep2<P, Q> {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        self.0 <= self.1
            && thrust_models::forall(|x: Int| !(self.0 <= x && x < self.1) || thrust_macros::pre!(self.2(&x)))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<i64>, o: Self) -> bool {
        self.1 == o.1 && self.2 == o.2 && self.3 == o.3 && self.0 <= o.0 && o.0 <= o.1
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).0 >= (*self).1 && *self == !self
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust_macros::requires(
    k.0 <= k.1
        && thrust_models::forall(|x: Int| !(k.0 <= x && x < k.1) || thrust_macros::pre!(k.2(&x)))
)]
#[thrust_macros::ensures(true)]
fn g<P: Fn(&i64) -> bool, Q: Call + thrust_models::Model>(k: Keep2<P, Q>) {
    let mut k = k;
    let _ = k.next();
}

fn main() {
    let mk = |c: i64| {
        thrust_macros::closure!(
            captures(c: i64),
            requires(*x < c),
            ensures(true),
            move |x: &i64| -> bool { assert!(*x < c); true },
        )
    };
    let k = Keep2 { cur: 0, end: 3, pred: mk(10), other: Noop };
    g(k);
}
