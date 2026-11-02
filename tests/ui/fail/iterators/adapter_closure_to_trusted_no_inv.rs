//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_VERIFY_ONLY=main
// As `pass/iterators/adapter_closure_to_trusted.rs`, with a consumer that does not require the
// adapter's `inv`: nothing establishes `inv` of the adapter, which a struct literal builds, so the
// closure is handed over with its obligation, which Thrust cannot state of a value in a field.

use thrust_models::model::Int;

pub struct Keep<P> {
    cur: i64,
    end: i64,
    pred: P,
}

impl<P> thrust_models::Model for Keep<P> {
    type Ty = (i64, i64, thrust_models::model::Closure<P>);
}

impl<P: Fn(&i64) -> bool> Iterator for Keep<P> {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        while self.cur < self.end {
            let x = self.cur;
            self.cur += 1;
            if (self.pred)(&x) {
                return Some(x);
            }
        }
        None
    }
}

#[thrust_macros::context]
impl<P: Fn(&i64) -> bool> IteratorSpec for Keep<P> {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        self.0 <= self.1
            && thrust_models::forall(|x: Int| !(self.0 <= x && x < self.1) || thrust_macros::pre!(self.2(&x)))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<i64>, o: Self) -> bool {
        self.1 == o.1 && self.2 == o.2 && self.0 <= o.0 && o.0 <= o.1
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

#[thrust::trusted]
#[thrust::callable]
fn consume<I: IteratorSpec<Item = i64>>(mut it: I)
where
    I::Item: thrust_models::Model,
{
    let _ = it.next();
}

fn main() {
    let f = |x: &i64| {
        assert!(*x < 10);
        *x > 0
    };
    let k = Keep { cur: 0, end: 3, pred: f };
    consume(k); //~ ERROR: where Thrust cannot follow it
}
