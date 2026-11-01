//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_VERIFY_ONLY=main
// As `pass/iterators/adapter_closure_in_inv.rs`, with more closures of the same type in a `Vec`
// field that `inv` states no `pre!` of: the `pre!` stated covers only one value of the type, and
// `Vec<P>` holds its elements behind a raw allocation, so the call stops.

use thrust_models::model::Int;

pub struct Keep<P> {
    cur: i64,
    end: i64,
    pred: P,
    others: Vec<P>,
}

impl<P> thrust_models::Model for Keep<P> {
    type Ty = (i64, i64, thrust_models::model::Closure<P>, Vec<thrust_models::model::Closure<P>>);
}

impl<P: Fn(&i64) -> bool> Iterator for Keep<P> {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        while self.cur < self.end {
            let x = self.cur;
            self.cur += 1;
            if (self.pred)(&x) && (self.others[0])(&x) {
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

fn main() {
    let f = |x: &i64| { assert!(*x < 10); *x > 0 };
    let mut others = Vec::new();
    others.push(f);
    let mut k = Keep { cur: 0, end: 3, pred: f, others };
    let _ = k.next(); //~ ERROR: where Thrust cannot follow it
}
