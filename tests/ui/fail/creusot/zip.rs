//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Fail twin: `next` returns `None` after both `a` and `b` produced an item, which `completed` does not allow.
// Creusot's `examples/iterators/12_zip.rs` (3620de437): `Zip` and its `Iterator` impl, with
// Creusot's code and Thrust's annotations. `invariant` states the inner iterators', which Creusot
// carries as the type invariants of the fields. The `resolve(x)` of the item `a` produced before
// `b` finished, in `completed`, has no counterpart: Thrust has no `resolve` predicate (fork
// issue #156).
use thrust_models::model::{Mut, Seq, Int};
use thrust_models::{exists, forall, Model};

#[path = "../../pass/creusot/auxiliary/common.rs"]
mod common;
pub use common::Iterator;

pub struct Zip<A, B> {
    pub a: A,
    pub b: B,
}

impl<A: Model, B: Model> Model for Zip<A, B> {
    type Ty = Zip<<A as Model>::Ty, <B as Model>::Ty>;
}

#[thrust_macros::context]
impl<A: Iterator, B: Iterator> Iterator for Zip<A, B> {
    type Item = (A::Item, B::Item);

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        A::invariant(self.a) && B::invariant(self.b)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (A::completed(Mut::new((*self).a, (!self).a)) && (*self).b == (!self).b)
            || exists(|x: <<A as Iterator>::Item as Model>::Ty|
                A::produces((*self).a, Seq::singleton(x), (!self).a)
                    && B::completed(Mut::new((*self).b, (!self).b)))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, tl: Self) -> bool {
        exists(|p1: Seq<<<A as Iterator>::Item as Model>::Ty>| exists(|p2: Seq<<<B as Iterator>::Item as Model>::Ty>|
            p1.len() == visited.len()
                && p2.len() == visited.len()
                && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == (p1[i], p2[i]))
                && A::produces(self.a, p1, tl.a)
                && B::produces(self.b, p2, tl.b)))
    }

    fn next(&mut self) -> Option<Self::Item> {
        let x = match self.a.next() {
            None => return None,
            Some(x) => x,
        };
        let y = match self.b.next() {
            None => return None,
            Some(y) => y,
        };
        // Unsat: `next` returns `None` after `a` and `b` both produced an item, so `produces` does not hold.
        let _ = (x, y);
        None
    }
}
