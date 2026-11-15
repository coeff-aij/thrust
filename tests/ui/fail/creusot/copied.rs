//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `examples/iterators/14_copied.rs` (3620de437): `Copied` and its `Iterator` impl, with
// Creusot's code and Thrust's annotations. `invariant` states the inner iterator's, which Creusot
// carries as the type invariant of the field; `resolve(self)` in `completed` is spelled out.
// `next` matches the inner `next()` where Creusot calls `Option::copied`, which std.rs does not specify.
// `visited[i] == *s[i]` is `s[i] == &visited[i]` (the model of `&T` is a reference to `T`'s).
use thrust_models::forall;
use thrust_models::exists;
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::Model;

#[path = "../../pass/creusot/auxiliary/common.rs"]
mod common;
pub use common::Iterator;

pub struct Copied<I> {
    pub iter: I,
}

impl<I: Model> Model for Copied<I> {
    type Ty = Copied<<I as Model>::Ty>;
}

#[thrust_macros::context]
impl<'a, I, T: 'a> Iterator for Copied<I>
where
    I: Iterator<Item = &'a T>,
    T: Copy + Model,
{
    type Item = T;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.iter)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).iter, (!self).iter))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        exists(|s: Seq<&'a <T as Model>::Ty>| {
            I::produces(self.iter, s, o.iter)
                // Unsat: `visited` is one longer than `s`, so `next` does not produce its item.
                && visited.len() == s.len() + 1
                && forall(|i: Int| !(0 <= i && i < s.len()) || s[i] == &visited[i])
        })
    }

    fn next(&mut self) -> Option<T> {
        match self.iter.next() {
            None => None,
            Some(x) => Some(*x),
        }
    }
}
