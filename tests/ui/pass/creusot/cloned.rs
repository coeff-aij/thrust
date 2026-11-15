//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `examples/iterators/13_cloned.rs` (3620de437): `Cloned` and its `Iterator` impl, with
// Creusot's code and Thrust's annotations. `invariant` states the inner iterator's, which Creusot
// carries as the type invariant of the field; `resolve(self)` in `completed` is spelled out.
// `next` matches the inner `next()` where Creusot calls `Option::cloned`, which std.rs does not specify.
// `T::clone.postcondition((s[i],), visited[i])` is `s[i] == &visited[i]`: a clone is its referent in the model, as std.rs's `Cloned` has it.
use thrust_models::forall;
use thrust_models::exists;
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::Model;

#[path = "auxiliary/common.rs"]
mod common;
pub use common::Iterator;

pub struct Cloned<I> {
    pub iter: I,
}

impl<I: Model> Model for Cloned<I> {
    type Ty = Cloned<<I as Model>::Ty>;
}

#[thrust_macros::context]
impl<'a, I, T: 'a> Iterator for Cloned<I>
where
    I: Iterator<Item = &'a T>,
    T: Clone + Model,
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
                && visited.len() == s.len()
                && forall(|i: Int| !(0 <= i && i < s.len()) || s[i] == &visited[i])
        })
    }

    fn next(&mut self) -> Option<T> {
        match self.iter.next() {
            None => None,
            Some(x) => Some(x.clone()),
        }
    }
}
