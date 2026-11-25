//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `local_iterator_override_collect_own_spec` (pass) with an own spec whose precondition std.rs's
// `collect` contract does not imply.
use thrust_models::{exists, forall, Model, model::{Int, Mut, Seq}};
#[derive(PartialEq)]
struct Up {
    n: i64,
}

impl Model for Up {
    type Ty = Up;
}

impl Iterator for Up {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        if self.n < 3 {
            let x = self.n;
            self.n += 1;
            Some(x)
        } else {
            None
        }
    }

    fn collect<B: std::iter::FromIterator<i64>>(self) -> B {
        B::from_iter(self)
    }
}

#[thrust_macros::context]
impl IteratorSpec for Up {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self.n && self.n <= 3
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<i64>, o: Self) -> bool {
        self.n <= o.n
            && o.n <= 3
            && visited.len() == o.n - self.n
            && forall(|i: Int|
                !(0 <= i && i < visited.len()) || visited[i] == self.n + i)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).n >= 3 && *self == !self
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: Seq<Int>,
        b: &Self,
        bc: Seq<Int>,
        c: &Self,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(it.n == 0)]
#[thrust_macros::ensures(
    exists(|done: Up, fin: Up|
        <Up as IteratorSpec>::produces(it, result, done)
            && <Up as IteratorSpec>::completed(Mut::new(done, fin)))
)]
fn _extern_spec_up_collect(it: Up) -> Vec<i64> {
    <Up as Iterator>::collect::<Vec<i64>>(it)
}

#[thrust_macros::requires(I::inv(it))]
#[thrust_macros::ensures(
    exists(|done: <I as Model>::Ty, fin: <I as Model>::Ty|
        I::produces(it, result, done)
            && (I::completed(Mut::new(done, fin))
                || I::fold_completed(Mut::new(done, fin))))
)]
fn collect_all<I: IteratorSpec<Item = i64>>(it: I) -> Vec<i64> {
    it.collect()
}

fn main() {
    let v = collect_all(Up { n: 0 });
    assert!(v.len() == 3);
}
