//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin with an override that panics instead of summing.

#[derive(PartialEq)]
struct Up {
    n: usize,
}

impl thrust_models::Model for Up {
    type Ty = Up;
}

impl Iterator for Up {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        if self.n < 3 {
            let x = self.n;
            self.n += 1;
            Some(x)
        } else {
            None
        }
    }

    fn sum<S: std::iter::Sum<usize>>(self) -> S {
        panic!()
    }
}

#[thrust_macros::context]
impl IteratorSpec for Up {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        self.n <= 3
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<usize>, o: Self) -> bool {
        self.n <= o.n
            && o.n <= 3
            && visited.len() == o.n - self.n
            && thrust_models::forall(|i: thrust_models::model::Int| {
                !(0 <= i && i < visited.len()) || visited[i] == self.n + i
            })
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).n >= 3 && *self == !self
    }

    fn produces_refl(a: &Self) {}
    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<usize as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<usize as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(I::inv(it))]
#[thrust_macros::ensures(
    thrust_models::exists(|prod: thrust_models::model::Seq<<usize as thrust_models::Model>::Ty>,
                           done: <I as thrust_models::Model>::Ty,
                           fin: <I as thrust_models::Model>::Ty|
        I::produces(it, prod, done)
            && I::completed(thrust_models::model::Mut::new(done, fin))
            && result == seq_sum(prod, prod.len()))
)]
fn _extern_spec_usize_sum<I>(it: I) -> usize
where
    I: IteratorSpec<Item = usize>,
{
    <usize as std::iter::Sum<usize>>::sum(it)
}

fn main() {
    let s: usize = Up { n: 0 }.sum();
    assert!(s == 3);
}
