//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `collect_all` is verified once over `I`, taking std.rs's `collect` contract at `Vec<i64>`;
// at `I = Up` the call runs `Up`'s override, which is checked against that contract at that
// instance.

#[derive(PartialEq)]
struct Up {
    n: i64,
}

impl thrust_models::Model for Up {
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
            && thrust_models::forall(|i: thrust_models::model::Int|
                !(0 <= i && i < visited.len()) || visited[i] == self.n + i)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).n >= 3 && *self == !self
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<thrust_models::model::Int>,
        b: &Self,
        bc: thrust_models::model::Seq<thrust_models::model::Int>,
        c: &Self,
    ) {
    }
}

fn collect_all<I: IteratorSpec<Item = i64>>(it: I) -> Vec<i64> {
    it.collect()
}

fn main() {
    let v = collect_all(Up { n: 0 });
    assert!(v.len() == 3);
}
