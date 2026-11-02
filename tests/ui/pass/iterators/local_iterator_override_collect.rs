//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `Up` overrides `collect`, whose std.rs contract covers only `B = Vec<T>`: verified once over
// `B`, the override has no trait contract to be checked against, so it is checked at the
// instance `B = Vec<i64>` a call takes that contract at.

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

fn main() {
    let v: Vec<i64> = Up { n: 0 }.collect();
    assert!(v.len() == 3);
}
