//@ignore-on-host: not yet verifiable: PCSat gives no answer within 150 s on fptprove develop c471e831b; ruling out `None` from `next` needs a sequence of 3 items `Up` produces, as a witness against the universal in the TrustedRandomAccess disjunct of `Skip`'s `completed`
//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `Skip` over an iterator with its own `IteratorSpec`: std's `Skip::next` calls the iterator's
// `nth`, which is checked against `Iterator::nth`'s contract.

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
        if self.n < 10 {
            let x = self.n;
            self.n += 1;
            Some(x)
        } else {
            None
        }
    }
}

#[thrust_macros::context]
impl IteratorSpec for Up {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        self.n <= 10
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<i64>, o: Self) -> bool {
        self.n <= o.n
            && o.n <= 10
            && visited.len() == o.n - self.n
            && thrust_models::forall(|i: thrust_models::model::Int|
                !(0 <= i && i < visited.len()) || visited[i] == self.n + i)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).n >= 10 && *self == !self
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
    let mut s = (Up { n: 0 }).skip(2);
    let x = s.next();
    assert!(matches!(x, Some(2)));
}
