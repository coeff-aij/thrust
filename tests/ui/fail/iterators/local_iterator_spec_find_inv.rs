//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin asserting the counter is short of its end, which a `find` that finds nothing
// leaves it at.

#[derive(PartialEq)]
struct Counter {
    cur: i64,
    end: i64,
}

impl thrust_models::Model for Counter {
    type Ty = Self;
}

impl Iterator for Counter {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        if self.cur < self.end {
            let x = self.cur;
            self.cur += 1;
            Some(x)
        } else {
            None
        }
    }
}

#[thrust_macros::context]
impl IteratorSpec for Counter {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        self.cur <= self.end
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<i64>, o: Self) -> bool {
        self.end == o.end
            && self.cur <= o.cur
            && visited.len() == o.cur - self.cur
            && thrust_models::forall(|i: thrust_models::model::Int|
                !(0 <= i && i < visited.len()) || visited[i] == self.cur + i)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).cur >= (*self).end && *self == !self
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
    let mut c = Counter { cur: 0, end: 3 };
    let _ = c.find(|x| *x == 1);
    assert!(c.cur < c.end);
}
