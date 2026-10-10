//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin extending by a `Counter` past its end, outside `inv`, where `next` panics.

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
        if self.cur == self.end {
            None
        } else {
            assert!(self.cur < self.end);
            let x = self.cur;
            self.cur += 1;
            Some(x)
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
            && o.cur <= o.end
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
    let mut v: Vec<i64> = Vec::new();
    v.extend(Counter { cur: 5, end: 3 });
}
