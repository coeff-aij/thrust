//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `next` of a local `IteratorSpec` type with a contract of its own, stronger than the one std.rs
// gives `Iterator::next`: `completed` here does not say the counter is at its end, so only the
// impl's contract says a counter before its end yields an item. The body is checked against the
// impl's contract, the impl's contract against the trait's, and the call in `main` uses the
// impl's.

struct Counter {
    cur: i64,
    end: i64,
}

// `(*self).0` is `self.cur`, `(*self).1` is `self.end`.
impl thrust_models::Model for Counter {
    type Ty = (thrust_models::model::Int, thrust_models::model::Int);
}

#[thrust_macros::context]
impl Iterator for Counter {
    type Item = i64;

    #[thrust_macros::ensures(
        ((*self).0 < (*self).1
            && result == Some((*self).0)
            && (!self).0 == (*self).0 + 1
            && (!self).1 == (*self).1)
        || ((*self).0 >= (*self).1 && result == None && !self == *self)
    )]
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
        self.0 <= self.1
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<i64>, o: Self) -> bool {
        self.1 == o.1
            && self.0 <= o.0
            && o.0 <= o.1
            && visited.len() == o.0 - self.0
            && thrust_models::forall(|i: thrust_models::model::Int|
                !(0 <= i && i < visited.len()) || visited[i] == self.0 + i)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == !self
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
    let x = c.next();
    assert!(matches!(x, Some(0)));
}
