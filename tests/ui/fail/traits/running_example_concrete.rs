//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:804d76744

// Fail twin of `pass/traits/running_example_concrete.rs`: `count` promises a positive result,
// which an empty range (`start == end`, allowed by the precondition) refutes.
#[derive(PartialEq)]
struct Range {
    start: i64,
    end: i64,
}

impl thrust_models::Model for Range {
    type Ty = Range;
}

#[thrust_macros::context]
impl Range {
    #[thrust_macros::ensures(result == None ==> !((*self).start < (*self).end) && *self == !self)]
    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> (*self).start < (*self).end && i == (*self).start && (!self).start == i + 1 && (!self).end == (*self).end))]
    fn next(&mut self) -> Option<i64> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item)
        } else {
            None
        }
    }
}

#[thrust_macros::context]
#[thrust_macros::requires((*it).start <= (*it).end)]
#[thrust_macros::ensures(result > 0)]
fn count(it: &mut Range) -> i64 {
    let mut n = 0;
    let b = it;
    while let Some(_) = b.next() {
        n += 1;
    }
    n
}

fn main() {
    let mut r = Range { start: 1, end: 5 };
    let n = count(&mut r);
    assert!(n >= 0);
}
