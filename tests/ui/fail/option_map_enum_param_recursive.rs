//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// A closure taking a generic recursive enum, passed to `Option::map`: no finite formula follows
// the payloads of the list, so the precondition states the refinement of its type argument of
// every `i64`.
enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

fn main() {
    let r = Some(List::Cons(1i64, Box::new(List::Nil))).map(|l: List<i64>| -> i64 {
        match l {
            List::Cons(x, _) => x,
            List::Nil => 0,
        }
    });
    assert!(r == Some(0));
}
