//@compile-flags: -C debug-assertions=off

// An `Iterator::sum` override whose body calls `S::sum` at its type parameter reaches a method
// without a specification: Thrust stops at the call instead of assuming a contract.
struct Up {
    n: usize,
}

impl Iterator for Up {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        None
    }

    fn sum<S: std::iter::Sum<usize>>(self) -> S {
        S::sum(Vec::<usize>::new().into_iter()) //~ ERROR: no specification of
    }
}

fn main() {
    let u = Up { n: 0 };
    let _: usize = u.sum();
}
