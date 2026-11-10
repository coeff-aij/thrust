//@compile-flags: -C debug-assertions=off -A dead_code

// Thrust enables `specialization` for its std.rs only: without the feature in the crate, a
// `default` item of the crate's own is rejected, as rustc rejects it.
trait Lim {
    fn lim(&self) -> i64;
}

impl<T> Lim for T { //~ ERROR: specialization needs `#![feature(specialization)]`
    default fn lim(&self) -> i64 {
        0
    }
}

fn main() {}
