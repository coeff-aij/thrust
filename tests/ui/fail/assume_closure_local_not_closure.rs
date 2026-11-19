//@compile-flags: -C debug-assertions=off
// `|x: _|` is for a closure local; an integer's type is written.

fn f(x: i64) -> i64 {
    thrust_macros::assume!(|x: _| true); //~ ERROR: in the type of `x`: `_` stands for a closure's type, but it has the type `i64` there
    x
}

fn main() {
    let _ = f(1);
}
