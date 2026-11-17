//@compile-flags: -C debug-assertions=off
// `|x: _|` is for a closure local; an integer's type is written.

fn f(x: i64) -> i64 {
    thrust_macros::assume!(|x: _| true); //~ ERROR: `x: _` stands for a closure's type, but `x` has the type `i64`
    x
}

fn main() {
    let _ = f(1);
}
