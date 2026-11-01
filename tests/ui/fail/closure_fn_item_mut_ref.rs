//@compile-flags: -C debug-assertions=off
// A call through `&mut F` has no contract here, as `pre!` of a `&mut` closure has none.

fn inc(x: i32) -> i32 {
    x + 1
}

fn apply<G: FnMut(i32) -> i32>(mut g: G, x: i32) -> i32 {
    g(x) //~ ERROR: a call through an `Fn` bound at `&mut fn(i32) -> i32 {inc}` is not supported
}

fn main() {
    let mut f = inc;
    apply(&mut f, 4);
}
