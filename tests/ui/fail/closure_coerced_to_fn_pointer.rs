//@compile-flags: -C debug-assertions=off

fn main() {
    let p: fn(i32) = |x: i32| assert!(x > 0); //~ ERROR: a closure coerced to a function pointer is not supported
    p(1);
}
