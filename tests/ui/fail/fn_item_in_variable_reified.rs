//@compile-flags: -C debug-assertions=off

fn check(x: i32) {
    assert!(x > 0);
}

fn main() {
    let f = check;
    let p: fn(i32) = f; //~ ERROR: a function pointer made from a function item held in a variable is not supported
    p(1);
}
