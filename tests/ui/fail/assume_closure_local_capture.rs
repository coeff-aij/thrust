//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `|f: _|` names a closure local; a closure captured by another closure is a capture, which is
// not named (the error says so).
fn main() {
    let f = |x: i64| x + 1;
    let g = |y: i64| {
        thrust_macros::assume!(|f: _| true); //~ ERROR: a variable this closure captures
        f(y)
    };
    let _ = g(1);
}
