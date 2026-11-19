//@compile-flags: -C debug-assertions=off

// `g` is checked at each of its instances in rustc's mono item set, and its own call
// `g(&mut f, ..)` reaches it at another closure type each time, so rustc stops instantiating it.

#[thrust::callable]
fn g<F: FnMut(i32) -> i32>(mut f: F, n: i32) -> i32 {
    if n <= 0 {
        f(1)
    } else {
        g(&mut f, n - 1) //~ ERROR: reached the recursion limit while instantiating
    }
}

fn inc(x: i32) -> i32 {
    x + 1
}

#[thrust::callable]
fn caller() {
    g(inc, 3);
}

fn main() {}
