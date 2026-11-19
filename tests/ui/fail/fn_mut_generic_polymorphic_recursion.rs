//@error-in-other-file: polymorphically recursive function
//@compile-flags: -C debug-assertions=off

// `g` is analyzed at each instance a call reaches, and its own call `g(&mut f, ..)` reaches it at
// another closure type, so the analysis stops there.

#[thrust::callable]
fn g<F: FnMut(i32) -> i32>(mut f: F, n: i32) -> i32 {
    if n <= 0 {
        f(1)
    } else {
        g(&mut f, n - 1)
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
