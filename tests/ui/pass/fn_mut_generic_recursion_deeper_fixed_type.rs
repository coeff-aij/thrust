//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `g` is analyzed at the function item `inc`, and its body calls it at the opaque type `wrapped`
// returns, a type that is not the entry instance's. That type is fixed: the instance's own recursive call reaches
// the instance already analyzed, so this is not polymorphic recursion
// (`fail/fn_mut_generic_polymorphic_recursion.rs`).

#[thrust::callable]
fn g<F: FnMut(i32) -> i32>(mut f: F, n: i32) -> i32 {
    if n <= 0 {
        f(1)
    } else {
        g(wrapped(), n - 1)
    }
}

fn wrapped() -> impl FnMut(i32) -> i32 {
    |x| inc(x)
}

fn inc(x: i32) -> i32 {
    x + 1
}

#[thrust::callable]
fn caller() {
    g(inc, 3);
}

fn main() {}
