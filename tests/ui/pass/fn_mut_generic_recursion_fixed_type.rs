//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `g` is analyzed at `caller`'s closure, and its body calls it at the function item `inc`, a fixed
// type no larger than the closure's: that instance's own recursive call hits the instance already
// analyzed, so this is not polymorphic recursion
// (`fail/fn_mut_generic_polymorphic_recursion.rs`).

#[thrust::callable]
fn g<F: FnMut(i32) -> i32>(mut f: F, n: i32) -> i32 {
    if n <= 0 {
        f(1)
    } else {
        g(inc, n - 1)
    }
}

fn inc(x: i32) -> i32 {
    x + 1
}

#[thrust::callable]
fn caller() {
    let mut k = 0;
    g(
        |x| {
            k += 1;
            x
        },
        2,
    );
}

fn main() {}
