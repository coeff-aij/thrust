//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=caller,make THRUST_PER_INSTANCE_GENERICS=1

// `make` turns `g::<i64>` into a function pointer that the selected `caller` calls; the assertion of `g` fails at that instance.

#[thrust::callable]
fn g<T: Copy>(x: T) -> T {
    let ok = false;
    assert!(ok);
    x
}

struct H {
    f: fn(i64) -> i64,
}

fn make() -> H {
    H { f: g::<i64> }
}

#[thrust::callable]
fn caller() {
    let h = make();
    let _ = (h.f)(3);
}

fn main() {}
