//@check-pass
//@compile-flags: -C debug-assertions=off
// An `assume!` in a closure's body names a variable the closure captures, as it names its own
// parameters and locals.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn main() {
    let n = rand();
    let add = |y: i64| -> i64 {
        thrust_macros::assume!(|n: i64| n >= 0 && n <= 10);
        y + n
    };
    let v = add(1);
    assert!(v <= 11 + 0 && v >= 1);
}
