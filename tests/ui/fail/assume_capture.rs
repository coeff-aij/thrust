//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// An `assume!` in a closure's body names a captured variable and bounds it by 10, not by 9.
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
    assert!(v <= 10 && v >= 1);
}
