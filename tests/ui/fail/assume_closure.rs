//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// An `assume!` in a closure holds after it in the closure's body, also where the loop calls it.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn main() {
    let clamp = |y: i64| -> i64 {
        thrust_macros::assume!(|y: i64| y >= 0 && y <= 10);
        y
    };
    let mut i = 0;
    while i < 3 {
        let v = clamp(rand());
        assert!(v <= 9);
        i += 1;
    }
}
