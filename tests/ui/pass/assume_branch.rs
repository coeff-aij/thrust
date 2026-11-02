//@check-pass
//@compile-flags: -C debug-assertions=off

// An `assume!` holds on its own path only.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn main() {
    let x = rand();
    if x > 0 {
        thrust_macros::assume!(|x: i64| x == 1);
        assert!(x == 1);
    } else {
        assert!(x <= 0);
    }
}
