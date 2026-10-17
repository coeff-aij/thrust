#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 {
    unimplemented!()
}

fn take_max<'a>(a: &'a mut i64, b: &'a mut i64) -> &'a mut i64 {
    if *a >= *b {
        a
    } else {
        b
    }
}

fn main() {
    let mut a = rand();
    let mut b = rand();
    let m = take_max(&mut a, &mut b);
    *m += 0;
    assert!(a != b);
}
