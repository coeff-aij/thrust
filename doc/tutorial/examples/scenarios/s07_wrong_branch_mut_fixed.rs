#[thrust_macros::ensures(*a >= *b ==> (*result == *a && !result == !a && !b == *b))]
#[thrust_macros::ensures(*a < *b ==> (*result == *b && !result == !b && !a == *a))]
fn take_max<'a>(a: &'a mut i64, b: &'a mut i64) -> &'a mut i64 {
    if *a >= *b {
        a
    } else {
        b
    }
}

fn main() {
    let mut a = 1;
    let mut b = 2;
    let m = take_max(&mut a, &mut b);
    *m += 1;
    assert!(b == 3);
}
