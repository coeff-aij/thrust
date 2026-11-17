fn double(x: i64) -> i64 {
    x + x
}

#[thrust::split_goals]
fn twice() {
    let a = double(2);
    assert!(a == 4);
    let b = double(3);
    assert!(b == 7);
}

fn main() {
    twice();
    let c = double(4);
    assert!(c == 8);
}
