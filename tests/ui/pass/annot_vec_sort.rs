//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::requires((*v).1 >= 2)]
#[thrust::ensures(
    (^v).0.select(0) <= (^v).0.select(1)
)]
fn sort_two(v: &mut Vec<i64>) {
    if !(v[0] <= v[1]) {
        let tmp = v[1];
        v[1] = v[0];
        v[0] = tmp;
    }
}

fn main() {
    let mut v = Vec::new();
    v.push(2);
    v.push(0);
    sort_two(&mut v);

    assert!(v[0] <= v[1]);
}
