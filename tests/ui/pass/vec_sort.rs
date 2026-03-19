//@check-pass
//@compile-flags: -C debug-assertions=off

fn sort_three(v: &mut Vec<i64>) {
    if v[0] > v[1] {
        let tmp = v[1];
        v[1] = v[0];
        v[0] = tmp;
    }
    if v[1] > v[2] {
        let tmp = v[2];
        v[2] = v[1];
        v[1] = tmp;
    }
    if v[0] > v[1] {
        let tmp = v[1];
        v[1] = v[0];
        v[0] = tmp;
    }
}

fn main() {
    let mut v = Vec::new();
    v.push(2);
    v.push(0);
    v.push(1);
    sort_three(&mut v);

    assert!(v[0] <= v[1]);
    assert!(v[1] <= v[2]);
    assert!(v[0] <= v[2]);
}
