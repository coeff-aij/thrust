//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

#[thrust_macros::requires((*v).length > 0)]
#[thrust_macros::requires((*v).array[0].length > 0)]
#[thrust_macros::ensures(true)]
#[thrust_macros::context]
fn test(v: &Vec<Vec<i64>>) {
    assert!(v[0][0] >= 0);
}

fn main() {
    let mut inner = Vec::new();
    inner.push(1_i64);
    inner.push(2);
    let mut v = Vec::new();
    v.push(inner);
    test(&v);
}
