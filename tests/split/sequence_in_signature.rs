fn first_or_zero(v: &mut Vec<i64>) -> i64 {
    v.push(1);
    v.len() as i64
}
#[thrust_macros::ensures(result > x)]
fn bad(x: i64) -> i64 { x }
fn main() {
    let mut v = Vec::new();
    let n = first_or_zero(&mut v);
    assert!(n >= 1);
}
