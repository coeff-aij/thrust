fn count(n: i64) -> i64 {
    let mut c = 0;
    for _i in 0..n {
        c += 1;
    }
    c
}
#[thrust_macros::ensures(result > x)]
fn bad(x: i64) -> i64 { x }
fn main() {}
