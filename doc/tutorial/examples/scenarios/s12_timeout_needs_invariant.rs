#[thrust_macros::ensures(result <= 100 * v.len())]
fn sum_capped(v: &Vec<i64>) -> i64 {
    let mut s = 0;
    for x in v.iter() {
        if *x <= 100 {
            s += *x;
        } else {
            s += 100;
        }
    }
    s
}

fn main() {}
