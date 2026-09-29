//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result >= a && result >= b && (result == a || result == b))]
fn max(a: i32, b: i32) -> i32 {
    a.max(b)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result <= a && result <= b && (result == a || result == b))]
fn min(a: i32, b: i32) -> i32 {
    a.min(b)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures((a < b ==> result == Some(std::cmp::Ordering::Less)) && (a == b ==> result == Some(std::cmp::Ordering::Equal)) && (a > b ==> result == Some(std::cmp::Ordering::Greater)))]
fn partial_cmp(a: i32, b: i32) -> Option<std::cmp::Ordering> {
    a.partial_cmp(&b)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures((result ==> a < b) && (a < b ==> result))]
fn lt(a: i32, b: i32) -> bool {
    a.lt(&b)
}

fn main() {
    let _ = (max(1, 2), min(1, 2), partial_cmp(1, 2), lt(1, 2));
}
