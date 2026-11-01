pub mod ops;

#[thrust_macros::ensures(result == x + 1)]
pub fn inc(x: i64) -> i64 {
    x + 1
}

pub struct Pair;

impl Pair {
    pub fn twice(x: i64) -> i64 {
        x * 2
    }
}

pub trait Scale {
    fn scale(x: i64) -> i64;
}

impl Scale for Pair {
    fn scale(x: i64) -> i64 {
        Pair::twice(x) + x
    }
}

pub fn sextuple(x: i64) -> i64 {
    let y = Pair::twice(Pair::scale(x));
    assert!(y == x * 6);
    y
}
