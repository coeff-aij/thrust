//@error-in-other-file: in `<Tagged as std::cmp::PartialEq>::eq` compares values holding a `Ghost`
//@compile-flags: -C debug-assertions=off -A unused-variables

// A derived `eq` on a struct with a `Ghost` field runs `Ghost`'s `PartialEq`, which panics.

use thrust_models::Ghost;

#[derive(PartialEq)]
struct Tagged {
    v: i64,
    g: Option<Ghost<i64>>,
}

impl thrust_models::Model for Tagged {
    type Ty = Tagged;
}

fn main() {
    let x: i64 = 1;
    let g = thrust_macros::ghost!(|x: i64| -> i64 { x });
    let a = Tagged { v: 1, g: Some(g) };
    let b = Tagged { v: 1, g: Some(g) };
    assert!(a == b);
}
