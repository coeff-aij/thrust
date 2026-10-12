//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `==` in a specification is logical equality, so it compares values holding a `Ghost` by
// their models. `Ghost` has no `PartialEq`: executable code cannot compare it.

use thrust_models::Ghost;

struct Tagged {
    v: i64,
    g: Option<Ghost<i64>>,
}

impl thrust_models::Model for Tagged {
    type Ty = Tagged;
}

#[thrust_macros::predicate]
fn same_tag(a: Tagged, b: Tagged) -> bool {
    a == b
}

#[thrust_macros::requires(a == b)]
#[thrust_macros::ensures(result == b)]
fn pick(a: Option<Ghost<i64>>, b: Option<Ghost<i64>>) -> Option<Ghost<i64>> {
    a
}

#[thrust_macros::requires(same_tag(*a, *b))]
#[thrust_macros::ensures(result == (*b).v)]
fn tag_v(a: &Tagged, b: &Tagged) -> i64 {
    a.v
}

fn main() {
    let x: i64 = 1;
    let g = thrust_macros::ghost!(|x: i64| -> i64 { x });
    let a = Tagged { v: 1, g: Some(g) };
    let b = Tagged { v: 1, g: Some(g) };
    assert!(a.g == b.g); //~ ERROR: binary operation `==` cannot be applied
    assert!(tag_v(&a, &b) == 1);
}
