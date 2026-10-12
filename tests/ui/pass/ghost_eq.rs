//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `==` on a type holding a `Ghost` compares the ghosts' contents in a specification. In
// executable code it would run `Ghost`'s `PartialEq`, which panics, and is rejected.

use thrust_models::Ghost;

struct Tagged {
    v: i64,
    g: Option<Ghost<i64>>,
}

impl thrust_models::Model for Tagged {
    type Ty = Tagged;
}

impl PartialEq for Tagged {
    #[thrust::ignored]
    fn eq(&self, other: &Tagged) -> bool {
        self.v == other.v && self.g == other.g
    }
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
    let _ = pick(a.g, b.g);
    assert!(tag_v(&a, &b) == 1);
}
