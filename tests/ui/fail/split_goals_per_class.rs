//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// `definite` and `not_definite` have written contracts, so their clauses are two classes. At the
// call in `not_definite`, `post!` of the closures are unknowns, and `either`'s body analyzed with
// them has a disjunction of two unknowns in the head of its `ensures`: that class is one part,
// while the two assertions of `definite` are a cone each. The assertion of `not_definite` fails:
// `either` returns `g(x)`, 6.
fn double(x: i64) -> i64 {
    x + x
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn definite() {
    let a = double(2);
    assert!(a == 4);
    let b = double(3);
    assert!(b == 6);
}

#[thrust_macros::requires(thrust_macros::pre!(g(x)) && thrust_macros::pre!(h(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), result) || thrust_macros::post!(h(x), result))]
fn either<G: Fn(i64) -> i64, H: Fn(i64) -> i64>(g: &G, h: &H, x: i64) -> i64 {
    g(x)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn not_definite() {
    let g = |x: i64| x + 1;
    let h = |x: i64| x - 1;
    let r = either(&g, &h, 5);
    assert!(r == 5);
}

fn main() {
    definite();
    not_definite();
}
