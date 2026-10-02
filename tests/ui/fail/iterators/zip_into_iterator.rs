//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `zip` takes `IntoIterator`s, not iterators: it holds `a.into_iter()`, here the `vec::IntoIter`
// of a `Vec` and the `slice::Iter` of a `&Vec`.

#[thrust_macros::context]
#[thrust_macros::requires(a.len() > 0 && (*b).len() > 0 && a[0] == 5 && (*b)[0] == 6)]
fn first(a: Vec<i64>, b: &Vec<i64>) {
    let mut it = std::iter::zip(a, b);
    match it.next() {
        Some((x, y)) => assert!(x == 5 && *y == 7),
        None => {}
    }
}

fn main() {}
