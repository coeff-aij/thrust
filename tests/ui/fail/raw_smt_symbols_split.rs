//@error-in-other-file: which the query does not declare (a name Thrust generates, by its hash)
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SPLIT=2
#![feature(custom_inner_attributes)]
#![thrust::raw_command("(define-fun is_double ((x Int) (y Int)) Bool (= (* x 2) y))")]

// A raw SMT-LIB2 body names a function of a raw command and the selectors of a tuple, both of
// which the query declares.
#[thrust_macros::predicate]
fn doubled(p: (i64, i64)) -> bool {
    "(is_double (tuple_proj<Int-Int>.0 p) (second_ee0fcd4f4ccedd188692f9aa4f468aed p))";
    true
}

#[thrust_macros::ensures(doubled(result))]
fn pair(x: i64) -> (i64, i64) {
    (x, x + x)
}

fn main() {
    pair(3);
}
