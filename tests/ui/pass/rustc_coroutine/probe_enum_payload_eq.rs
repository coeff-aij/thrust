//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

use thrust_models::exists;

#[derive(PartialEq)]
enum E {
    A,
    B(i64),
    C(Option<i64>),
}

impl thrust_models::Model for E {
    type Ty = Self;
}

#[thrust_macros::requires(x == E::B(3))]
#[thrust_macros::ensures(true)]
fn test_b(x: E) {
    if let E::B(n) = x {
        assert!(n == 3);
    } else {
        loop {}
    }
}

#[thrust_macros::requires(exists(|k: i64| x == E::C(Some(k))))]
#[thrust_macros::ensures(true)]
fn test_c(x: E) {
    if let E::C(Some(k)) = x {
        let _ = k;
    } else {
        loop {}
    }
}

fn main() {
    test_b(E::B(3));
    test_c(E::C(Some(7)));
}
