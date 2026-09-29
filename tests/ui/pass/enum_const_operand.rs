//@check-pass
//@compile-flags: -C debug-assertions=off

#[derive(PartialEq)]
#[repr(i8)]
enum E {
    A = -1,
    B = 5,
    C,
}

enum W {
    X(E),
    Y,
}

const K: W = W::X(E::B);

fn is_c(e: E) -> bool {
    e == E::C
}

fn wrapped(w: W) -> bool {
    match w {
        W::X(e) => e == E::B,
        W::Y => false,
    }
}

fn main() {
    assert!(!is_c(E::A));
    assert!(is_c(E::C));
    assert!(wrapped(K));
}
