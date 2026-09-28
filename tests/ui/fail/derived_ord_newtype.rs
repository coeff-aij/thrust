//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The derived `PartialOrd` / `Ord` of a newtype over an integer call the integer's
// `partial_cmp` / `cmp`; their specifications in std.rs carry the order through.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Align {
    pow2: u8,
}

impl thrust_models::Model for Align {
    type Ty = thrust_models::model::Int;
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (a < b))]
fn lt(a: Align, b: Align) -> bool {
    a < b
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures((a <= b) == (result == std::cmp::Ordering::Less))]
fn cmp(a: Align, b: Align) -> std::cmp::Ordering {
    a.cmp(&b)
}

fn main() {
    assert!(lt(Align { pow2: 1 }, Align { pow2: 2 }));
    let _ = cmp(Align { pow2: 2 }, Align { pow2: 1 });
}
