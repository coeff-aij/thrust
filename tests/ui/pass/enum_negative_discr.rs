//@check-pass
//@compile-flags: -C debug-assertions=off

// An enum with an explicit `repr` narrower than `u32` and a negative discriminant. Both the
// discriminant of each variant and the `switchInt` target that matches on it have to be read as
// signed integers of the `repr` type's width.

#[repr(i8)]
#[derive(PartialEq)]
pub enum Sign {
    Neg = -1,
    Zero = 0,
    Pos = 1,
}

impl thrust_models::Model for Sign {
    type Ty = Sign;
}

#[thrust_macros::ensures((x < 0) ==> (result == Sign::Neg))]
#[thrust_macros::ensures((x == 0) ==> (result == Sign::Zero))]
#[thrust_macros::ensures((x > 0) ==> (result == Sign::Pos))]
fn sign(x: i64) -> Sign {
    if x < 0 {
        Sign::Neg
    } else if x == 0 {
        Sign::Zero
    } else {
        Sign::Pos
    }
}

fn main() {
    let n = match sign(-5) {
        Sign::Neg => 1,
        Sign::Zero => 2,
        Sign::Pos => 3,
    };
    assert!(n == 1);

    let m = match sign(7) {
        Sign::Neg => 1,
        Sign::Zero => 2,
        Sign::Pos => 3,
    };
    assert!(m == 3);
}
