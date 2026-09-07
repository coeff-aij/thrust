//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A variant without an explicit discriminant takes the value of the preceding one plus one, so
// `Mid` is 6 and `High` is 7 here. Numbering them from zero instead would make the `switchInt`
// targets (which are the real discriminants) match no variant at all.

#[repr(i8)]
#[derive(PartialEq)]
pub enum Level {
    Low = 5,
    Mid,
    High,
}

impl thrust_models::Model for Level {
    type Ty = Level;
}

#[thrust_macros::ensures((x < 10) ==> (result == Level::Low))]
#[thrust_macros::ensures(((x >= 10) && (x < 100)) ==> (result == Level::Mid))]
#[thrust_macros::ensures((x >= 100) ==> (result == Level::High))]
fn level(x: i64) -> Level {
    if x < 10 {
        Level::Low
    } else if x < 100 {
        Level::Mid
    } else {
        Level::High
    }
}

fn main() {
    let n = match level(50) {
        Level::Low => 1,
        Level::Mid => 2,
        Level::High => 3,
    };
    assert!(n == 3);
}
