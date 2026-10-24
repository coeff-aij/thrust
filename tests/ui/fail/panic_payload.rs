//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A panic with a message, through each of std's panic entry points: a function of another crate
// without a specification may only be called where it is unreachable, as Creusot specifies one,
// and the payload's `fmt::Arguments` holds opaque raw pointers. `expect` is `unwrap`.
fn checked(x: u64, y: u64, o: Option<u64>, r: Result<u64, u8>) -> u64 {
    if x > 10 {
        panic!("x is {x}, above 10");
    }
    assert!(x < y, "x was {} and y {}", x, y);
    assert_eq!(x + 1, y, "y follows x");
    assert_ne!(x, y);
    let z = match x {
        0 => o.expect("o is some"),
        _ => r.expect("r is ok"),
    };
    if z > 100 {
        unreachable!("z is {}", z);
    }
    z
}

fn main() {
    let _ = checked(0, 1, Some(5), Err(0));
    let _ = checked(2, 3, None, Ok(101));
}
