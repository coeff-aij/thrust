#[thrust::callable]
fn check(x: i64) {
    if x > -1 && x < 1 {
        assert!(x != 0);
    }
}

#[thrust_macros::param(x: &mut { v: i32 | v >= 0 })]
#[thrust_macros::ret(&mut { v: i32 | v >= 1 })]
fn identity(x: &mut i32) -> &mut i32 {
    x
}

fn main() {}
