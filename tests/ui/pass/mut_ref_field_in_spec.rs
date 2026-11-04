//@check-pass
//@compile-flags: -C overflow-checks=on -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// In a specification, `p.x` of a `&mut P` is a field of the current value, `(*p).x`.
struct P {
    x: i64,
    y: i64,
}

impl thrust_models::Model for P {
    type Ty = P;
}

#[thrust_macros::requires(0 <= p.x && p.x < 100)]
#[thrust_macros::ensures((!p).x == p.x + 1 && (!p).y == p.y)]
fn inc(p: &mut P) {
    p.x += 1;
}

fn main() {}
