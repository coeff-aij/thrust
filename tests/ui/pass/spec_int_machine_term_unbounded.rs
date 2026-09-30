//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

struct Matrix {
    rows: usize,
    cols: usize,
}

impl thrust_models::Model for Matrix {
    type Ty = Self;
}

#[thrust_macros::requires(m.cols < m.rows)]
#[thrust_macros::ensures(m.cols - m.rows < 0)]
fn narrow(m: Matrix) {}

fn main() {}
