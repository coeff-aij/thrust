//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// A field read through a reference derefs it, as `m.cols` does in Rust.

struct Matrix {
    rows: i64,
    cols: i64,
}

impl thrust_models::Model for Matrix {
    type Ty = Self;
}

#[thrust_macros::requires(m.cols < m.rows)]
#[thrust_macros::ensures(result < m.rows)]
fn cols(m: &Matrix) -> i64 {
    m.cols
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures((!m).rows == m.rows + 1 && (!m).cols == m.cols)]
fn add_row(m: &mut Matrix) {
    m.rows += 1;
}

fn main() {}
