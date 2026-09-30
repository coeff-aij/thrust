//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

use thrust_models::model::Int;

#[derive(thrust_macros::Model)]
struct Matrix {
    rows: usize,
    cols: usize,
    words: Vec<u64>,
}

#[thrust_macros::logic]
fn num_words(bits: Int) -> Int {
    (bits + 63) / 64
}

#[thrust_macros::requires(m.words.len() == m.rows * num_words(m.cols))]
#[thrust_macros::requires(m.cols == 64)]
#[thrust_macros::ensures(result == 2 * m.rows)]
fn word_count(m: &Matrix) -> usize {
    m.words.len()
}

fn main() {}
