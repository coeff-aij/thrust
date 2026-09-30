//@compile-flags: -Adead_code -C debug-assertions=off

use thrust_models::model::Int;

struct Matrix {
    rows: usize,
    cols: usize,
    words: Vec<u64>,
}

impl thrust_models::Model for Matrix {
    type Ty = Self;
}

#[thrust_macros::logic]
fn num_words(bits: Int) -> Int {
    (bits + 63) / 64
}

#[thrust_macros::predicate]
fn wide(bits: usize) -> bool {
    bits > 64
}

#[thrust_macros::requires((*m).words.len() == (*m).rows * num_words((*m).cols))] //~ ERROR: mismatched types
fn word_count(m: &Matrix) -> usize {
    m.words.len()
}

#[thrust_macros::requires(wide((*m).cols))] //~ ERROR: mismatched types
fn first_row(m: &Matrix) -> usize {
    m.rows
}

fn main() {}
