//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:804d76744

// `BitMatrix::wf` of bitset.rs over the model struct `derive(Model)` declares, where the
// fields are `Int` and `Seq<Int>`: the word count is the logic function `num_words` rather
// than an existential. `any_in_word` returns a `bool` because a word read from a field
// carries no `v >= 0` for a `u64` result (coord-e/thrust#165).

use std::marker::PhantomData;
use thrust_models::model::Int;

#[derive(thrust_macros::Model)]
pub struct BitMatrix<R, C> {
    num_rows: usize,
    num_columns: usize,
    words: Vec<u64>,
    marker: PhantomData<(R, C)>,
}

#[thrust_macros::logic]
fn num_words(n: Int) -> Int {
    (n + 63) / 64
}

#[thrust_macros::context]
impl<R, C> BitMatrix<R, C> {
    #[thrust_macros::predicate]
    fn wf(self) -> bool {
        self.words.len() == self.num_rows * num_words(self.num_columns)
    }

    #[thrust_macros::requires(Self::wf(*self))]
    #[thrust_macros::requires(row <= self.num_rows && column < self.num_columns)]
    #[thrust_macros::ensures(true)]
    fn any_in_word(&self, row: usize, column: usize) -> bool {
        let words_per_row = (self.num_columns + 63) / 64;
        self.words[row * words_per_row + column / 64] != 0
    }
}

fn main() {}
