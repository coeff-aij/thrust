//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_index::bit_set::DenseBitSet::new_empty,rustc_index::bit_set::DenseBitSet::clear_excess_bits,rustc_index::bit_set::DenseBitSet::count,rustc_index::bit_set::DenseBitSet::contains,rustc_index::bit_set::DenseBitSet::insert,rustc_index::bit_set::DenseBitSet::insert_all,rustc_index::bit_set::DenseBitSet::iter,rustc_index::bit_set::BitIter::new,rustc_index::bit_set::BitIter::next,rustc_index::bit_set::BitMatrix::rows,rustc_index::bit_set::BitMatrix::range,rustc_index::bit_set::BitMatrix::iter,rustc_index::bit_set::BitMatrix::count,rustc_index::bit_set::row_cols_below,rustc_index::bit_set::row_words,rustc_index::bit_set::row_bits_clear,rustc_index::bit_set::num_words,rustc_index::bit_set::word_index_and_mask,rustc_index::bit_set::clear_excess_bits_in_final_word,rustc_index::bit_set::bits::bit_range,rustc_index::bit_set::bits::masked_range,rustc_index::bit_set::bits::masked_def,rustc_index::bit_set::bits::set_bit_at,rustc_index::bit_set::bits::set_bit,rustc_index::bit_set::bits::zero_word_bit,rustc_index::bit_set::bits::full_word_bits,rustc_index::bit_set::bits::zero_word_bits,rustc_index::bit_set::bits::low_mask_bits,rustc_index::bit_set::bits::test_bit,rustc_index::bit_set::bits::bit_to_come_range,rustc_index::bit_set::bits::bit_to_come_at_start,rustc_index::bit_set::bits::bits_to_come_at_start,rustc_index::bit_set::bits::bit_to_come_next_word,rustc_index::bit_set::bits::bits_to_come_next_word,rustc_index::bit_set::bits::lowest_bit_set,rustc_index::bit_set::bits::shifted_one,rustc_index::bit_set::bits::xored,rustc_index::bit_set::bits::flipped_word,rustc_index::bit_set::bits::flipped_bit,rustc_index::bit_set::bits::flipped_bits,rustc_index::bit_set::bits::bit_to_come_clear,rustc_index::bit_set::bits::bits_to_come_clear,rustc_index::bit_set::bits::bit_to_come_exhausted,rustc_index::bit_set::bits::bits_to_come_exhausted,rustc_index::bit_set::bits::high_mask_bits,rustc_index::bit_set::bits::bits_clear_of,rustc_index::bit_set::count::zero_bits_ones,rustc_index::bit_set::count::ones_le,rustc_index::bit_set::count::ones_le_upto,rustc_index::bit_set::count::ones_full,rustc_index::bit_set::count::ones_set_bit,rustc_index::bit_set::count::ones_to_come_at_start,rustc_index::bit_set::count::ones_to_come_le,rustc_index::bit_set::count::ones_to_come_next_word,rustc_index::bit_set::count::ones_to_come_clear,rustc_index::bit_set::count::ones_to_come_exhausted,rustc_index::bit_set::count::ones_past,rustc_index::bit_set::filled_bits,rustc_index::bit_set::excess_bits_clear,rustc_index::bit_set::count_ones
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// Generated root: the call graph of `layout()` reaches the functions of row rustc_index in module(s) listed below; see README.md.
#![feature(new_range_api)]

#[path = "../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

fn main() {}
