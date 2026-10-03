# Bit-set facts the solver does not answer

Two variants of `tests/ui/pass/rustc_coroutine/bitset.rs` (fork `main` 7f913c04) whose
bit-level facts verify only up to the solver. Integer bit operations are translated through
bit-vectors (`int_to_bv`, `ubv_to_int`), and the bit-set predicates read bit `i % 64` of word
`i / 64` with `BitVec`.

- `contains_untrusted.rs`: `word_index_and_mask` and `DenseBitSet::contains` untrusted, each
  requiring `Idx::index_is` to hold of one index only. Without that requirement the query is
  `unsat`, correctly: nothing else makes `index_is` functional.
- `insert_all_untrusted.rs`: `DenseBitSet::insert_all`, `clear_excess_bits` and
  `clear_excess_bits_in_final_word` untrusted, with `<[u64]>::fill` specified and the bits below
  `domain_size` stated as kept by the last two.

Both are expected `sat`: the source programs are the pass side of a verified stage file.

Dump:

    RUST_LOG=info THRUST_OUTPUT_DIR=<dir> THRUST_SOLVER=true THRUST_TRY_SPECS=1 \
      target/debug/thrust-rustc -Adead_code -C debug-assertions=off --edition 2021 <file>
