//@ignore-on-host: draft, passes the frontend and gets no answer from the solver (README.md)
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::coroutine::layout,case_study::iter,case_study::counts::filter_count,case_study::counts::filter_yields_below
// Stage 7 of the rustc-coroutine verification target: `layout()` of rustc_abi's
// layout/coroutine.rs, with the local iterator adapters it calls (rewrites.md R8). The counting
// lemmas it uses are assumed here: those of thrust/lemmas.rs are verified by the `lemmas.rs`
// root, those of thrust/counts.rs are checked by the `counts.rs` root. `counts::filter_count` is
// checked here too: it takes the per-variant closure's `Map` and `Filter`, and a closure held
// inside a struct cannot be handed to a callee Thrust does not analyze. `counts::filter_yields_below`
// is generic in `P` and takes no closure; it is listed here only to be checked with this root's
// settings.
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage and
// drives it.
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
