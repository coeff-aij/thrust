//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: RUST_LOG=info

// The log shares stderr with rustc's JSON diagnostics, so none of its lines may start with `{`,
// as the wrapped refinement types of `std.rs`'s `checked_add` would.

fn main() {
    let x: i64 = 1;
    assert!(x + 1 == 2);
}
