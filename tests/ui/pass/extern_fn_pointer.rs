//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_UNSPECIFIED_UNREACHABLE=1

// A pointer to a function without a specification may be made; calling it must be unreachable.
fn main() {
    let f: fn() -> u32 = std::process::id;
    let _ = f;
}
