//@compile-flags: -C debug-assertions=off

fn to_const(p: *mut i32) -> *const i32 {
    p as *const i32 //~ ERROR: casting a raw pointer is not supported
}

fn main() {
    let _ = to_const;
}
