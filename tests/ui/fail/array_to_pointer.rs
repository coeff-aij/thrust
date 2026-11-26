//@compile-flags: -C debug-assertions=off

fn main() {
    let a = [1, 2, 3];
    let p = &a as *const i32; //~ ERROR: taking a raw pointer is not supported
    let _ = p;
}
