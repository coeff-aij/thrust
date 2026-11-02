//@compile-flags: -C debug-assertions=off

// A slice pattern on a mutable slice borrows its element mutably, which is not supported.

fn bump(s: &mut [i64]) {
    if let [x, ..] = s { //~ ERROR: a mutable borrow into a slice or an array by a slice pattern
        *x += 1;
    }
}

fn main() {
    let mut a = [1, 2];
    bump(&mut a);
}
