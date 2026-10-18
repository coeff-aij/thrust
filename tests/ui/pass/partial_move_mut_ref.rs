//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/partial_move_mut_ref.rs`: the write through the `&mut` moved out of `t`
// reaches `a`.

fn main() {
    let mut a = 0;
    let t = (Some(&mut a), 1);
    let y = t.0;
    if let Some(r) = y {
        *r = 5;
    }
    assert!(a == 5);
}
