//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/partial_move_mut_ref_join.rs`: `a` is written only on the path that moves
// `t.0` out.

fn cond() -> bool {
    true
}

fn main() {
    let mut a = 0;
    let t = (Some(&mut a), 1);
    let c = cond();
    if c {
        let y = t.0;
        if let Some(r) = y {
            *r = 5;
        }
    }
    assert!(c || a == 0);
}
