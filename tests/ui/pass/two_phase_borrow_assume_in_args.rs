//@check-pass
//@compile-flags: -C debug-assertions=off

// `assume!` in the argument names `x`, which `bump` reserves: the annotation reads the value
// before the call, not the value the call leaves.

trait Bump {
    fn bump(&mut self, k: i64);
}

impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}

fn main() {
    let mut x: i64 = 0;
    x.bump({
        thrust_macros::assume!(|x: i64| x == 0);
        5
    });
    assert!(x == 6);
}
