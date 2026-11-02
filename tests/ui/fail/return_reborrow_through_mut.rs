//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

use thrust_models::model::Mut;

#[thrust_macros::ensures(*result == **r && !r == Mut::new(**r, !*r))]
fn get<'b>(r: &'b mut &mut i64) -> &'b mut i64 {
    &mut **r
}

struct H<'a> {
    r: &'a mut i64,
    n: i64,
}

impl H<'_> {
    fn get(&mut self) -> &mut i64 {
        self.r
    }
}

fn main() {
    let mut a = 0_i64;
    let mut r = &mut a;
    *get(&mut r) = 1;

    let mut b = 0_i64;
    let mut h = H { r: &mut b, n: 5 };
    *h.get() += 3;
    assert!(*h.r == 3 && h.n == 5);
    assert!(b == 3);
}
