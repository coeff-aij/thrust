//@check-pass
//@compile-flags: -C debug-assertions=off
// The program of `fail/closure_fnonce_hist_inv.rs` with an `FnMut` closure, which `hist_inv!`
// accepts.

#[thrust::trusted]
#[thrust_macros::ensures(thrust_macros::hist_inv!(g, result))]
fn keep<G: FnMut() -> i32>(g: G) -> G {
    g
}

fn main() {
    let mut n: i32 = 0;
    keep(move || {
        n += 1;
        n
    });
}
