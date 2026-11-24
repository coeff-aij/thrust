//@compile-flags: -C debug-assertions=off
// `hist_inv!` relates the states of a closure that may be called more than once; an `FnOnce`
// closure is rejected.

#[thrust::trusted]
#[thrust_macros::ensures(thrust_macros::hist_inv!(g, result))] //~ ERROR: `hist_inv!` needs an `Fn` or `FnMut` closure
fn keep<G: FnOnce() -> Vec<i32>>(g: G) -> G {
    g
}

#[thrust::trusted]
#[thrust_macros::ensures(true)]
fn make() -> Vec<i32> {
    Vec::new()
}

fn main() {
    let v = make();
    keep(move || v);
}
