//@compile-flags: -C debug-assertions=off
// `hist_inv!` relates the states of a closure called more than once; an `FnOnce` closure has
// none, and is rejected.

struct Token(i32);

#[thrust::trusted]
#[thrust_macros::ensures(thrust_macros::hist_inv!(g, result))] //~ ERROR: `hist_inv!` is not supported
fn keep<G: FnOnce() -> i32>(g: G) -> G {
    g
}

fn main() {
    let t = Token(1);
    keep(move || {
        let Token(x) = t;
        x
    });
}
