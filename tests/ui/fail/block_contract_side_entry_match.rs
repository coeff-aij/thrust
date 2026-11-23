//@compile-flags: -C debug-assertions=off

// As `block_contract_side_entry.rs`, with the marker in one arm of a `match`.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

fn main() {
    let c = rand();
    let mut x: i64 = 0;
    match c {
        0 => {
            thrust_macros::block_requires!(|x: i64| x == 0); //~ ERROR: the code under `block_requires!` is also reached by a path that does not pass it
        }
        _ => {}
    }
    x += 1;
    thrust_macros::block_ensures!(|x: i64| x == 1);
    assert!(c == 0);
}
