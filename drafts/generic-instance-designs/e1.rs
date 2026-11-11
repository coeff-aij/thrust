#[thrust::callable]
fn apply<F: Fn(i32) -> i32>(f: F) -> i32 {
    f(1)
}

fn main() {
    let _ = apply(|x| x + 1);
}
