#[thrust::callable]
fn apply<F: FnMut(i32) -> i32>(mut f: F) -> i32 {
    f(1)
}

fn main() {
    let mut n = 0;
    let _ = apply(|x| {
        n += 1;
        x + 1
    });
}
