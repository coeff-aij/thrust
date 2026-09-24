#[thrust::callable]
fn double(x: u32) -> u32 {
    x << 1
}

fn main() {}
