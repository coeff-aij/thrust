struct Ring {
    data: [i32; 4],
}

impl thrust_models::Model for Ring {
    type Ty = Self;
}

#[thrust::callable]
fn set(r: &mut Ring, i: usize) {
    if i < 4 {
        r.data[i] = 1;
    }
}

fn main() {}
