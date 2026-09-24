struct Ring {
    data: i32,
    ntt: bool,
}

impl thrust_models::Model for Ring {
    type Ty = Self;
}

impl PartialEq for Ring {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

fn main() {
    let a = Ring { data: 1, ntt: false };
    let b = Ring { data: 1, ntt: true };
    assert!(a == b);
}
