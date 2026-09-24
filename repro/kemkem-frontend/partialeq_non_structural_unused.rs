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

fn main() {}
