//@check-pass
//@compile-flags: -C debug-assertions=off

// The specification written on `Add::add` reaches the `+` in `main`.

#[derive(PartialEq)]
struct Size {
    raw: i64,
}

impl thrust_models::Model for Size {
    type Ty = Size;
}

#[thrust_macros::context]
impl std::ops::Add for Size {
    type Output = Size;

    #[thrust_macros::ensures(result.raw == self.raw + other.raw)]
    fn add(self, other: Size) -> Self::Output {
        Size {
            raw: self.raw + other.raw,
        }
    }
}

fn main() {
    let sum = Size { raw: 2 } + Size { raw: 3 };
    assert!(sum.raw == 5);
}
