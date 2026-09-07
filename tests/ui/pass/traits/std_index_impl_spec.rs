//@check-pass
//@compile-flags: -C debug-assertions=off

// A specified method whose signature names an associated type of the impl
// (`-> &Self::Output`): the wrapper the specification moves to spells the projection out,
// since `Self::Output` means nothing in the inherent impl the wrapper lands in.

struct Pair {
    left: i64,
    right: i64,
}

// Pair is represented as Tuple<Int, Int>, so `(*self).0` is `self.left`.
impl thrust_models::Model for Pair {
    type Ty = (thrust_models::model::Int, thrust_models::model::Int);
}

#[thrust_macros::context]
impl std::ops::Index<usize> for Pair {
    type Output = i64;

    #[thrust_macros::requires(index < 2)]
    #[thrust_macros::ensures(index == 0 ==> *result == (*self).0)]
    #[thrust_macros::ensures(index == 1 ==> *result == (*self).1)]
    fn index(&self, index: usize) -> &Self::Output {
        if index == 0 {
            &self.left
        } else {
            &self.right
        }
    }
}

fn main() {
    let pair = Pair { left: 4, right: 7 };
    assert!(pair[0] == 4);
    assert!(pair[1] == 7);
}
