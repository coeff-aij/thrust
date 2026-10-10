//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The pass twin with the postcondition for index 0 naming the other field, which the
// body does not satisfy.

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
    #[thrust_macros::ensures(index == 0 ==> *result == (*self).1)]
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
    assert!(pair[1] == 7);
}
