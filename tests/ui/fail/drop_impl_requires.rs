//@compile-flags: -C debug-assertions=off

// A destructor takes no precondition: Rust runs it wherever a value is dropped, also in code
// Thrust does not analyze, which would not establish one.

struct Guard(i32);

impl thrust_models::Model for Guard {
    type Ty = Self;
}

#[thrust_macros::context]
impl Drop for Guard {
    #[thrust_macros::requires(self.0 == 0)] //~ ERROR: a `Drop::drop` takes no `requires` or `ensures`
    fn drop(&mut self) {}
}

fn main() {
    let _g = Guard(0);
}
