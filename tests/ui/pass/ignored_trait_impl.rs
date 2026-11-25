//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/ignored_trait_impl.rs`: an impl method that is not ignored is checked against
// the trait's spec, which a call then takes.
use thrust_models::Model;
struct S(i32);

impl Model for S {
    type Ty = Self;
}

impl PartialEq for S {
    fn eq(&self, o: &S) -> bool {
        self.0 == o.0
    }
}

fn main() {
    let a = S(1);
    let _ = a == a;
}
