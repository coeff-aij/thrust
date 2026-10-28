//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A method called on a `Box` held in a slice: the deref temporary of `(*s)[1]` is replaced by
// that place, which does not change before the call.
struct Tri {
    a: u32,
}

impl thrust_models::Model for Tri {
    type Ty = Self;
}

impl Tri {
    fn bump(&mut self) {
        self.a += 1;
    }

    fn sides(&self) -> u32 {
        self.a
    }
}

#[thrust::callable]
fn check(s: &mut [Box<Tri>]) {
    if s.len() > 1 {
        let before = s[1].sides();
        s[1].bump();
        assert!(s[1].sides() == before + 1);
    }
}

fn main() {}
