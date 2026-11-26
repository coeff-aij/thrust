//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=caller THRUST_PER_INSTANCE_GENERICS=1

// The method of `S<T>` calls the per-instance `g` at `T`; the selected `caller` runs it only through
// the vtable of `&S<i64>` as `&dyn Get`, which makes the instance `g::<i64>`; its assertion fails there.

#[thrust_macros::context]
trait Get {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
    fn get(&self) -> i32;
}

#[thrust::callable]
fn g<T: Copy>(_x: T) -> i32 {
    let ok = false;
    assert!(ok);
    1
}

struct S<T>(T);

impl<T: thrust_models::Model> thrust_models::Model for S<T> {
    type Ty = S<<T as thrust_models::Model>::Ty>;
}

#[thrust_macros::context]
impl<T: Copy> Get for S<T> {
    fn get(&self) -> i32 {
        g(self.0)
    }
}

#[thrust::callable]
fn caller() {
    let s = S(3_i64);
    let d: &dyn Get = &s;
    let _ = d.get();
}

fn main() {}
