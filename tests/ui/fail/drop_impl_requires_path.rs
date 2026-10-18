//@compile-flags: -C debug-assertions=off

// A contract on a destructor is rejected also when written without `thrust_macros`, by the
// attribute the macros expand to.

struct Guard(i32);

impl thrust_models::Model for Guard {
    type Ty = Self;
}

#[thrust::formula_fn]
fn guard_pre(_g: <&mut Guard as thrust_models::Model>::Ty) -> bool {
    true
}

impl Drop for Guard {
    #[allow(path_statements)]
    fn drop(&mut self) { //~ ERROR: a `Drop::drop` takes no `requires` or `ensures`
        #[thrust::requires_path]
        guard_pre;
    }
}

fn main() {
    let _g = Guard(0);
}
