//@error-in-other-file: Unsat

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == *dest && !dest == false)]
fn _extern_spec_take(dest: &mut bool) -> bool {
    std::mem::take(dest)
}

fn main() {
    let mut x = true;
    let old = std::mem::take(&mut x);
    assert!(x);
}
