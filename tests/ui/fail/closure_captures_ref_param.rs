//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// The fail twin of closure_captures_ref_param.rs: the body adds one more than the `ensures`
// states of the captured `p`.
#[thrust_macros::requires(*p == 5)]
fn add_to(p: &i32) -> i32 {
    let f = thrust_macros::closure!(
        captures(p: &i32),
        requires(x > 0),
        ensures(result == x + *p),
        |x: i32| -> i32 {
            let q: &i32 = &*p;
            x + *q + 1
        },
    );
    let r = f(7);
    assert!(r == 12);
    r
}

fn main() {
    add_to(&5);
}
