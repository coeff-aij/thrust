//@check-pass
//@compile-flags: -C debug-assertions=off
// `&*p` borrows the place `*p`, a deref of the reference parameter `p`, which rustc captures as
// that place; the clauses name it `p` with `p`'s type `&i32`.
#[thrust_macros::requires(*p == 5)]
fn add_to(p: &i32) -> i32 {
    let f = thrust_macros::closure!(
        captures(p: &i32),
        requires(x > 0),
        ensures(result == x + *p),
        |x: i32| -> i32 {
            let q: &i32 = &*p;
            x + *q
        },
    );
    let r = f(7);
    assert!(r == 12);
    r
}

fn main() {
    add_to(&5);
}
