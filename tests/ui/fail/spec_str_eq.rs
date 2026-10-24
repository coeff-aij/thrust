//@compile-flags: -C debug-assertions=off -A unused-variables

// `a == b` over `&str`s would hold of any two strings, so a `requires` stating it would not
// constrain the call `t("x", "y")`.
#[thrust::trusted]
#[thrust_macros::requires(a == b)] //~ ERROR: cannot compare values of `&str`
#[thrust_macros::ensures(true)]
fn t(a: &str, b: &str) {}

fn main() {
    t("x", "y");
}
