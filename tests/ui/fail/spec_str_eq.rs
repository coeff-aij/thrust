//@compile-flags: -C debug-assertions=off -A unused-variables

// A `&str` has no model: a specification sees the parameters as `NoModel`, which it may not
// compare, since `a == b` would hold of any two strings.
#[thrust::trusted]
#[thrust_macros::requires(a == b)] //~ ERROR: cannot compare values of `thrust_models::model::NoModel`
#[thrust_macros::ensures(true)]
fn t(a: &str, b: &str) {}

fn main() {
    t("x", "y");
}
