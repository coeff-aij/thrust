#![feature(stmt_expr_attributes)]
#[thrust::split_goals]
struct S;

fn main() {
    let f = #[thrust::split_goals]
    |x: i64| x + 1;
    assert!(f(1) == 2);
}
