fn main() {
    let f = thrust_macros::closure!(
        ensures(result >= x),
        ensures(result == x + 2),
        |x: i32| -> i32 { x + 1 },
    );
    f(3);
}
