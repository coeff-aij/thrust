//@check-pass
//@compile-flags: -C debug-assertions=off

// A function a `macro_rules!` macro writes binds its parameter through the `$n` it is passed, so
// the parameter is named `n`, also as `old!(n)`, as the caller writes it.
macro_rules! count_down {
    ($f:ident, $n:ident) => {
        #[thrust_macros::requires($n >= 0)]
        #[thrust_macros::ensures(result == 0)]
        fn $f(mut $n: i64) -> i64 {
            while $n > 0 {
                thrust_macros::invariant!(|$n: i64, old!($n): i64| $n >= 0 && $n <= old!($n));
                $n -= 1;
            }
            $n
        }
    };
}

count_down!(down, n);

fn main() {
    assert!(down(3) == 0);
}
