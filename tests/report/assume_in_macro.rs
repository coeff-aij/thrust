macro_rules! make_get {
    ($name:ident) => {
        #[thrust_macros::requires(true)]
        #[thrust_macros::ensures(result == 0)]
        fn $name() -> i64 {
            let x: i64 = 1;
            thrust_macros::assume!(|x: i64| x == 0);
            x
        }
    };
}

make_get!(get);

fn main() {
    assert!(get() == 0);
}
