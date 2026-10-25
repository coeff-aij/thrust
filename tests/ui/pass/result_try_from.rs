//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_TRY_SPECS=1

// `?` converts the error through `From::from`, here a local impl with a contract.
struct Small(u8);
struct Big(u8);

impl thrust_models::Model for Small {
    type Ty = Small;
}

impl thrust_models::Model for Big {
    type Ty = Big;
}

#[thrust_macros::context]
impl From<Small> for Big {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.0 == e.0)]
    fn from(e: Small) -> Big {
        Big(e.0)
    }
}

fn conv(r: Result<i32, Small>) -> Result<i32, Big> {
    let x = r?;
    Ok(x + 1)
}

fn main() {
    match conv(Err(Small(7))) {
        Ok(_) => {}
        Err(e) => assert!(e.0 == 7),
    }
}
