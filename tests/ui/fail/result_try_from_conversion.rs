//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:9799dfd7b THRUST_TRY_SPECS=1

#[derive(PartialEq)]
struct Wide(u8);

impl thrust_models::Model for Wide {
    type Ty = Wide;
}

impl From<u8> for Wide {
    fn from(e: u8) -> Wide {
        assert!(e < 100);
        Wide(e)
    }
}

#[thrust_macros::context]
impl IntoSpec<Wide> for u8 {
    #[thrust_macros::predicate]
    fn converts(self) -> bool {
        self < 100
    }

    #[thrust_macros::predicate]
    fn converts_to(self, out: Wide) -> bool {
        out.0 == self
    }
}

fn inc(r: Result<i32, u8>) -> Result<i32, Wide> {
    let x = r?;
    Ok(x + 1)
}

fn main() {
    assert!(matches!(inc(Err(200)), Err(Wide(200))));
}
