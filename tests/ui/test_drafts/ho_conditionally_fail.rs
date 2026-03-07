//@check-pass

trait Validator {
    #[thrust::ensures((result == true && Self::is_valid(self, x)) || (result == false && !Self::is_valid(self, x)))]
    fn validate(self, x: i64) -> bool;

    #[thrust::predicate]
    fn is_valid(self, x: i64) -> bool;
}

struct RangeValidator {
    min: i64,
    max: i64,
}

impl Validator for RangeValidator {
    fn validate(self, x: i64) -> bool {
        self.min <= x && x <= self.max
    }

    #[thrust::predicate]
    fn is_valid(self, x: i64) -> bool {
        // self.min <= x && x <= self.max
        "(and
            (<= (tuple_proj<Int-Int>.0 self) x)
            (<= x (tuple_proj<Int-Int>.1 self))
        )"; true
    }
}

struct AlwaysValidValidator {
    dummy: i64
}

impl Validator for AlwaysValidValidator {
    fn validate(self, x: i64) -> bool {
        true
    }

    #[thrust::predicate]
    fn is_valid(self, x: i64) -> bool {
        "true"; true
    }
}

// #[thrust::ensures((v.is_valid(x) && result == secret) || (!v.is_valid(x) && result == dummy))]
// fn get_secret_if_valid<V: Validator>(v: &V, x: i64, secret: i64, dummy: i64) -> i64 {
//     // correct implementation:
//     // if v.validate(x) {
//     //     secret
//     // } else {
//     //     dummy
//     // }

//     // incorrect implementation:
//     secret
// }


#[thrust::ensures((RangeValidator_is_valid(v, x) && (result == secret)) || (!RangeValidator_is_valid(v, x) && (result == dummy)))]
fn range_get_secret_if_valid(v: &RangeValidator, x: i64, secret: i64, dummy: i64) -> i64 {
    secret
}

#[thrust::ensures((AlwaysValidValidator_is_valid(v, x) && (result == secret)) || (!AlwaysValidValidator_is_valid(v, x) && (result == dummy)))]
fn always_valid_get_secret_if_valid(v: &AlwaysValidValidator, x: i64, secret: i64, dummy: i64) -> i64 {
    secret
}

fn main() {
    let input_num = 150;
    let secret = 42;
    let dummy = -1;

    // let range_validator = RangeValidator { min: 0, max: 100 };
    // let r1 = range_get_secret_if_valid(&range_validator, input_num, secret, dummy);
    // assert!(r1 == dummy);

    let always_valid_validator = AlwaysValidValidator { dummy: -1 };
    let r2 = always_valid_get_secret_if_valid(&always_valid_validator, input_num, secret, dummy);
    // assert!(r2 == secret);
}
