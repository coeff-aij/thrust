//! The specs in `std.rs` and in the case study of std's integer functions agree with std.
//!
//! These std bodies are compiler intrinsics (`add_with_overflow`, `ctpop`, `cttz`, ...), which
//! Thrust cannot check as transcriptions (`tests/ui/pass/std_specs/option.rs`). Each test instead
//! runs the toolchain's function and evaluates the spec's formula, written here in wider
//! integers, on the same arguments: every pair at 8 bits, and boundary values with a fixed
//! pseudo-random sample at the wider types. It is a test, not a proof; the spec is the text
//! of `std.rs` it names, copied as a Rust expression, and a spec weaker than std (no clause about
//! a result) is noted at its test.

/// Boundary values of a type with `bits` bits, as signed or unsigned 128-bit patterns, then a
/// pseudo-random sample, so that every test sees the same arguments.
fn samples(bits: u32, signed: bool) -> Vec<i128> {
    let (min, max) = if signed {
        (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
    } else {
        (0, (1i128 << bits.min(126)) - 1)
    };
    let mut v = vec![0, 1, 2, 3, max, max - 1, max / 2, max / 2 + 1, min, min + 1];
    if signed {
        v.extend([-1, -2]);
    }
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15 ^ u64::from(bits);
    for _ in 0..300 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let wide = (u128::from(state) << 64) | u128::from(state.rotate_left(29));
        let x = (wide >> (128 - bits)) as i128;
        v.push(if signed && x > max {
            x - (max + 1) * 2
        } else {
            x
        });
    }
    v
}

macro_rules! checked_spec_test {
    ($name:ident, $T:ident, $bits:expr, $signed:expr) => {
        #[test]
        fn $name() {
            let (min, max) = ($T::MIN as i128, $T::MAX as i128);
            let all: Vec<i128> = if $bits <= 8 {
                (min..=max).collect()
            } else {
                samples($bits, $signed)
            };
            // `None` is an exact result beyond 128 bits, which no type of at most 64 bits holds.
            let in_range = |v: Option<i128>| v.is_some_and(|v| min <= v && v <= max);
            let spec = |r: Option<$T>, exact: Option<i128>| match r {
                Some(v) => in_range(exact) && Some(v as i128) == exact,
                None => !in_range(exact),
            };
            for &x in &all {
                for &y in &all {
                    let (a, b) = (x as $T, y as $T);
                    assert!(spec(a.checked_add(b), x.checked_add(y)), "{} + {}", a, b);
                    assert!(spec(a.checked_sub(b), x.checked_sub(y)), "{} - {}", a, b);
                    assert!(spec(a.checked_mul(b), x.checked_mul(y)), "{} * {}", a, b);
                }
            }
        }
    };
}

// The unsigned specs state the same as the signed ones, written without the lower bound; the
// exact result is in 128 bits for every type of at most 64 bits.
checked_spec_test!(checked_u8, u8, 8, false);
checked_spec_test!(checked_u16, u16, 16, false);
checked_spec_test!(checked_u32, u32, 32, false);
checked_spec_test!(checked_u64, u64, 64, false);
checked_spec_test!(checked_usize, usize, 64, false);
checked_spec_test!(checked_i8, i8, 8, true);
checked_spec_test!(checked_i16, i16, 16, true);
checked_spec_test!(checked_i32, i32, 32, true);
checked_spec_test!(checked_i64, i64, 64, true);
checked_spec_test!(checked_isize, isize, 64, true);

fn u64_samples() -> Vec<u64> {
    let mut v: Vec<u64> = samples(64, false).into_iter().map(|x| x as u64).collect();
    v.extend(samples(64, true).into_iter().map(|x| x as u64));
    v.extend((0..64).map(|i| 1u64 << i));
    v.extend((0..64).map(|i| u64::MAX << i));
    v
}

/// `trailing_zeros` (std.rs): the result is at most 64, it is 64 exactly for 0, and otherwise
/// shifting the argument left by `63 - result` leaves bit 63 alone set.
#[test]
fn u64_trailing_zeros() {
    for x in u64_samples() {
        let result = x.trailing_zeros();
        assert!(result <= 64);
        assert_eq!(result == 64, x == 0);
        if result != 64 {
            assert_eq!(x << (63 - result), 1u64 << 63, "{x:#x}");
        }
    }
}

/// `count_ones` (std.rs) states only `result <= 64`, which is weaker than std.
#[test]
fn u64_count_ones() {
    for x in u64_samples() {
        assert!(x.count_ones() <= 64);
    }
}

/// The wrapping specs of `tests/rustc_coroutine/thrust/std_specs.rs`: the sum or difference
/// modulo 2^w, written without wrapping arithmetic.
macro_rules! wrapping_spec_test {
    ($name:ident, $T:ident, $bits:expr, add) => {
        #[test]
        fn $name() {
            for &x in &samples_unsigned::<$T>($bits) {
                for &y in &samples_unsigned::<$T>($bits) {
                    let exact = if x > $T::MAX - y {
                        x - ($T::MAX - y) - 1
                    } else {
                        x + y
                    };
                    assert_eq!(x.wrapping_add(y), exact, "{x} + {y}");
                }
            }
        }
    };
    ($name:ident, $T:ident, $bits:expr, sub) => {
        #[test]
        fn $name() {
            for &x in &samples_unsigned::<$T>($bits) {
                for &y in &samples_unsigned::<$T>($bits) {
                    let exact = if x >= y { x - y } else { $T::MAX - (y - x) + 1 };
                    assert_eq!(x.wrapping_sub(y), exact, "{x} - {y}");
                }
            }
        }
    };
}

fn samples_unsigned<T: TryFrom<u128> + Copy>(bits: u32) -> Vec<T> {
    let mut v: Vec<u128> = samples(bits.min(64), false)
        .into_iter()
        .map(|x| x as u128)
        .collect();
    if bits == 128 {
        v.extend([
            u128::MAX,
            u128::MAX - 1,
            u128::MAX / 2,
            u128::MAX / 2 + 1,
            1 << 64,
            (1 << 64) - 1,
        ]);
        v.extend(
            samples(64, false)
                .into_iter()
                .map(|x| (x as u128) << 64 | 0xFFFF),
        );
    }
    v.into_iter().filter_map(|x| T::try_from(x).ok()).collect()
}

wrapping_spec_test!(wrapping_add_u128, u128, 128, add);
wrapping_spec_test!(wrapping_sub_u128, u128, 128, sub);
wrapping_spec_test!(wrapping_add_u64, u64, 64, add);
wrapping_spec_test!(wrapping_add_usize, usize, 64, add);

/// A value of any integer type as a sign and a magnitude, so that types of both signs compare.
fn wide<T: TryInto<i128> + TryInto<u128> + Copy>(v: T) -> (bool, u128) {
    match TryInto::<i128>::try_into(v) {
        Ok(x) if x < 0 => (true, x.unsigned_abs()),
        _ => (false, TryInto::<u128>::try_into(v).ok().unwrap()),
    }
}

fn at_most(a: (bool, u128), b: (bool, u128)) -> bool {
    match (a.0, b.0) {
        (true, false) => true,
        (false, true) => false,
        (false, false) => a.1 <= b.1,
        (true, true) => a.1 >= b.1,
    }
}

/// `TryInto::try_into` (std.rs, `TryIntoSpec`): `Ok` with an equal value exactly when the value
/// lies between the target's `MIN` and `MAX`, `Err` otherwise.
macro_rules! try_into_spec_test {
    ($name:ident, $from:ident => $($to:ident),*) => {
        #[test]
        fn $name() {
            let mut values: Vec<$from> = samples(<$from>::BITS.min(126), <$from>::MIN != 0)
                .into_iter()
                .map(|x| x as $from)
                .collect();
            values.extend([<$from>::MIN, <$from>::MAX]);
            for &v in &values {
                $(
                    let fits = at_most(wide($to::MIN), wide(v)) && at_most(wide(v), wide($to::MAX));
                    match TryInto::<$to>::try_into(v) {
                        Ok(out) => assert!(fits && wide(out) == wide(v), "{v} -> {}", stringify!($to)),
                        Err(_) => assert!(!fits, "{v} -> {}", stringify!($to)),
                    }
                )*
            }
        }
    };
}

macro_rules! try_into_spec_tests {
    ($($name:ident: $from:ident),*) => {
        $(try_into_spec_test!(
            $name, $from => isize, i8, i16, i32, i64, i128, usize, u8, u16, u32, u64, u128
        );)*
    };
}

try_into_spec_tests!(
    try_into_isize: isize, try_into_i8: i8, try_into_i16: i16, try_into_i32: i32,
    try_into_i64: i64, try_into_i128: i128, try_into_usize: usize, try_into_u8: u8,
    try_into_u16: u16, try_into_u32: u32, try_into_u64: u64, try_into_u128: u128
);
