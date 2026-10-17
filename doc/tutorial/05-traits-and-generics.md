# 5. Traits and generics

A trait can carry contracts on its methods and declare predicates and logic functions that each
implementation defines. A generic function is then verified once, against the trait's contracts,
for every implementation. Items that use these annotations take `#[thrust_macros::context]`.

## A contract on a trait method

[examples/05_double.rs](examples/05_double.rs) (z3):

```rust
#[derive(PartialEq)]
struct Meter {
    m: i64,
}

impl thrust_models::Model for Meter {
    type Ty = Self;
}

#[thrust_macros::context]
trait Double {
    #[thrust_macros::predicate]
    fn is_double(self, doubled: Self) -> bool;

    #[thrust_macros::ensures(Self::is_double(*self, !self))]
    fn double(&mut self);
}

#[thrust_macros::context]
impl Double for Meter {
    #[thrust_macros::predicate]
    fn is_double(self, doubled: Self) -> bool {
        self.m * 2 == doubled.m
    }

    fn double(&mut self) {
        self.m += self.m;
    }
}

fn main() {
    let mut a = Meter { m: 3 };
    a.double();
    assert!(a.m == 6);
}
```

```console
$ thrust 05_double.rs; echo "exit $?"
exit 0
```

- A `#[thrust_macros::predicate]` is a Boolean function used only in specifications. The trait
  declares it; each impl defines it in Rust syntax.
- The trait's `ensures` applies to every impl: `<Meter as Double>::double` is checked against it
  with `is_double` replaced by Meter's definition, and `main`'s call uses it.
- `Model` says what a value of the type is in a specification (here the struct itself). Structs
  used in specifications need a `Model` impl.

Breaking the impl (`self.m += 2`) is [scenario 9](scenarios.md).

## Logic functions, laws and a generic function

[examples/05_counter.rs](examples/05_counter.rs) (PCSat):

```rust
use thrust_models::model::UInt;
use thrust_models::Model;

#[thrust_macros::context]
trait Counter: Model {
    #[thrust_macros::logic]
    fn count(self) -> UInt;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::count(*c) >= 0)]
    fn count_nonneg(c: &Self);

    #[thrust_macros::ensures(Self::count(!self) == Self::count(*self) + 1)]
    fn tick(&mut self);
}

#[thrust_macros::context]
#[thrust_macros::ensures(C::count(!c) == C::count(*c) + 2)]
#[thrust_macros::ensures(C::count(!c) >= 2)]
fn tick_twice<C: Counter>(c: &mut C) {
    c.tick();
    c.tick();
}

struct Clicks {
    n: u64,
}

impl Model for Clicks {
    type Ty = (UInt,);
}

#[thrust_macros::context]
impl Counter for Clicks {
    #[thrust_macros::logic]
    fn count(self) -> UInt {
        self.0
    }

    fn count_nonneg(c: &Clicks) {}

    fn tick(&mut self) {
        self.n += 1;
    }
}
```

```console
$ export THRUST_SOLVER=$THRUST/tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
$ thrust 05_counter.rs; echo "exit $?"
warning: unused variable: `c`
...
warning: associated function `count_nonneg` is never used
...
warning: 2 warnings emitted

exit 0
```

rustc warns about the law's unused parameter and that nothing calls the law: a law is used by the
verifier only.

- A `#[thrust_macros::logic]` function returns any model value, here the count. Its body is one
  expression over the model: `Clicks`'s model is the tuple `(UInt,)`, so the field is `self.0`.
- `tick_twice` is verified once, over every `C: Counter`. There `C::count` is an unknown function
  of which only the trait's contracts and laws are known.
- A `#[thrust_macros::law]` states a fact about every implementation. Each impl proves it (here
  with an empty body), and generic code may use it. Without the law, `count(!c) >= 2` does not
  follow from `count(!c) == count(*c) + 2`, and
  [examples/05_counter_no_law.rs](examples/05_counter_no_law.rs) fails:

  ```console
  $ thrust 05_counter_no_law.rs
  error: verification error: Unsat
  ```

- A law the impl cannot prove fails at the impl. With `count` returning `Int` over a model
  `(Int,)` ([examples/05_counter_int_model.rs](examples/05_counter_int_model.rs)), nothing makes
  the count non-negative; `THRUST_SPLIT` (chapter 8) names the part that fails:

  ```console
  $ THRUST_SPLIT=4 thrust 05_counter_int_model.rs
  ...
  error: verification error: Unsat
    --> 05_counter_int_model.rs:40:5
     |
  40 |     fn count_nonneg(c: &Clicks) {}
     |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
     |
     = note: in part 1 of 4, of 2 clauses from `<Clicks as Counter>::count_nonneg` (05_counter_int_model.rs:40)

  note: thrust: 4 parts solved on their own, 0 of them from earlier runs
  ```

z3 cannot read the query of a generic function over a trait's logic function:

```console
$ unset THRUST_SOLVER; thrust 05_counter.rs
...
error: verification error: Error { stdout: "unsupported\n(error \"line 23 column 19: invalid datatype declaration, unknown sort 'a0'\")\n ...
```

## More

- Lemmas (`#[thrust_macros::lemma]`, used with `proof!`), recursive logic functions with
  `#[thrust_macros::variant]`, and ghost values (`ghost!`, `Ghost<T>`): [Annotation](../../README.md#annotation).
- An impl method with a contract of its own, which must refine the trait's: the paragraph on
  trait impls in [Loop invariants](../../README.md#loop-invariants).
- `pre!`/`post!` for closures and trait methods at a type parameter: the same section.
- `THRUST_PER_INSTANCE_GENERICS=1` analyzes a generic body at each instance instead, as upstream
  Thrust does ([Configuration](../../README.md#configuration)).
