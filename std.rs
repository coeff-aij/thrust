// This file is injected to source code by Thrust

mod thrust_models {
    pub trait Model {
        #[thrust::def::model_ty]
        type Ty;
    }

    /// `==` on the type is equality of its models: the type holds no `&mut` (whose model also has
    /// the final value, which `==` does not read), float, raw or function pointer, or `Ghost` (which
    /// has no `PartialEq`, so `==` on a type holding one leaves it out).
    /// Thrust decides it from the type's structure (`analyze::model_eq`); the specs that state
    /// `PartialEq` as model equality are bounded by it, and so is a derived `eq`.
    #[thrust::def::model_eq]
    pub trait ModelEq {}

    pub mod model {
        use std::marker::PhantomData;

        /// Models denoting a mathematical integer.
        ///
        /// Arithmetic and comparison mix these freely: the model of an unsigned integer
        /// denotes the same mathematical integers as [`Int`], only non-negative ones.
        pub trait Integer {}

        impl Integer for Int {}
        impl Integer for UInt {}

        /// Models usable as an index into `Array<I, _>`.
        pub trait IndexModel<I: ?Sized> {}

        impl<I: ?Sized> IndexModel<I> for I {}
        impl IndexModel<Int> for UInt {}
        impl IndexModel<UInt> for Int {}

        macro_rules! integer_model_ops {
            ($M:ty) => {
                impl<T> PartialEq<T> for $M where T: super::Model, T::Ty: Integer {
                    #[thrust::ignored]
                    fn eq(&self, _other: &T) -> bool {
                        unimplemented!()
                    }
                }

                impl<T> PartialOrd<T> for $M where T: super::Model, T::Ty: Integer {
                    #[thrust::ignored]
                    fn partial_cmp(&self, _other: &T) -> Option<std::cmp::Ordering> {
                        unimplemented!()
                    }
                }

                impl<T> std::ops::Add<T> for $M where T: super::Model, T::Ty: Integer {
                    type Output = Self;

                    #[thrust::ignored]
                    fn add(self, _rhs: T) -> Self::Output {
                        unimplemented!()
                    }
                }

                impl<T> std::ops::Sub<T> for $M where T: super::Model, T::Ty: Integer {
                    type Output = Self;

                    #[thrust::ignored]
                    fn sub(self, _rhs: T) -> Self::Output {
                        unimplemented!()
                    }
                }

                impl<T> std::ops::Mul<T> for $M where T: super::Model, T::Ty: Integer {
                    type Output = Self;

                    #[thrust::ignored]
                    fn mul(self, _rhs: T) -> Self::Output {
                        unimplemented!()
                    }
                }

                impl<T> std::ops::Div<T> for $M where T: super::Model, T::Ty: Integer {
                    type Output = Self;

                    #[thrust::ignored]
                    fn div(self, _rhs: T) -> Self::Output {
                        unimplemented!()
                    }
                }

                impl<T> std::ops::Rem<T> for $M where T: super::Model, T::Ty: Integer {
                    type Output = Self;

                    #[thrust::ignored]
                    fn rem(self, _rhs: T) -> Self::Output {
                        unimplemented!()
                    }
                }

                impl std::ops::Neg for $M {
                    type Output = Int;

                    #[thrust::ignored]
                    fn neg(self) -> Self::Output {
                        unimplemented!()
                    }
                }
            };
        }

        #[thrust::def::int_model]
        pub struct Int;

        #[thrust::def::uint_model]
        pub struct UInt;

        integer_model_ops!(Int);
        integer_model_ops!(UInt);

        /// The model of an unsigned integer of `BITS` bits: the same mathematical integers as
        /// [`UInt`], below `2^BITS`. With `THRUST_INT_RANGE` set (`cfg(thrust_int_range)`), it is
        /// the model of each `BITS`-bit unsigned type, so the model of `Vec<u64>` is
        /// `Seq<UIntN<64>>`; Thrust then assumes the bound of every such value (each element of
        /// such a sequence) and checks it where a value of another type enters. Unset, those
        /// models are [`UInt`]. Arithmetic on it is unbounded, as on [`UInt`]: a
        /// term of a specification is not assumed in range, only a value is.
        #[thrust::def::uint_n_model]
        pub struct UIntN<const BITS: usize>;

        impl UInt {
            /// The same integer as a model of `BITS` bits, where a specification passes a
            /// [`UInt`] (such as a `Seq::len`) to a parameter of a model of a Rust unsigned type.
            /// A term is not assumed in the range of its type, so this states nothing.
            #[allow(dead_code)]
            #[thrust::def::uint_to_uint_n]
            #[thrust::ignored]
            pub fn to_uint_n<const BITS: usize>(self) -> UIntN<BITS> {
                unimplemented!()
            }
        }

        impl<const BITS: usize> UIntN<BITS> {
            /// The same integer as a [`UInt`].
            #[allow(dead_code)]
            #[thrust::def::uint_n_to_uint]
            #[thrust::ignored]
            pub fn to_uint(self) -> UInt {
                unimplemented!()
            }
        }

        impl<const BITS: usize> Integer for UIntN<BITS> {}
        impl<const BITS: usize> IndexModel<Int> for UIntN<BITS> {}
        impl<const BITS: usize> IndexModel<UInt> for UIntN<BITS> {}

        /// The model of a signed integer of `BITS` bits: the same mathematical integers as
        /// [`Int`], in `[-2^(BITS-1), 2^(BITS-1))`. With `THRUST_INT_RANGE` set
        /// (`cfg(thrust_int_range)`), it is the model of each `BITS`-bit signed type, as
        /// [`UIntN`] is of the unsigned ones; unset, those models are [`Int`].
        #[thrust::def::int_n_model]
        pub struct IntN<const BITS: usize>;

        impl Int {
            /// The same integer as a model of `BITS` bits, as [`UInt::to_uint_n`].
            #[allow(dead_code)]
            #[thrust::def::int_to_int_n]
            #[thrust::ignored]
            pub fn to_int_n<const BITS: usize>(self) -> IntN<BITS> {
                unimplemented!()
            }
        }

        impl<const BITS: usize> IntN<BITS> {
            /// The same integer as an [`Int`].
            #[allow(dead_code)]
            #[thrust::def::int_n_to_int]
            #[thrust::ignored]
            pub fn to_int(self) -> Int {
                unimplemented!()
            }
        }

        impl<const BITS: usize> Integer for IntN<BITS> {}
        impl<const BITS: usize> IndexModel<Int> for IntN<BITS> {}
        impl<const BITS: usize> IndexModel<UInt> for IntN<BITS> {}

        impl<const BITS: usize> std::ops::Neg for IntN<BITS> {
            type Output = Self;

            #[thrust::ignored]
            fn neg(self) -> Self::Output {
                unimplemented!()
            }
        }

        // Arithmetic and comparison of a model with a width, against any integer model, as
        // `integer_model_ops!` for `Int` and `UInt`.
        macro_rules! width_model_ops {
            ($N:ident) => {
                width_model_ops!(@op $N, Add add, Sub sub, Mul mul, Div div, Rem rem);

                impl<T, const BITS: usize> PartialEq<T> for $N<BITS>
                where
                    T: super::Model,
                    T::Ty: Integer,
                {
                    #[thrust::ignored]
                    fn eq(&self, _other: &T) -> bool {
                        unimplemented!()
                    }
                }

                impl<T, const BITS: usize> PartialOrd<T> for $N<BITS>
                where
                    T: super::Model,
                    T::Ty: Integer,
                {
                    #[thrust::ignored]
                    fn partial_cmp(&self, _other: &T) -> Option<std::cmp::Ordering> {
                        unimplemented!()
                    }
                }
            };
            (@op $N:ident, $($Op:ident $op:ident),*) => {
                $(
                    impl<T, const BITS: usize> std::ops::$Op<T> for $N<BITS>
                    where
                        T: super::Model,
                        T::Ty: Integer,
                    {
                        type Output = Self;

                        #[thrust::ignored]
                        fn $op(self, _rhs: T) -> Self::Output {
                            unimplemented!()
                        }
                    }
                )*
            };
        }

        width_model_ops!(UIntN);
        width_model_ops!(IntN);

        /// An SMT-LIB bit-vector of `WIDTH` bits. `SIGNED` selects the signed or unsigned variant
        /// of the operations that have both.
        #[thrust::def::bit_vec_model]
        pub struct BitVec<const WIDTH: usize, const SIGNED: bool>;

        impl<const WIDTH: usize, const SIGNED: bool> BitVec<WIDTH, SIGNED> {
            #[allow(dead_code)]
            #[thrust::def::bit_vec_from_int]
            #[thrust::ignored]
            pub fn from_int<U>(_n: U) -> Self where U: super::Model, U::Ty: Integer {
                unimplemented!()
            }

            #[allow(dead_code)]
            #[thrust::def::bit_vec_to_int]
            #[thrust::ignored]
            pub fn to_int(self) -> Int {
                unimplemented!()
            }
        }

        impl<const WIDTH: usize, const SIGNED: bool> PartialEq for BitVec<WIDTH, SIGNED> {
            #[thrust::ignored]
            fn eq(&self, _other: &Self) -> bool {
                unimplemented!()
            }
        }

        impl<const WIDTH: usize, const SIGNED: bool> PartialOrd for BitVec<WIDTH, SIGNED> {
            #[thrust::ignored]
            fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
                unimplemented!()
            }
        }

        macro_rules! bit_vec_binary_op {
            ($Trait:ident, $method:ident) => {
                impl<const WIDTH: usize, const SIGNED: bool> std::ops::$Trait
                    for BitVec<WIDTH, SIGNED>
                {
                    type Output = Self;

                    #[thrust::ignored]
                    fn $method(self, _rhs: Self) -> Self::Output {
                        unimplemented!()
                    }
                }
            };
        }

        bit_vec_binary_op!(Add, add);
        bit_vec_binary_op!(Sub, sub);
        bit_vec_binary_op!(Mul, mul);
        bit_vec_binary_op!(BitAnd, bitand);
        bit_vec_binary_op!(BitOr, bitor);
        bit_vec_binary_op!(BitXor, bitxor);
        bit_vec_binary_op!(Shl, shl);
        bit_vec_binary_op!(Shr, shr);

        impl<const WIDTH: usize, const SIGNED: bool> std::ops::Not for BitVec<WIDTH, SIGNED> {
            type Output = Self;

            #[thrust::ignored]
            fn not(self) -> Self::Output {
                unimplemented!()
            }
        }

        impl<const WIDTH: usize, const SIGNED: bool> std::ops::Neg for BitVec<WIDTH, SIGNED> {
            type Output = Self;

            #[thrust::ignored]
            fn neg(self) -> Self::Output {
                unimplemented!()
            }
        }

        #[thrust::def::mut_model]
        pub struct Mut<T: ?Sized>(PhantomData<T>);

        impl<T> Mut<T> {
            #[allow(dead_code)]
            #[thrust::def::mut_new]
            #[thrust::ignored]
            pub fn new(_a: T, _b: T) -> Self {
                unimplemented!()
            }
        }

        impl<T, U> PartialEq<U> for Mut<T> where U: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn eq(&self, _other: &U) -> bool {
                unimplemented!()
            }
        }

        impl<T> std::ops::Deref for Mut<T> {
            type Target = T;

            #[thrust::ignored]
            fn deref(&self) -> &Self::Target {
                unimplemented!()
            }
        }

        impl<T> std::ops::Not for Mut<T> {
            type Output = T;

            #[thrust::ignored]
            fn not(self) -> Self::Output {
                unimplemented!()
            }
        }

        #[thrust::def::box_model]
        pub struct Box<T: ?Sized>(PhantomData<T>);

        impl<T> Box<T> {
            #[allow(dead_code)]
            #[thrust::def::box_new]
            #[thrust::ignored]
            pub fn new(_x: T) -> Self {
                unimplemented!()
            }
        }

        impl<T, U> PartialEq<U> for Box<T> where U: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn eq(&self, _other: &U) -> bool {
                unimplemented!()
            }
        }

        impl<T> std::ops::Deref for Box<T> {
            type Target = T;

            #[thrust::ignored]
            fn deref(&self) -> &Self::Target {
                unimplemented!()
            }
        }

        #[thrust::def::array_model]
        pub struct Array<I: ?Sized, T: ?Sized>(PhantomData<I>, PhantomData<T>);

        impl<I, T, U> PartialEq<U> for Array<I, T> where U: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn eq(&self, _other: &U) -> bool {
                unimplemented!()
            }
        }

        impl<I, T, U> std::ops::Index<U> for Array<I, T> where U: super::Model, U::Ty: IndexModel<I> {
            type Output = T;

            #[thrust::ignored]
            fn index(&self, _index: U) -> &Self::Output {
                unimplemented!()
            }
        }

        impl<I, T> Array<I, T> {
            #[allow(dead_code)]
            #[thrust::def::array_store]
            #[thrust::ignored]
            pub fn store<U>(&self, _index: U, _value: T) -> Self
                where U: super::Model, U::Ty: IndexModel<I>
            {
                unimplemented!()
            }

            /// The array whose element at each index `i` is `f(i)` (SMT-LIB's `lambda`).
            #[allow(dead_code)]
            #[thrust::def::array_from_fn]
            #[thrust::ignored]
            pub fn from_fn<F: Fn(I) -> T>(_f: F) -> Self {
                unimplemented!()
            }
        }

        #[thrust::def::closure_model]
        pub struct Closure<T: ?Sized>(PhantomData<T>);

        impl<T: ?Sized> PartialEq for Closure<T> {
            #[thrust::ignored]
            fn eq(&self, _other: &Self) -> bool {
                unimplemented!()
            }
        }

        /// Refers to the precondition of a closure in a specification.
        ///
        /// Prefer the `thrust_macros::pre!(f(x))` surface syntax, which desugars to this; the
        /// `args` here is the tuple of logical arguments (`(x,)` for one argument, `()` for none).
        #[allow(dead_code)]
        #[thrust::def::closure_precondition]
        #[thrust::ignored]
        pub fn closure_precondition<F, Args>(_f: F, _args: Args) -> bool {
            unimplemented!()
        }

        /// Refers to the postcondition of a closure in a specification, relating the
        /// logical arguments `args` to the closure's `result`.
        ///
        /// Prefer the `thrust_macros::post!(f(x), r)` surface syntax, which desugars to this.
        #[allow(dead_code)]
        #[thrust::def::closure_postcondition]
        #[thrust::ignored]
        pub fn closure_postcondition<F, Args, R>(_f: F, _args: Args, _result: R) -> bool {
            unimplemented!()
        }

        /// Relates two states of an `FnMut` closure: Creusot's `FnMutExt::hist_inv` (formerly
        /// `hist_inv`). Reflexive, transitive, and implied by every call's postcondition between
        /// the states before and after the call; at a concrete closure, the captures taken by
        /// `&mut` keep their final values and those taken by `&` their values.
        ///
        /// Prefer the `thrust_macros::hist_inv!(f, g)` surface syntax, which desugars to this.
        #[allow(dead_code)]
        #[thrust::def::closure_hist_inv]
        #[thrust::ignored]
        pub fn closure_hist_inv<F>(_f: F, _g: F) -> bool {
            unimplemented!()
        }

        /// The integer `n` as the integer model `M`. `#[thrust_macros::logic]` writes an integer
        /// literal the function returns as this, so that it takes the model of the result type.
        #[allow(dead_code)]
        #[thrust::def::int_lit]
        #[thrust::ignored]
        pub fn int_lit<M: Integer>(_n: i128) -> M {
            unimplemented!()
        }

        #[thrust::def::seq_model]
        pub struct Seq<T: ?Sized>(PhantomData<T>);

        impl<T, U> PartialEq<U> for Seq<T> where U: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn eq(&self, _other: &U) -> bool {
                unimplemented!()
            }
        }

        impl<T, U> std::ops::Index<U> for Seq<T> where U: super::Model, U::Ty: Integer {
            type Output = T;

            #[thrust::ignored]
            fn index(&self, _index: U) -> &Self::Output {
                unimplemented!()
            }
        }

        impl<T> Seq<T> {
            #[allow(dead_code)]
            #[thrust::def::seq_empty]
            #[thrust::ignored]
            pub fn empty() -> Self {
                unimplemented!()
            }

            #[allow(dead_code)]
            #[thrust::def::seq_singleton]
            #[thrust::ignored]
            pub fn singleton(_x: T) -> Self {
                unimplemented!()
            }

            // With `THRUST_INT_RANGE` the length has the type of a `usize` model, so that it is
            // passed where a specification takes a `usize`; a term is not assumed in the range of
            // its type, so this states nothing.
            #[allow(dead_code)]
            #[cfg(not(thrust_int_range))]
            #[thrust::def::seq_len]
            #[thrust::ignored]
            pub fn len(&self) -> UInt {
                unimplemented!()
            }

            #[allow(dead_code)]
            #[cfg(thrust_int_range)]
            #[thrust::def::seq_len]
            #[thrust::ignored]
            pub fn len(&self) -> UIntN<64> {
                unimplemented!()
            }

            #[allow(dead_code)]
            #[thrust::def::seq_push]
            #[thrust::ignored]
            pub fn push(self, _x: T) -> Self {
                unimplemented!()
            }

            /// Returns `self` with the element at `index` replaced by `value`.
            ///
            /// The result is unspecified when `index` is out of range.
            #[allow(dead_code)]
            #[thrust::def::seq_store]
            #[thrust::ignored]
            pub fn store<U>(self, _index: U, _value: T) -> Self
            where
                U: super::Model, U::Ty: Integer,
            {
                unimplemented!()
            }

            #[allow(dead_code)]
            #[thrust::def::seq_subsequence]
            #[thrust::ignored]
            pub fn subsequence<U, V>(self, _start: U, _end: V) -> Self
            where
                U: super::Model, U::Ty: Integer,
                V: super::Model, V::Ty: Integer,
            {
                unimplemented!()
            }

            #[allow(dead_code)]
            #[thrust::def::seq_concat]
            #[thrust::ignored]
            pub fn concat(self, _other: Self) -> Self {
                unimplemented!()
            }
        }
    }

    impl<T: ?Sized> Model for model::Seq<T> {
        type Ty = model::Seq<T>;
    }

    impl Model for model::Int {
        type Ty = model::Int;
    }

    impl Model for model::UInt {
        type Ty = model::UInt;
    }

    impl<const BITS: usize> Model for model::UIntN<BITS> {
        type Ty = model::UIntN<BITS>;
    }

    impl<const BITS: usize> Model for model::IntN<BITS> {
        type Ty = model::IntN<BITS>;
    }

    impl<const WIDTH: usize, const SIGNED: bool> Model for model::BitVec<WIDTH, SIGNED> {
        type Ty = model::BitVec<WIDTH, SIGNED>;
    }

    macro_rules! model_arith {
        ($T:ty, $M:ty) => {
            impl PartialEq<$M> for $T {
                #[thrust::ignored]
                fn eq(&self, _other: &$M) -> bool {
                    unimplemented!()
                }
            }

            impl PartialOrd<$M> for $T {
                #[thrust::ignored]
                fn partial_cmp(&self, _other: &$M) -> Option<std::cmp::Ordering> {
                    unimplemented!()
                }
            }

            impl std::ops::Add<$M> for $T {
                type Output = $M;

                #[thrust::ignored]
                fn add(self, _rhs: $M) -> Self::Output {
                    unimplemented!()
                }
            }

            impl std::ops::Sub<$M> for $T {
                type Output = $M;

                #[thrust::ignored]
                fn sub(self, _rhs: $M) -> Self::Output {
                    unimplemented!()
                }
            }

            impl std::ops::Mul<$M> for $T {
                type Output = $M;

                #[thrust::ignored]
                fn mul(self, _rhs: $M) -> Self::Output {
                    unimplemented!()
                }
            }

            impl std::ops::Div<$M> for $T {
                type Output = $M;

                #[thrust::ignored]
                fn div(self, _rhs: $M) -> Self::Output {
                    unimplemented!()
                }
            }

            impl std::ops::Rem<$M> for $T {
                type Output = $M;

                #[thrust::ignored]
                fn rem(self, _rhs: $M) -> Self::Output {
                    unimplemented!()
                }
            }
        };
    }

    macro_rules! integer_model {
        ($T:ty, $M:ty) => {
            impl Model for $T {
                type Ty = $M;
            }

            model_arith!($T, model::Int);
            model_arith!($T, model::UInt);
            model_arith_n!($T);
        };
    }

    // `x op n` of a Rust integer `x` and an `n` of a model with a width (`UIntN`, `IntN`), as
    // `model_arith!` for `Int` and `UInt`.
    macro_rules! model_arith_n {
        (@model $T:ty, $N:ident) => {
            impl<const BITS: usize> PartialEq<model::$N<BITS>> for $T {
                #[thrust::ignored]
                fn eq(&self, _other: &model::$N<BITS>) -> bool {
                    unimplemented!()
                }
            }

            impl<const BITS: usize> PartialOrd<model::$N<BITS>> for $T {
                #[thrust::ignored]
                fn partial_cmp(&self, _other: &model::$N<BITS>) -> Option<std::cmp::Ordering> {
                    unimplemented!()
                }
            }

            model_arith_n!(@op $T, $N, Add add, Sub sub, Mul mul, Div div, Rem rem);
        };
        (@op $T:ty, $N:ident, $($Op:ident $op:ident),*) => {
            $(
                impl<const BITS: usize> std::ops::$Op<model::$N<BITS>> for $T {
                    type Output = model::$N<BITS>;

                    #[thrust::ignored]
                    fn $op(self, _rhs: model::$N<BITS>) -> Self::Output {
                        unimplemented!()
                    }
                }
            )*
        };
        ($T:ty) => {
            model_arith_n!(@model $T, UIntN);
            model_arith_n!(@model $T, IntN);
        };
    }

    #[cfg(not(thrust_int_range))]
    integer_model!(isize, model::Int);
    #[cfg(thrust_int_range)]
    integer_model!(isize, model::IntN<64>);
    #[cfg(not(thrust_int_range))]
    integer_model!(i32, model::Int);
    #[cfg(thrust_int_range)]
    integer_model!(i32, model::IntN<32>);
    #[cfg(not(thrust_int_range))]
    integer_model!(i64, model::Int);
    #[cfg(thrust_int_range)]
    integer_model!(i64, model::IntN<64>);
    #[cfg(not(thrust_int_range))]
    integer_model!(usize, model::UInt);
    #[cfg(thrust_int_range)]
    integer_model!(usize, model::UIntN<64>);
    #[cfg(not(thrust_int_range))]
    integer_model!(u32, model::UInt);
    #[cfg(thrust_int_range)]
    integer_model!(u32, model::UIntN<32>);
    #[cfg(not(thrust_int_range))]
    integer_model!(u64, model::UInt);
    #[cfg(thrust_int_range)]
    integer_model!(u64, model::UIntN<64>);
    #[cfg(not(thrust_int_range))]
    integer_model!(i8, model::Int);
    #[cfg(thrust_int_range)]
    integer_model!(i8, model::IntN<8>);
    #[cfg(not(thrust_int_range))]
    integer_model!(i16, model::Int);
    #[cfg(thrust_int_range)]
    integer_model!(i16, model::IntN<16>);
    #[cfg(not(thrust_int_range))]
    integer_model!(i128, model::Int);
    #[cfg(thrust_int_range)]
    integer_model!(i128, model::IntN<128>);
    #[cfg(not(thrust_int_range))]
    integer_model!(u8, model::UInt);
    #[cfg(thrust_int_range)]
    integer_model!(u8, model::UIntN<8>);
    #[cfg(not(thrust_int_range))]
    integer_model!(u16, model::UInt);
    #[cfg(thrust_int_range)]
    integer_model!(u16, model::UIntN<16>);
    #[cfg(not(thrust_int_range))]
    integer_model!(u128, model::UInt);
    #[cfg(thrust_int_range)]
    integer_model!(u128, model::UIntN<128>);

    impl Model for bool {
        type Ty = bool;
    }

    impl Model for std::cmp::Ordering {
        type Ty = std::cmp::Ordering;
    }

    impl<T: ?Sized> Model for model::Closure<T> {
        type Ty = model::Closure<T>;
    }

    macro_rules! impl_tuple_model {
        ($($T:ident),*) => {
            impl<$($T),*> Model for ($($T,)*) where $($T: Model),* {
                type Ty = ($(<$T as Model>::Ty,)*);
            }
        };
    }

    impl_tuple_model!();
    impl_tuple_model!(T0);
    impl_tuple_model!(T0, T1);
    impl_tuple_model!(T0, T1, T2);
    impl_tuple_model!(T0, T1, T2, T3);
    impl_tuple_model!(T0, T1, T2, T3, T4);
    impl_tuple_model!(T0, T1, T2, T3, T4, T5);
    impl_tuple_model!(T0, T1, T2, T3, T4, T5, T6);
    impl_tuple_model!(T0, T1, T2, T3, T4, T5, T6, T7);
    impl_tuple_model!(T0, T1, T2, T3, T4, T5, T6, T7, T8);
    impl_tuple_model!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9);

    impl<'a, T: ?Sized> Model for &'a mut T where T: Model {
        type Ty = model::Mut<<T as Model>::Ty>;
    }

    impl<T: ?Sized> Model for model::Mut<T> {
        type Ty = model::Mut<T>;
    }

    impl<'a, T: ?Sized> Model for &'a T where T: Model {
        type Ty = &'a <T as Model>::Ty;
    }

    impl<T: ?Sized> Model for Box<T> where T: Model {
        type Ty = model::Box<<T as Model>::Ty>;
    }

    impl<T: ?Sized> Model for model::Box<T> {
        type Ty = model::Box<T>;
    }

    impl<I: ?Sized, T: ?Sized> Model for model::Array<I, T> {
        type Ty = model::Array<I, T>;
    }

    impl<T> Model for Vec<T> where T: Model {
        type Ty = model::Seq<<T as Model>::Ty>;
    }

    impl<T> Model for [T] where T: Model {
        type Ty = model::Seq<<T as Model>::Ty>;
    }

    // NOTE: basic_block::Analyzer depends on the structure of array model
    impl<T: Model, const N: usize> Model for [T; N] {
        type Ty = model::Seq<<T as Model>::Ty>;
    }

    // An iterator over a contiguous sequence is a `(base, cursor)` pair: the sequence it was
    // made from, and the position of the element the next `next` returns. The alternative --
    // the sequence of items still to come -- would shift the whole sequence on every step, and
    // carry the universal quantifier that describes the shift into every loop invariant.
    //
    // None of the three has a field that survives translation, so, unlike `Vec` and `[T]`, they
    // are not merely better served by a model than by their fields: they cannot be traversed at
    // any element type at all. The refinement type builder knows all three by name for that
    // reason.

    impl<'a, T> Model for core::slice::Iter<'a, T> where T: Model {
        type Ty = (model::Seq<<T as Model>::Ty>, model::Int);
    }

    // The two halves of the `&mut [T]` the iterator was made from, kept apart, and the cursor.
    // The final value of every element is already fixed here; `next` hands out the element at
    // the cursor as the `Mut` pair of the two sequences at that position. They are not a `Mut`
    // themselves: the pair belongs to the caller's reference, and a `Mut` in the model of a
    // local is resolved when that local dies.
    impl<'a, T> Model for core::slice::IterMut<'a, T> where T: Model {
        type Ty = (
            model::Seq<<T as Model>::Ty>,
            model::Seq<<T as Model>::Ty>,
            model::Int,
        );
    }

    impl<T> Model for std::vec::IntoIter<T> where T: Model {
        type Ty = (model::Seq<<T as Model>::Ty>, model::Int);
    }

    // The iterator it wraps and the number of items handed out. It has the shape of the struct,
    // so the refinement type builder needs no special case.
    impl<I> Model for core::iter::Enumerate<I> where I: Model {
        #[cfg(not(thrust_int_range))]
        type Ty = (<I as Model>::Ty, model::UInt);
        #[cfg(thrust_int_range)]
        type Ty = (<I as Model>::Ty, model::UIntN<64>);
    }

    // The two iterators it wraps, in the order of the arguments to `zip`.
    impl<A, B> Model for core::iter::Zip<A, B> where A: Model, B: Model {
        type Ty = (<A as Model>::Ty, <B as Model>::Ty);
    }

    // The iterator it wraps and the number of items still to skip (`Skip`) or to hand out
    // (`Take`): the fields of the struct.
    impl<I> Model for core::iter::Skip<I> where I: Model {
        #[cfg(not(thrust_int_range))]
        type Ty = (<I as Model>::Ty, model::UInt);
        #[cfg(thrust_int_range)]
        type Ty = (<I as Model>::Ty, model::UIntN<64>);
    }

    impl<I> Model for core::iter::Take<I> where I: Model {
        #[cfg(not(thrust_int_range))]
        type Ty = (<I as Model>::Ty, model::UInt);
        #[cfg(thrust_int_range)]
        type Ty = (<I as Model>::Ty, model::UIntN<64>);
    }

    // `Cloned` and `Copied` hold only the iterator they wrap.
    impl<I> Model for core::iter::Cloned<I> where I: Model {
        type Ty = <I as Model>::Ty;
    }

    impl<I> Model for core::iter::Copied<I> where I: Model {
        type Ty = <I as Model>::Ty;
    }

    // The iterator it wraps and the closure's state.
    impl<I, F> Model for core::iter::Map<I, F> where I: Model {
        type Ty = (<I as Model>::Ty, model::Closure<F>);
    }

    // The iterator it wraps and the predicate's state.
    impl<I, P> Model for core::iter::Filter<I, P> where I: Model {
        type Ty = (<I as Model>::Ty, model::Closure<P>);
    }

    // The two iterators, the first `None` once it has completed.
    impl<A, B> Model for core::iter::Chain<A, B> where A: Model, B: Model {
        type Ty = (Option<<A as Model>::Ty>, Option<<B as Model>::Ty>);
    }

    impl<T> Model for Option<T> where T: Model {
        type Ty = Option<<T as Model>::Ty>;
    }

    impl<T, E> Model for Result<T, E> where T: Model, E: Model {
        type Ty = Result<<T as Model>::Ty, <E as Model>::Ty>;
    }

    // A datatype without constructors is not accepted by the solver, so `Infallible` is modelled
    // by a type with one value; the model may hold more values than the type does.
    impl Model for core::convert::Infallible {
        type Ty = ();
    }

    impl Model for core::num::TryFromIntError {
        type Ty = ();
    }

    impl<B, C> Model for core::ops::ControlFlow<B, C> where B: Model, C: Model {
        type Ty = core::ops::ControlFlow<<B as Model>::Ty, <C as Model>::Ty>;
    }

    impl<Idx> Model for core::ops::Range<Idx> where Idx: Model {
        type Ty = core::ops::Range<<Idx as Model>::Ty>;
    }

    impl<Idx> Model for core::ops::RangeFrom<Idx> where Idx: Model {
        type Ty = core::ops::RangeFrom<<Idx as Model>::Ty>;
    }

    impl<Idx> Model for core::ops::RangeTo<Idx> where Idx: Model {
        type Ty = core::ops::RangeTo<<Idx as Model>::Ty>;
    }

    impl<Idx> Model for core::ops::RangeToInclusive<Idx> where Idx: Model {
        type Ty = core::ops::RangeToInclusive<<Idx as Model>::Ty>;
    }

    // The fields `start`, `end` and `exhausted`, which are private to core, so a tuple rather
    // than the struct.
    impl<Idx> Model for core::ops::RangeInclusive<Idx> where Idx: Model {
        type Ty = (<Idx as Model>::Ty, <Idx as Model>::Ty, bool);
    }

    // `Rev` holds only the iterator it wraps.
    impl<I> Model for core::iter::Rev<I> where I: Model {
        type Ty = <I as Model>::Ty;
    }

    impl Model for core::ops::RangeFull {
        type Ty = core::ops::RangeFull;
    }

    #[allow(dead_code)]
    #[thrust::def::exists]
    #[thrust::ignored]
    pub fn exists<T>(_x: T) -> bool {
        unimplemented!()
    }

    #[allow(dead_code)]
    #[thrust::def::forall]
    #[thrust::ignored]
    pub fn forall<T>(_x: T) -> bool {
        unimplemented!()
    }

    #[allow(dead_code)]
    #[thrust::def::implies]
    #[thrust::ignored]
    pub fn implies(_lhs: bool, _rhs: bool) -> bool {
        unimplemented!()
    }

    /// The operands of logical equality, which `==` and `!=` mean in a specification:
    /// `thrust_macros::formula!` writes `a == b` as `log_eq_args(&a, &b).log_eq()`, which holds
    /// when the models of `a` and `b` are equal, and `a != b` as `.log_ne()`. Unlike `==` it needs
    /// no `PartialEq`. Operands whose types [`LogEq`] relates take [`LogEqArgs::log_eq`]; others of
    /// one type reach [`LogEqSameArgs::log_eq`] through `Deref`. Method resolution tries them in
    /// this order and takes the first whose bound may hold, so that the type of an operand still
    /// to be inferred (`2 * s`, `Seq::empty()`) is settled by `LogEq` rather than by equating it
    /// with the other's.
    #[allow(dead_code)]
    #[thrust::def::log_eq_args]
    #[thrust::ignored]
    pub fn log_eq_args<'a, T: ?Sized, U: ?Sized>(_lhs: &'a T, _rhs: &'a U) -> LogEqArgs<'a, T, U> {
        unimplemented!()
    }

    #[doc(hidden)]
    #[allow(dead_code)]
    pub struct LogEqArgs<'a, T: ?Sized, U: ?Sized>(LogEqSameArgs<'a, T, U>);

    #[doc(hidden)]
    #[allow(dead_code)]
    pub struct LogEqSameArgs<'a, T: ?Sized, U: ?Sized>(&'a T, &'a U);

    impl<'a, T: ?Sized, U: ?Sized> LogEqArgs<'a, T, U> where T: LogEq<U> {
        #[allow(dead_code)]
        #[thrust::ignored]
        pub fn log_eq(self) -> bool {
            unimplemented!()
        }

        #[allow(dead_code)]
        #[thrust::ignored]
        pub fn log_ne(self) -> bool {
            unimplemented!()
        }
    }

    impl<'a, T: ?Sized, U: ?Sized> std::ops::Deref for LogEqArgs<'a, T, U> {
        type Target = LogEqSameArgs<'a, T, U>;

        #[thrust::ignored]
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl<'a, T: ?Sized> LogEqSameArgs<'a, T, T> {
        #[allow(dead_code)]
        #[thrust::ignored]
        pub fn log_eq(&self) -> bool {
            unimplemented!()
        }

        #[allow(dead_code)]
        #[thrust::ignored]
        pub fn log_ne(&self) -> bool {
            unimplemented!()
        }
    }

    /// The pairs of operand types [`log_eq_args`] compares besides a type with itself, those the
    /// model types' `PartialEq` impls admit: two integers, a model with a type whose model it is,
    /// and a `Ghost` with a type whose model is its content. A marker trait, so that the impls may
    /// overlap. It has no impl for a type with itself, which would make a comparison with
    /// `Seq::empty()` ambiguous between that impl and `Seq`'s.
    #[marker]
    pub trait LogEq<Rhs: ?Sized> {}

    impl<T: ?Sized, U: ?Sized> LogEq<U> for T
    where
        T: Model,
        U: Model,
        T::Ty: model::Integer,
        U::Ty: model::Integer,
    {
    }

    impl<T: ?Sized, U: ?Sized> LogEq<U> for model::Seq<T> where U: Model<Ty = Self> {}
    impl<T: ?Sized, U: ?Sized> LogEq<U> for model::Mut<T> where U: Model<Ty = Self> {}
    impl<T: ?Sized, U: ?Sized> LogEq<U> for model::Box<T> where U: Model<Ty = Self> {}
    impl<I: ?Sized, T: ?Sized, U: ?Sized> LogEq<U> for model::Array<I, T> where U: Model<Ty = Self> {}
    impl<T: ?Sized, U: ?Sized> LogEq<U> for Ghost<T> where T: Model, U: Model<Ty = <T as Model>::Ty> {}

    #[thrust::def::invariant_marker]
    #[thrust::ignored]
    #[inline(never)]
    pub fn __invariant_marker<F>(_f: F) {
        unimplemented!()
    }

    #[thrust::def::partial_invariant_marker]
    #[thrust::ignored]
    #[inline(never)]
    pub fn __partial_invariant_marker<F>(_f: F) {
        unimplemented!()
    }

    /// Proof-only data, introduced by `thrust_macros::ghost!`. In the logic it is its
    /// content, so a specification refers to a `Ghost<T>` as if it were a `T`.
    #[allow(dead_code)]
    #[thrust::def::ghost_model]
    pub struct Ghost<T: ?Sized>(std::marker::PhantomData<T>);

    impl<T: ?Sized> Clone for Ghost<T> {
        #[thrust::ignored]
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<T: ?Sized> Copy for Ghost<T> {}

    // Proof-only data hashes to nothing, so that a struct with a ghost field keeps its derives.
    impl<T: ?Sized> std::hash::Hash for Ghost<T> {
        #[thrust::ignored]
        fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
    }

    // TODO: keep this in step with the `ghost_model` arm of `model_adt` in
    // `refine::template`, which resolves a `Ghost<T>` to its content as well.
    //
    // The other `#[thrust::def::*_model]` types are fixed points of `Model` and leave the
    // meaning to `model_adt` alone. This one cannot be: a specification names a ghost value
    // as its content (`s.len()` on a `Ghost<Seq<Int>>`), so the lifted formula function has
    // to receive `<T as Model>::Ty` for the term to type-check.
    impl<T: ?Sized> Model for Ghost<T> where T: Model {
        type Ty = <T as Model>::Ty;
    }

    // A lifted formula function receives a `Ghost<T>` parameter as `<T as Model>::Ty`
    // already, but a `Ghost<T>` field of a struct whose model is the struct itself keeps its
    // surface type. This impl lets a formula use such a field as its content too, for method
    // calls and `*g`; in the logic it is the identity on the content, as the `ghost_model` arm
    // of `model_adt` has it. `Ghost` has no `PartialEq`: a formula's `==` is `log_eq`.
    impl<T: ?Sized> std::ops::Deref for Ghost<T> where T: Model {
        type Target = <T as Model>::Ty;

        #[thrust::ignored]
        fn deref(&self) -> &Self::Target {
            unimplemented!()
        }
    }

    #[doc(hidden)]
    #[thrust::def::ghost_marker]
    #[thrust::ignored]
    #[inline(never)]
    pub fn __ghost_marker<F, T: ?Sized>(_f: F) -> Ghost<T> {
        Ghost(std::marker::PhantomData)
    }

    /// Taken in the analysis and not at run time: the branch in which `proof!` calls a lemma.
    #[doc(hidden)]
    #[thrust::def::proof_branch]
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == true)]
    #[inline(never)]
    pub fn __proof_branch() -> bool {
        false
    }

    #[allow(dead_code)]
    #[thrust::def::fn_param_wrapper]
    pub struct FnParam<T>(std::marker::PhantomData<T>);

    impl<T> Model for FnParam<T> where T: Model {
        type Ty = FnParam<<T as Model>::Ty>;
    }

    impl<T> FnParam<T> {
        #[allow(dead_code)]
        #[thrust::def::fn_param_at_entry]
        #[thrust::ignored]
        pub fn at_entry(self) -> T {
            unimplemented!()
        }
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == thrust_models::model::Box::new(x))]
fn _extern_spec_box_new<T>(x: T) -> Box<T> where T: thrust_models::Model {
    Box::new(x)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (x == y))]
fn _extern_spec_box_partialeq_eq<T>(x: &Box<T>, y: &Box<T>) -> bool
  where T: thrust_models::Model + thrust_models::ModelEq + PartialEq
{
    <Box<T> as PartialEq>::eq(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*x == !y && *y == !x)]
fn _extern_spec_std_mem_swap<T>(x: &mut T, y: &mut T) where T: thrust_models::Model {
    std::mem::swap(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!dest == src && result == *dest)]
fn _extern_spec_std_mem_replace<T>(dest: &mut T, src: T) -> T where T: thrust_models::Model {
    std::mem::replace(dest, src)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (x == y))]
fn _extern_spec_option_partialeq_eq<T>(x: &Option<T>, y: &Option<T>) -> bool
  where T: thrust_models::Model + thrust_models::ModelEq + PartialEq
{
    <Option<T> as PartialEq>::eq(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(opt != None)]
#[thrust_macros::ensures(Some(result) == opt)]
fn _extern_spec_option_unwrap<T>(opt: Option<T>) -> T where T: thrust_models::Model {
    Option::unwrap(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*opt == None && result == true)
    || (*opt != None && result == false)
)]
fn _extern_spec_option_is_none<T>(opt: &Option<T>) -> bool where T: thrust_models::Model {
    Option::is_none(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*opt == None && result == false)
    || (*opt != None && result == true)
)]
fn _extern_spec_option_is_some<T>(opt: &Option<T>) -> bool where T: thrust_models::Model {
    Option::is_some(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (opt != None && Some(result) == opt)
    || (opt == None && result == default)
)]
fn _extern_spec_option_unwrap_or<T>(opt: Option<T>, default: T) -> T where T: thrust_models::Model {
    Option::unwrap_or(opt, default)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(
    opt == None || thrust_models::exists(|i| opt == Some(i) && thrust_macros::pre!(f(i)))
)]
#[thrust_macros::ensures(
    (opt == None && result == None)
    || thrust_models::exists(|i| thrust_models::exists(|j|
        opt == Some(i) && thrust_macros::post!(f(i), j) && result == Some(j)))
)]
fn _extern_spec_option_map<T, U, F>(opt: Option<T>, f: F) -> Option<U>
where
    T: thrust_models::Model,
    U: thrust_models::Model,
    F: FnOnce(T) -> U,
{
    Option::map(opt, f)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(
    opt == None || thrust_models::exists(|i| opt == Some(i) && thrust_macros::pre!(f(i)))
)]
#[thrust_macros::ensures(
    (opt == None && result == default)
    || thrust_models::exists(|i| opt == Some(i) && thrust_macros::post!(f(i), result))
)]
fn _extern_spec_option_map_or<T, U, F>(opt: Option<T>, default: U, f: F) -> U
where
    T: thrust_models::Model,
    U: thrust_models::Model,
    F: FnOnce(T) -> U,
{
    Option::map_or(opt, default, f)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(opt != None || thrust_macros::pre!(f()))]
#[thrust_macros::ensures(
    (opt != None && Some(result) == opt)
    || (opt == None && thrust_macros::post!(f(), result))
)]
fn _extern_spec_option_unwrap_or_else<T, F>(opt: Option<T>, f: F) -> T
where
    T: thrust_models::Model,
    F: FnOnce() -> T,
{
    Option::unwrap_or_else(opt, f)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (thrust_models::exists(|x| opt == Some(x) && result == Ok(x)))
    || (opt == None && result == Err(err))
)]
fn _extern_spec_option_ok_or<T, E>(opt: Option<T>, err: E) -> Result<T, E>
    where T: thrust_models::Model,
          E: thrust_models::Model,
{
    Option::ok_or(opt, err)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!opt == None && result == *opt)]
fn _extern_spec_option_take<T>(opt: &mut Option<T>) -> Option<T> where T: thrust_models::Model {
    Option::take(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!opt == Some(src) && result == *opt)]
fn _extern_spec_option_replace<T>(opt: &mut Option<T>, src: T) -> Option<T>
    where T: thrust_models::Model
{
    Option::replace(opt, src)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x| opt == &Some(x) && result == Some(&x))
    || (opt == &None && result == None)
)]
fn _extern_spec_option_as_ref<T>(opt: &Option<T>) -> Option<&T> where T: thrust_models::Model {
    Option::as_ref(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x1, x2|
      *opt == Some(x1) &&
      !opt == Some(x2) &&
      result == Some(thrust_models::model::Mut::new(x1, x2))
    )
    || (
      *opt == None &&
      !opt == None &&
      result == None
    )
)]
fn _extern_spec_option_as_mut<T>(opt: &mut Option<T>) -> Option<&mut T>
  where T: thrust_models::Model
{
    Option::as_mut(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == value)]
fn _extern_spec_from_identity<T>(value: T) -> T
    where T: thrust_models::Model,
{
    <T as From<T>>::from(value)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (x == y))]
fn _extern_spec_result_partialeq_eq<T, E>(x: &Result<T, E>, y: &Result<T, E>) -> bool
  where T: thrust_models::Model + thrust_models::ModelEq + PartialEq,
        E: thrust_models::Model + thrust_models::ModelEq + PartialEq,
{
    <Result<T, E> as PartialEq>::eq(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(thrust_models::exists(|x| res == Ok(x)))]
#[thrust_macros::ensures(Ok(result) == res)]
fn _extern_spec_result_unwrap<T, E: std::fmt::Debug>(res: Result<T, E>) -> T
  where T: thrust_models::Model,
        E: thrust_models::Model,
{
    Result::unwrap(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(thrust_models::exists(|x| res == Err(x)))]
#[thrust_macros::ensures(Err(result) == res)]
fn _extern_spec_result_unwrap_err<T: std::fmt::Debug, E>(res: Result<T, E>) -> E
  where T: thrust_models::Model,
        E: thrust_models::Model,
{
    Result::unwrap_err(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x| res == Ok(x) && result == Some(x))
    || thrust_models::exists(|x| res == Err(x) && result == None)
)]
fn _extern_spec_result_ok<T, E>(res: Result<T, E>) -> Option<T>
  where T: thrust_models::Model,
        E: thrust_models::Model,
{
    Result::ok(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x| res == Ok(x) && result == None)
    || thrust_models::exists(|x| res == Err(x) && result == Some(x))
)]
fn _extern_spec_result_err<T, E>(res: Result<T, E>) -> Option<E>
  where T: thrust_models::Model,
        E: thrust_models::Model,
{
    Result::err(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x| *res == Ok(x) && result == true)
    || thrust_models::exists(|x| *res == Err(x) && result == false)
)]
fn _extern_spec_result_is_ok<T, E>(res: &Result<T, E>) -> bool
  where T: thrust_models::Model,
        E: thrust_models::Model,
{
    Result::is_ok(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x| *res == Ok(x) && result == false)
    || thrust_models::exists(|x| *res == Err(x) && result == true)
)]
fn _extern_spec_result_is_err<T, E>(res: &Result<T, E>) -> bool
  where T: thrust_models::Model,
        E: thrust_models::Model,
{
    Result::is_err(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)] // TODO: require x != i32::MIN
#[thrust_macros::ensures(result >= 0 && (result == x || result == -x))]
fn _extern_spec_i32_abs(x: i32) -> i32 {
    i32::abs(x)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (x >= y && result == (x - y))
    || (x < y && result == (y - x))
)]
fn _extern_spec_i32_abs_diff(x: i32, y: i32) -> u32 {
    i32::abs_diff(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((x == 0 && result == 0) || (x > 0 && result == 1) || (x < 0 && result == -1))]
fn _extern_spec_i32_signum(x: i32) -> i32 {
    i32::signum(x)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((x <= 0 && result == false) || (x > 0 && result == true))]
fn _extern_spec_i32_is_positive(x: i32) -> bool {
    i32::is_positive(x)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((x < 0 && result == true) || (x >= 0 && result == false))]
fn _extern_spec_i32_is_negative(x: i32) -> bool {
    i32::is_negative(x)
}

// Bit-counting intrinsics have no bitvector model (integers are plain `Int`, not bitvectors), so
// the only sound fact stated is the one every caller relies on: the count of a 64-bit value's
// bits cannot exceed 64.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result <= 64)]
fn _extern_spec_u64_trailing_zeros(x: u64) -> u32 {
    u64::trailing_zeros(x)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result <= 64)]
fn _extern_spec_u64_count_ones(x: u64) -> u32 {
    u64::count_ones(x)
}

// The checked arithmetic of signed integers: `None` exactly when the result leaves the range of
// the type.
macro_rules! int_checked_specs {
    ($T:ty, $checked_add:ident, $checked_sub:ident, $checked_mul:ident) => {
        #[thrust::extern_spec_fn]
        #[thrust_macros::requires(true)]
        #[thrust_macros::ensures(
            (<$T>::MIN <= x + y && x + y <= <$T>::MAX && result == Some(x + y))
            || ((x + y < <$T>::MIN || x + y > <$T>::MAX) && result == None)
        )]
        fn $checked_add(x: $T, y: $T) -> Option<$T> {
            <$T>::checked_add(x, y)
        }

        #[thrust::extern_spec_fn]
        #[thrust_macros::requires(true)]
        #[thrust_macros::ensures(
            (<$T>::MIN <= x - y && x - y <= <$T>::MAX && result == Some(x - y))
            || ((x - y < <$T>::MIN || x - y > <$T>::MAX) && result == None)
        )]
        fn $checked_sub(x: $T, y: $T) -> Option<$T> {
            <$T>::checked_sub(x, y)
        }

        #[thrust::extern_spec_fn]
        #[thrust_macros::requires(true)]
        #[thrust_macros::ensures(
            (<$T>::MIN <= x * y && x * y <= <$T>::MAX && result == Some(x * y))
            || ((x * y < <$T>::MIN || x * y > <$T>::MAX) && result == None)
        )]
        fn $checked_mul(x: $T, y: $T) -> Option<$T> {
            <$T>::checked_mul(x, y)
        }
    };
}

// The checked arithmetic of unsigned integers. The arguments are not negative, so a sum or a
// product can only leave the range above it and a difference only below it.
macro_rules! uint_checked_specs {
    ($T:ty, $checked_add:ident, $checked_sub:ident, $checked_mul:ident) => {
        #[thrust::extern_spec_fn]
        #[thrust_macros::requires(true)]
        #[thrust_macros::ensures(
            (x + y <= <$T>::MAX && result == Some(x + y)) || (x + y > <$T>::MAX && result == None)
        )]
        fn $checked_add(x: $T, y: $T) -> Option<$T> {
            <$T>::checked_add(x, y)
        }

        #[thrust::extern_spec_fn]
        #[thrust_macros::requires(true)]
        #[thrust_macros::ensures((x >= y && result == Some(x - y)) || (x < y && result == None))]
        fn $checked_sub(x: $T, y: $T) -> Option<$T> {
            <$T>::checked_sub(x, y)
        }

        #[thrust::extern_spec_fn]
        #[thrust_macros::requires(true)]
        #[thrust_macros::ensures(
            (x * y <= <$T>::MAX && result == Some(x * y)) || (x * y > <$T>::MAX && result == None)
        )]
        fn $checked_mul(x: $T, y: $T) -> Option<$T> {
            <$T>::checked_mul(x, y)
        }
    };
}

int_checked_specs!(isize, _extern_spec_isize_checked_add, _extern_spec_isize_checked_sub, _extern_spec_isize_checked_mul);
int_checked_specs!(i8, _extern_spec_i8_checked_add, _extern_spec_i8_checked_sub, _extern_spec_i8_checked_mul);
int_checked_specs!(i16, _extern_spec_i16_checked_add, _extern_spec_i16_checked_sub, _extern_spec_i16_checked_mul);
int_checked_specs!(i32, _extern_spec_i32_checked_add, _extern_spec_i32_checked_sub, _extern_spec_i32_checked_mul);
int_checked_specs!(i64, _extern_spec_i64_checked_add, _extern_spec_i64_checked_sub, _extern_spec_i64_checked_mul);
uint_checked_specs!(usize, _extern_spec_usize_checked_add, _extern_spec_usize_checked_sub, _extern_spec_usize_checked_mul);
uint_checked_specs!(u8, _extern_spec_u8_checked_add, _extern_spec_u8_checked_sub, _extern_spec_u8_checked_mul);
uint_checked_specs!(u16, _extern_spec_u16_checked_add, _extern_spec_u16_checked_sub, _extern_spec_u16_checked_mul);
uint_checked_specs!(u32, _extern_spec_u32_checked_add, _extern_spec_u32_checked_sub, _extern_spec_u32_checked_mul);
uint_checked_specs!(u64, _extern_spec_u64_checked_add, _extern_spec_u64_checked_sub, _extern_spec_u64_checked_mul);

// `div_ceil` is stable on the unsigned integers only.
macro_rules! uint_div_ceil_spec {
    ($T:ty, $div_ceil:ident) => {
        #[thrust::extern_spec_fn]
        #[thrust_macros::requires(y != 0)]
        #[thrust_macros::ensures(
            (x % y == 0 && result == x / y) || (x % y != 0 && result == x / y + 1)
        )]
        fn $div_ceil(x: $T, y: $T) -> $T {
            <$T>::div_ceil(x, y)
        }
    };
}

uint_div_ceil_spec!(usize, _extern_spec_usize_div_ceil);
uint_div_ceil_spec!(u8, _extern_spec_u8_div_ceil);
uint_div_ceil_spec!(u16, _extern_spec_u16_div_ceil);
uint_div_ceil_spec!(u32, _extern_spec_u32_div_ceil);
uint_div_ceil_spec!(u64, _extern_spec_u64_div_ceil);

// A conversion to `U` that fails exactly when the value does not fit, specified through the
// source type: `fits` says the value is one of `U`, and `converts_to` relates it to the `U` it
// becomes.
#[thrust_macros::context]
trait TryIntoSpec<U>: core::convert::TryInto<U> + thrust_models::Model
where
    U: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn fits(self) -> bool;

    #[thrust_macros::predicate]
    fn converts_to(self, out: U) -> bool;
}

macro_rules! int_try_into_specs {
    ($($from:ident),*) => {
        $(int_try_into_specs!(
            @from $from => isize, i8, i16, i32, i64, i128, usize, u8, u16, u32, u64, u128
        );)*
    };
    (@from $from:ident => $($to:ident),*) => {
        $(
            #[thrust_macros::context]
            impl TryIntoSpec<$to> for $from {
                #[thrust_macros::predicate]
                fn fits(self) -> bool {
                    $to::MIN <= self && self <= $to::MAX
                }

                #[thrust_macros::predicate]
                fn converts_to(self, out: $to) -> bool {
                    out == self
                }
            }
        )*
    };
}

int_try_into_specs!(isize, i8, i16, i32, i64, i128, usize, u8, u16, u32, u64, u128);

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (T::fits(value) && thrust_models::exists(|x| result == Ok(x) && T::converts_to(value, x)))
    || (!T::fits(value) && thrust_models::exists(|e| result == Err(e)))
)]
fn _extern_spec_try_into<T, U>(value: T) -> Result<U, <T as core::convert::TryInto<U>>::Error>
    where T: TryIntoSpec<U>,
          U: thrust_models::Model,
          <T as core::convert::TryInto<U>>::Error: thrust_models::Model,
{
    <T as core::convert::TryInto<U>>::try_into(value)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (T::fits(value) && thrust_models::exists(|x| result == Ok(x) && T::converts_to(value, x)))
    || (!T::fits(value) && thrust_models::exists(|e| result == Err(e)))
)]
fn _extern_spec_try_from<T, U>(value: T) -> Result<U, <U as core::convert::TryFrom<T>>::Error>
    where T: TryIntoSpec<U>,
          U: core::convert::TryFrom<T> + thrust_models::Model,
          <U as core::convert::TryFrom<T>>::Error: thrust_models::Model,
{
    <U as core::convert::TryFrom<T>>::try_from(value)
}

// A `Vec` is modelled as a `Seq`: capacity overflow and allocation failure are outside the model,
// so `push`, `extend`, `from_iter` and the like require nothing for them. Creusot's `Vec::push`
// likewise has no precondition (`// can OOM` in creusot-std/src/std/vec.rs).
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == 0)]
fn _extern_spec_vec_new<T>() -> Vec<T> where T: thrust_models::Model {
    Vec::<T>::new()
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!vec == (*vec).push(elem))]
fn _extern_spec_vec_push<T>(vec: &mut Vec<T>, elem: T)
    where T: thrust_models::Model
{
    Vec::push(vec, elem)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*vec).len())]
fn _extern_spec_vec_len<T>(vec: &Vec<T>) -> usize where T: thrust_models::Model {
    Vec::len(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(I::in_bounds(index, *vec))]
#[thrust_macros::ensures(I::has_value(index, *vec, *result))]
fn _extern_spec_vec_index<T, I>(vec: &Vec<T>, index: I) -> &<I as std::slice::SliceIndex<[T]>>::Output
    where T: thrust_models::Model,
          I: SliceIndexSpec<T>,
          <I as std::slice::SliceIndex<[T]>>::Output: thrust_models::Model
{
    <Vec<T> as std::ops::Index<I>>::index(vec, index)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(I::in_bounds(index, *vec))]
#[thrust_macros::ensures(
    I::has_value(index, *vec, *result) &&
    I::store_value(index, *vec, !result, !vec)
)]
fn _extern_spec_vec_index_mut<T, I>(vec: &mut Vec<T>, index: I) -> &mut <I as std::slice::SliceIndex<[T]>>::Output
    where T: thrust_models::Model,
          I: SliceIndexSpec<T>,
          <I as std::slice::SliceIndex<[T]>>::Output: thrust_models::Model
{
    <Vec<T> as std::ops::IndexMut<I>>::index_mut(vec, index)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((!vec).len() == 0)]
fn _extern_spec_vec_clear<T>(vec: &mut Vec<T>) where T: thrust_models::Model {
    Vec::clear(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (
        (
            (*vec).len() > 0 &&
            !vec == (*vec).subsequence(0, (*vec).len() - 1) &&
            result == Some((*vec)[(*vec).len() - 1])
        ) || (
            (*vec).len() == 0 &&
            (!vec).len() == 0 &&
            result == None
        )
    )
)]
fn _extern_spec_vec_pop<T>(vec: &mut Vec<T>) -> Option<T> where T: thrust_models::Model {
    Vec::pop(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == ((*vec).len() == 0))]
fn _extern_spec_vec_is_empty<T>(vec: &Vec<T>) -> bool where T: thrust_models::Model {
    Vec::is_empty(vec)
}

// The result is the subsequence of the old vector at the positions `kept`. The closure may change
// its state between calls, and a state cannot be named in a specification, so its precondition is
// asked at every state and its postcondition only says that some state returns what the call did:
// an element is kept only if `true` is possible, dropped only if `false` is.
// The length bound and the kept elements' postcondition are stated outside `kept`: deriving them
// from it takes an induction or an existential the solver does not find.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(
    thrust_models::forall(|c: thrust_models::model::Closure<F>, i: thrust_models::model::Int|
        !(0 <= i && i < (*vec).len()) || thrust_macros::pre!(c((*vec)[i])))
)]
#[thrust_macros::ensures(
    (!vec).len() <= (*vec).len()
        && thrust_models::forall(|k: thrust_models::model::Int| !(0 <= k && k < (!vec).len())
            || thrust_models::exists(|c: thrust_models::model::Closure<F>, d: thrust_models::model::Closure<F>|
                thrust_macros::post!(thrust_models::model::Mut::new(c, d)((!vec)[k]), true)))
        && thrust_models::exists(|kept: thrust_models::model::Seq<thrust_models::model::Int>|
            kept.len() == (!vec).len()
                && thrust_models::forall(|k: thrust_models::model::Int| !(0 <= k && k < kept.len())
                    || (0 <= kept[k] && kept[k] < (*vec).len() && (!vec)[k] == (*vec)[kept[k]]
                        && (k + 1 >= kept.len() || kept[k] < kept[k + 1])))
            && thrust_models::forall(|i: thrust_models::model::Int| !(0 <= i && i < (*vec).len())
                || thrust_models::exists(|k: thrust_models::model::Int| 0 <= k && k < kept.len() && kept[k] == i)
                || thrust_models::exists(|c: thrust_models::model::Closure<F>, d: thrust_models::model::Closure<F>|
                    thrust_macros::post!(thrust_models::model::Mut::new(c, d)((*vec)[i]), false))))
)]
fn _extern_spec_vec_retain<T, F>(vec: &mut Vec<T>, f: F)
    where T: thrust_models::Model,
          F: FnMut(&T) -> bool
{
    Vec::retain(vec, f)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (
        (*vec).len() > len &&
        !vec == (*vec).subsequence(0, len)
    ) || (
        (*vec).len() <= len &&
        !vec == *vec
    )
)]
fn _extern_spec_vec_truncate<T>(vec: &mut Vec<T>, len: usize) where T: thrust_models::Model {
    Vec::truncate(vec, len)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*result == *vec)]
fn _extern_spec_vec_as_slice<T>(vec: &Vec<T>) -> &[T]
    where T: thrust_models::Model
{
    Vec::as_slice(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*result == *vec)]
fn _extern_spec_vec_deref<T>(vec: &Vec<T>) -> &[T]
    where T: thrust_models::Model
{
    <Vec<T> as std::ops::Deref>::deref(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*result == *vec && !result == !vec)]
fn _extern_spec_vec_deref_mut<T>(vec: &mut Vec<T>) -> &mut [T]
    where T: thrust_models::Model
{
    <Vec<T> as std::ops::DerefMut>::deref_mut(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*result == *vec)]
fn _extern_spec_vec_as_ref<T>(vec: &Vec<T>) -> &[T]
    where T: thrust_models::Model
{
    <Vec<T> as AsRef<[T]>>::as_ref(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*slice).len())]
fn _extern_spec_slice_len<T>(slice: &[T]) -> usize
    where T: thrust_models::Model
{
    <[T]>::len(slice)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == ((*slice).len() == 0))]
fn _extern_spec_slice_is_empty<T>(slice: &[T]) -> bool
    where T: thrust_models::Model
{
    <[T]>::is_empty(slice)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (index < (*slice).len() && result == Some(&(*slice)[index]))
    || ((*slice).len() <= index && result == None)
)]
fn _extern_spec_slice_get<T>(slice: &[T], index: usize) -> Option<&T>
    where T: thrust_models::Model
{
    <[T]>::get(slice, index)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (index < (*slice).len()
        && result == Some(thrust_models::model::Mut::new(
            (*slice)[index],
            (!slice)[index],
        ))
        && !slice == (*slice).store(index, (!slice)[index])
    )
    || ((*slice).len() <= index && result == None && !slice == *slice)
)]
fn _extern_spec_slice_get_mut<T>(slice: &mut [T], index: usize) -> Option<&mut T>
    where T: thrust_models::Model
{
    <[T]>::get_mut(slice, index)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    ((*slice).len() > 0 && result == Some(&(*slice)[0]))
    || ((*slice).len() == 0 && result == None)
)]
fn _extern_spec_slice_first<T>(slice: &[T]) -> Option<&T>
    where T: thrust_models::Model
{
    <[T]>::first(slice)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    ((*slice).len() > 0
        && result == Some(thrust_models::model::Mut::new(
            (*slice)[0],
            (!slice)[0],
        ))
        && !slice == (*slice).store(0, (!slice)[0])
    )
    || ((*slice).len() == 0 && result == None && !slice == *slice)
)]
fn _extern_spec_slice_first_mut<T>(slice: &mut [T]) -> Option<&mut T>
    where T: thrust_models::Model
{
    <[T]>::first_mut(slice)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    ((*slice).len() > 0 && result == Some(&(*slice)[(*slice).len() - 1]))
    || ((*slice).len() == 0 && result == None)
)]
fn _extern_spec_slice_last<T>(slice: &[T]) -> Option<&T>
    where T: thrust_models::Model
{
    <[T]>::last(slice)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    ((*slice).len() > 0
        && result == Some(thrust_models::model::Mut::new(
            (*slice)[(*slice).len() - 1],
            (!slice)[(*slice).len() - 1],
        ))
        && !slice == (*slice).store(
            (*slice).len() - 1,
            (!slice)[(*slice).len() - 1],
        )
    )
    || ((*slice).len() == 0 && result == None && !slice == *slice)
)]
fn _extern_spec_slice_last_mut<T>(slice: &mut [T]) -> Option<&mut T>
    where T: thrust_models::Model
{
    <[T]>::last_mut(slice)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    ((*slice).len() > 0
        && result == Some((
            &(*slice)[0],
            &(*slice).subsequence(1, (*slice).len()),
        ))
    )
    || ((*slice).len() == 0 && result == None)
)]
fn _extern_spec_slice_split_first<T>(slice: &[T]) -> Option<(&T, &[T])>
    where T: thrust_models::Model
{
    <[T]>::split_first(slice)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    ((*slice).len() > 0
        && result == Some((
            &(*slice)[(*slice).len() - 1],
            &(*slice).subsequence(0, (*slice).len() - 1),
        ))
    )
    || ((*slice).len() == 0 && result == None)
)]
fn _extern_spec_slice_split_last<T>(slice: &[T]) -> Option<(&T, &[T])>
    where T: thrust_models::Model
{
    <[T]>::split_last(slice)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    ((*slice).len() > 0
        && (!slice).len() == (*slice).len()
        && result == Some((
            thrust_models::model::Mut::new((*slice)[0], (!slice)[0]),
            thrust_models::model::Mut::new(
                (*slice).subsequence(1, (*slice).len()),
                (!slice).subsequence(1, (!slice).len()),
            ),
        ))
    )
    || ((*slice).len() == 0 && result == None && !slice == *slice)
)]
fn _extern_spec_slice_split_first_mut<T>(slice: &mut [T]) -> Option<(&mut T, &mut [T])>
    where T: thrust_models::Model
{
    <[T]>::split_first_mut(slice)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    ((*slice).len() > 0
        && (!slice).len() == (*slice).len()
        && result == Some((
            thrust_models::model::Mut::new(
                (*slice)[(*slice).len() - 1],
                (!slice)[(!slice).len() - 1],
            ),
            thrust_models::model::Mut::new(
                (*slice).subsequence(0, (*slice).len() - 1),
                (!slice).subsequence(0, (!slice).len() - 1),
            ),
        ))
    )
    || ((*slice).len() == 0 && result == None && !slice == *slice)
)]
fn _extern_spec_slice_split_last_mut<T>(slice: &mut [T]) -> Option<(&mut T, &mut [T])>
    where T: thrust_models::Model
{
    <[T]>::split_last_mut(slice)
}

#[thrust_macros::context]
trait SliceIndexSpec<T>: std::slice::SliceIndex<[T]> + thrust_models::Model
where
    T: thrust_models::Model,
    <Self as std::slice::SliceIndex<[T]>>::Output: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn in_bounds(self, seq: Vec<T>) -> bool;

    #[thrust_macros::predicate]
    fn has_value(
        self,
        seq: Vec<T>,
        out: <Self as std::slice::SliceIndex<[T]>>::Output,
    ) -> bool;

    #[thrust_macros::predicate]
    fn store_value(
        self,
        seq: Vec<T>,
        out: <Self as std::slice::SliceIndex<[T]>>::Output,
        new_seq: Vec<T>,
    ) -> bool;
}

#[thrust_macros::context]
impl<T> SliceIndexSpec<T> for usize
where
    T: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn in_bounds(self, seq: Vec<T>) -> bool {
        self < seq.len()
    }

    #[thrust_macros::predicate]
    fn has_value(
        self,
        seq: Vec<T>,
        out: T,
    ) -> bool {
        seq[self] == out
    }

    #[thrust_macros::predicate]
    fn store_value(self, seq: Vec<T>, out: T, new_seq: Vec<T>) -> bool {
        new_seq == seq.store(self, out)
    }
}

#[thrust_macros::context]
impl<T> SliceIndexSpec<T> for std::ops::Range<usize>
where
    T: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn in_bounds(self, seq: Vec<T>) -> bool {
        self.start <= self.end && self.end <= seq.len()
    }

    #[thrust_macros::predicate]
    fn has_value(self, seq: Vec<T>, out: [T]) -> bool {
        seq.subsequence(self.start, self.end) == out
    }

    #[thrust_macros::predicate]
    fn store_value(self, seq: Vec<T>, out: [T], new_seq: Vec<T>) -> bool {
        new_seq == seq.subsequence(0, self.start)
            .concat(out)
            .concat(seq.subsequence(self.end, seq.len()))
    }
}

#[thrust_macros::context]
impl<T> SliceIndexSpec<T> for std::ops::RangeFrom<usize>
where
    T: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn in_bounds(self, seq: Vec<T>) -> bool {
        self.start <= seq.len()
    }

    #[thrust_macros::predicate]
    fn has_value(self, seq: Vec<T>, out: [T]) -> bool {
        seq.subsequence(self.start, seq.len()) == out
    }

    #[thrust_macros::predicate]
    fn store_value(self, seq: Vec<T>, out: [T], new_seq: Vec<T>) -> bool {
        new_seq == seq.subsequence(0, self.start).concat(out)
    }
}

#[thrust_macros::context]
impl<T> SliceIndexSpec<T> for std::ops::RangeTo<usize>
where
    T: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn in_bounds(self, seq: Vec<T>) -> bool {
        self.end <= seq.len()
    }

    #[thrust_macros::predicate]
    fn has_value(self, seq: Vec<T>, out: [T]) -> bool {
        seq.subsequence(0, self.end) == out
    }

    #[thrust_macros::predicate]
    fn store_value(self, seq: Vec<T>, out: [T], new_seq: Vec<T>) -> bool {
        new_seq == out.concat(seq.subsequence(self.end, seq.len()))
    }
}

#[thrust_macros::context]
impl<T> SliceIndexSpec<T> for std::ops::RangeToInclusive<usize>
where
    T: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn in_bounds(self, seq: Vec<T>) -> bool {
        self.end < seq.len()
    }

    #[thrust_macros::predicate]
    fn has_value(self, seq: Vec<T>, out: [T]) -> bool {
        seq.subsequence(0, self.end + 1) == out
    }

    #[thrust_macros::predicate]
    fn store_value(self, seq: Vec<T>, out: [T], new_seq: Vec<T>) -> bool {
        new_seq == out.concat(seq.subsequence(self.end + 1, seq.len()))
    }
}

#[thrust_macros::context]
impl<T> SliceIndexSpec<T> for std::ops::RangeFull
where
    T: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn in_bounds(self, _seq: Vec<T>) -> bool {
        true
    }

    #[thrust_macros::predicate]
    fn has_value(self, seq: Vec<T>, out: [T]) -> bool {
        seq == out
    }

    #[thrust_macros::predicate]
    fn store_value(self, _seq: Vec<T>, out: [T], new_seq: Vec<T>) -> bool {
        new_seq == out
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(I::in_bounds(index, *slice))]
#[thrust_macros::ensures(I::has_value(index, *slice, *result))]
fn _extern_spec_slice_index<T, I>(slice: &[T], index: I) -> &<I as std::slice::SliceIndex<[T]>>::Output
    where T: thrust_models::Model,
          I: SliceIndexSpec<T>,
          <I as std::slice::SliceIndex<[T]>>::Output: thrust_models::Model
{
    <[T] as std::ops::Index<I>>::index(slice, index)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(I::in_bounds(index, *slice))]
#[thrust_macros::ensures(
    I::has_value(index, *slice, *result) &&
    I::store_value(index, *slice, !result, !slice)
)]
fn _extern_spec_slice_index_mut<T, I>(slice: &mut [T], index: I) -> &mut <I as std::slice::SliceIndex<[T]>>::Output
    where T: thrust_models::Model,
          I: SliceIndexSpec<T>,
          <I as std::slice::SliceIndex<[T]>>::Output: thrust_models::Model
{
    <[T] as std::ops::IndexMut<I>>::index_mut(slice, index)
}

// `sort_by_key` permutes the slice: `p` maps each final position to the current position of the
// element it now holds, one to one and onto (Creusot's `permutation_of`, by a witness). That the
// result is sorted by the key is not stated. The key closure is called on the elements.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(
    thrust_models::forall(|c: thrust_models::model::Closure<F>, i: thrust_models::model::Int|
        !(0 <= i && i < (*slice).len()) || thrust_macros::pre!(c(&(*slice)[i])))
)]
#[thrust_macros::ensures(
    (!slice).len() == (*slice).len()
        && thrust_models::exists(|p: thrust_models::model::Seq<thrust_models::model::Int>|
            p.len() == (*slice).len()
                && thrust_models::forall(|i: thrust_models::model::Int|
                    !(0 <= i && i < (*slice).len())
                        || (0 <= p[i] && p[i] < (*slice).len() && (!slice)[i] == (*slice)[p[i]]))
                && thrust_models::forall(|i: thrust_models::model::Int, j: thrust_models::model::Int|
                    !(0 <= i && i < (*slice).len() && 0 <= j && j < (*slice).len() && i != j)
                        || p[i] != p[j])
                && thrust_models::forall(|j: thrust_models::model::Int|
                    !(0 <= j && j < (*slice).len())
                        || thrust_models::exists(|i: thrust_models::model::Int|
                            0 <= i && i < (*slice).len() && p[i] == j)))
)]
fn _extern_spec_slice_sort_by_key<T, K, F>(slice: &mut [T], f: F)
    where T: thrust_models::Model,
          K: Ord + thrust_models::Model,
          F: FnMut(&T) -> K
{
    <[T]>::sort_by_key(slice, f)
}

// `<[T]>::iter` and `<[T]>::iter_mut` start a fresh iterator at
// position 0 over the sequence they are given.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    result.0 == *slice && result.1 == 0
        && <core::slice::Iter<'_, T> as IteratorSpec>::inv(result)
)]
fn _extern_spec_slice_iter<T>(slice: &[T]) -> core::slice::Iter<'_, T>
    where T: thrust_models::Model
{
    <[T]>::iter(slice)
}

// The length preservation is stated here because nothing else supplies it: the iterator's
// components are plain sequences, so no drop resolves them.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    result.0 == *slice && result.1 == !slice && result.2 == 0
        && (!slice).len() == (*slice).len()
)]
fn _extern_spec_slice_iter_mut<T>(slice: &mut [T]) -> core::slice::IterMut<'_, T>
    where T: thrust_models::Model
{
    <[T]>::iter_mut(slice)
}

// `slice::IterMut` gets its own `next` rather than one through `IteratorSpec`: the two state the
// same step, and this one keeps the preserved sequences and the cursor's step as conjuncts of each
// case, where the clauses show them. The element handed out is the `Mut` pair of the current and
// final sequences at the cursor. The tail the loop has not reached yet keeps its prophecy
// unconstrained, so dropping the iterator early leaves the caller unable to say the untouched
// elements are unchanged; running it to exhaustion is what the specification supports.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    ((*it).2 < (*it).0.len()
        && result == Some(thrust_models::model::Mut::new(
            (*it).0[(*it).2],
            (*it).1[(*it).2],
        ))
        && (!it).0 == (*it).0
        && (!it).1 == (*it).1
        && (!it).2 == (*it).2 + 1)
    || ((*it).2 >= (*it).0.len() && result == None && !it == *it)
)]
fn _extern_spec_slice_iter_mut_next<'a, T>(
    it: &mut core::slice::IterMut<'a, T>,
) -> Option<&'a mut T>
    where T: thrust_models::Model + 'a
{
    <core::slice::IterMut<'a, T> as std::iter::Iterator>::next(it)
}

// `next` is specified once, through the predicates of `IteratorSpec`; a type gets a `next` by
// implementing the trait. `next` is total: `completed` covers every position at or past the end.
// `inv` is the state invariant, Creusot's type invariant: `next` requires and keeps it, so that an
// iterator whose `next` panics outside it (one building an index) can implement the trait, and
// `produces_refl` holds at the states that satisfy it. The laws are Creusot's; they let a loop
// over a type parameter accumulate what `next` produced.
#[thrust_macros::context]
trait IteratorSpec: std::iter::Iterator + thrust_models::Model
where
    Self::Item: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool;

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<Self::Item>, o: Self) -> bool;

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::inv(*a))]
    #[thrust_macros::ensures(Self::produces(*a, thrust_models::model::Seq::empty(), *a))]
    fn produces_refl(a: &Self);

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b) && Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    );
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(I::inv(*it))]
#[thrust_macros::ensures(
    I::inv(!it)
        && (result == None ==> I::completed(it))
        && thrust_models::forall(|x: <I::Item as thrust_models::Model>::Ty| result == Some(x)
            ==> I::produces(*it, thrust_models::model::Seq::singleton(x), !it))
)]
fn _extern_spec_iterator_next<I>(it: &mut I) -> Option<I::Item>
    where I: IteratorSpec,
          I::Item: thrust_models::Model
{
    <I as std::iter::Iterator>::next(it)
}

// The predicate accepted the item found in some state of it; which state, and that it rejected
// the items before, is not stated: that needs the sequence of its states across the calls, on
// which PCSat fails. Each step is `next`, which keeps `inv`.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(
    I::inv(*it)
        && thrust_models::forall(|c: thrust_models::model::Closure<P>|
            thrust_models::forall(|x: <I::Item as thrust_models::Model>::Ty| thrust_macros::pre!(c(&x))))
)]
#[thrust_macros::ensures(
    I::inv(!it)
        && ((result == None
            && thrust_models::exists(|visited: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>, mid: I::Ty|
                I::produces(*it, visited, mid) && I::completed(thrust_models::model::Mut::new(mid, !it))))
        || thrust_models::exists(|visited: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>,
                                  x: <I::Item as thrust_models::Model>::Ty|
            result == Some(x)
                && I::produces(*it, visited.push(x), !it)
                && thrust_models::exists(|c: thrust_models::model::Closure<P>, d: thrust_models::model::Closure<P>|
                    thrust_macros::post!(thrust_models::model::Mut::new(c, d)(&x), true))))
)]
fn _extern_spec_iterator_find<I, P>(it: &mut I, predicate: P) -> Option<I::Item>
    where I: IteratorSpec,
          I::Item: thrust_models::Model,
          P: FnMut(&I::Item) -> bool
{
    <I as std::iter::Iterator>::find(it, predicate)
}

#[thrust_macros::context]
impl<'a, T> IteratorSpec for core::slice::Iter<'a, T>
where
    T: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        self.1 <= self.0.len()
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<&'a T>, o: Self) -> bool {
        self.0 == o.0
            && self.1 <= o.1
            && o.1 <= self.0.len()
            && visited.len() == o.1 - self.1
            && thrust_models::forall(|i: thrust_models::model::Int|
                !(0 <= i && i < visited.len()) || visited[i] == &self.0[self.1 + i])
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).1 >= (*self).0.len() && *self == !self
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust_macros::context]
impl<T> IteratorSpec for std::vec::IntoIter<T>
where
    T: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        self.1 <= self.0.len()
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<T>, o: Self) -> bool {
        self.0 == o.0
            && self.1 <= o.1
            && o.1 <= self.0.len()
            && visited.len() == o.1 - self.1
            && thrust_models::forall(|i: thrust_models::model::Int|
                !(0 <= i && i < visited.len()) || visited[i] == self.0[self.1 + i])
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).1 >= (*self).0.len() && *self == !self
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust_macros::context]
impl<I> IteratorSpec for core::iter::Enumerate<I>
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        I::inv(self.0)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<(usize, I::Item)>, o: Self) -> bool {
        visited.len() == o.1 - self.1
            && thrust_models::exists(|inner: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>|
                I::produces(self.0, inner, o.0)
                    && inner.len() == visited.len()
                    && thrust_models::forall(|i: thrust_models::model::UInt|
                        !(0 <= i && i < inner.len()) || visited[i] == (self.1 + i, inner[i])))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(thrust_models::model::Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.0 == it && result.1 == 0)]
fn _extern_spec_iterator_enumerate<I>(it: I) -> core::iter::Enumerate<I>
    where I: IteratorSpec,
          I::Item: thrust_models::Model
{
    <I as std::iter::Iterator>::enumerate(it)
}

// When both iterators are `TrustedRandomAccess` (slice iterators and the adapters over them,
// `Map` included), std's `Zip::next` steps neither of them and answers `None` once it has handed
// out as many items as the shorter one has, so `completed` also allows the zip unchanged at a
// point where one of the two could complete. A `Map` over the longer side then runs its closure
// once less than the general `Zip::next` would.
#[thrust_macros::context]
impl<A, B> IteratorSpec for core::iter::Zip<A, B>
where
    A: IteratorSpec,
    B: IteratorSpec,
    A::Item: thrust_models::Model,
    B::Item: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        A::inv(self.0) && B::inv(self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<(A::Item, B::Item)>, o: Self) -> bool {
        thrust_models::exists(|xs: thrust_models::model::Seq<<A::Item as thrust_models::Model>::Ty>| thrust_models::exists(|ys: thrust_models::model::Seq<<B::Item as thrust_models::Model>::Ty>|
            A::produces(self.0, xs, o.0)
                && B::produces(self.1, ys, o.1)
                && xs.len() == visited.len()
                && ys.len() == visited.len()
                && thrust_models::forall(|i: thrust_models::model::Int|
                    !(0 <= i && i < visited.len()) || visited[i] == (xs[i], ys[i]))))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (A::completed(thrust_models::model::Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1)
            || thrust_models::exists(|x: <A::Item as thrust_models::Model>::Ty|
                A::produces((*self).0, thrust_models::model::Seq::singleton(x), (!self).0)
                    && B::completed(thrust_models::model::Mut::new((*self).1, (!self).1)))
            || (*self == !self
                && (thrust_models::exists(|a: <A as thrust_models::Model>::Ty|
                        A::completed(thrust_models::model::Mut::new((*self).0, a)))
                    || thrust_models::exists(|b: <B as thrust_models::Model>::Ty|
                        B::completed(thrust_models::model::Mut::new((*self).1, b)))))
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

// The adapters below follow Creusot's (creusot-std src/std/iter/skip.rs, take.rs, cloned.rs,
// copied.rs and the constructors in src/std/iter.rs).

// The first `next` drops the `n` items ahead of the first item it hands out (std calls `nth`).
// `completed` leaves the inner iterator's state after the call open: where `nth` gives up, it can
// leave the inner iterator elsewhere than `next` would (an inverted `Range` is set to `end..end`).
#[thrust_macros::context]
impl<I> IteratorSpec for core::iter::Skip<I>
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        I::inv(self.0)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<I::Item>, o: Self) -> bool {
        (visited.len() == 0 && self == o)
            || (o.1 == 0
                && visited.len() > 0
                && thrust_models::exists(|s: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>|
                    s.len() == self.1 && I::produces(self.0, s.concat(visited), o.0)))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (!self).1 == 0
            && thrust_models::exists(|s: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>,
                                      j: I::Ty,
                                      j2: I::Ty|
                s.len() <= (*self).1
                    && I::produces((*self).0, s, j)
                    && I::completed(thrust_models::model::Mut::new(j, j2)))
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.0 == it && result.1 == n)]
fn _extern_spec_iterator_skip<I>(it: I, n: usize) -> core::iter::Skip<I>
    where I: IteratorSpec,
          I::Item: thrust_models::Model
{
    <I as std::iter::Iterator>::skip(it, n)
}

// `next` counts down before it asks the inner iterator, but `try_fold` and `advance_by` do not
// count the call on which the inner iterator runs out, so `completed` allows either count.
#[thrust_macros::context]
impl<I> IteratorSpec for core::iter::Take<I>
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        I::inv(self.0)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<I::Item>, o: Self) -> bool {
        self.1 == o.1 + visited.len() && I::produces(self.0, visited, o.0)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        ((*self).1 == 0 && *self == !self)
            || ((*self).1 > 0
                && ((*self).1 == (!self).1 + 1 || (*self).1 == (!self).1)
                && I::completed(thrust_models::model::Mut::new((*self).0, (!self).0)))
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.0 == it && result.1 == n)]
fn _extern_spec_iterator_take<I>(it: I, n: usize) -> core::iter::Take<I>
    where I: IteratorSpec,
          I::Item: thrust_models::Model
{
    <I as std::iter::Iterator>::take(it, n)
}

// Each item is a clone of the referent the inner iterator hands out, which is the referent itself
// in the model.
#[thrust_macros::context]
impl<'a, I, T> IteratorSpec for core::iter::Cloned<I>
where
    I: IteratorSpec<Item = &'a T>,
    T: thrust_models::Model + Clone + 'a,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        I::inv(self)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<T>, o: Self) -> bool {
        thrust_models::exists(|s: thrust_models::model::Seq<&'a <T as thrust_models::Model>::Ty>|
            I::produces(self, s, o)
                && s.len() == visited.len()
                && thrust_models::forall(|i: thrust_models::model::Int|
                    !(0 <= i && i < visited.len()) || s[i] == &visited[i]))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(thrust_models::model::Mut::new(*self, !self))
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == it)]
fn _extern_spec_iterator_cloned<'a, I, T>(it: I) -> core::iter::Cloned<I>
    where I: IteratorSpec<Item = &'a T>,
          T: thrust_models::Model + Clone + 'a
{
    <I as std::iter::Iterator>::cloned(it)
}

#[thrust_macros::context]
impl<'a, I, T> IteratorSpec for core::iter::Copied<I>
where
    I: IteratorSpec<Item = &'a T>,
    T: thrust_models::Model + Copy + 'a,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        I::inv(self)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<T>, o: Self) -> bool {
        thrust_models::exists(|s: thrust_models::model::Seq<&'a <T as thrust_models::Model>::Ty>|
            I::produces(self, s, o)
                && s.len() == visited.len()
                && thrust_models::forall(|i: thrust_models::model::Int|
                    !(0 <= i && i < visited.len()) || s[i] == &visited[i]))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(thrust_models::model::Mut::new(*self, !self))
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == it)]
fn _extern_spec_iterator_copied<'a, I, T>(it: I) -> core::iter::Copied<I>
    where I: IteratorSpec<Item = &'a T>,
          T: thrust_models::Model + Copy + 'a
{
    <I as std::iter::Iterator>::copied(it)
}

// Creusot's `Map` (creusot-std src/std/iter/map.rs). Its invariant asks that the closure accept
// the next item (`_iter_spec_map_next_precondition`), that each call leave it accepting the item
// after (`_iter_spec_map_preservation`), and that both hold again from wherever the inner
// iterator completes (`_iter_spec_map_reinitialize`). `produces` chains the closure's states `fs`
// along the inner items `s`: `fs[k]` before and `fs[k + 1]` after the `k`-th call. The helpers'
// names start with `_iter_spec_` because std.rs is injected at the root of the checked crate.
#[thrust_macros::predicate]
fn _iter_spec_map_next_precondition<I, B, F>(iter: I, func: F) -> bool
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
{
    thrust_models::forall(|e: <I::Item as thrust_models::Model>::Ty| thrust_models::forall(|i: <I as thrust_models::Model>::Ty|
        !I::produces(iter, thrust_models::model::Seq::singleton(e), i) || thrust_macros::pre!(func(e))))
}

#[thrust_macros::predicate]
fn _iter_spec_map_preservation<I, B, F>(iter: I, func: F) -> bool
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
{
    thrust_models::forall(|s: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>|
    thrust_models::forall(|e1: <I::Item as thrust_models::Model>::Ty|
    thrust_models::forall(|e2: <I::Item as thrust_models::Model>::Ty|
    thrust_models::forall(|i: <I as thrust_models::Model>::Ty|
    thrust_models::forall(|f1: thrust_models::model::Closure<F>|
    thrust_models::forall(|f2: thrust_models::model::Closure<F>|
    thrust_models::forall(|b: <B as thrust_models::Model>::Ty|
        !(thrust_macros::hist_inv!(func, f1)
            && I::produces(iter, s.push(e1).push(e2), i)
            && thrust_macros::pre!(f1(e1))
            && thrust_macros::post!(thrust_models::model::Mut::new(f1, f2)(e1), b))
            || thrust_macros::pre!(f2(e2)))))))))
}

#[thrust_macros::predicate]
fn _iter_spec_map_reinitialize<I, B, F>() -> bool
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
{
    thrust_models::forall(|cur: <I as thrust_models::Model>::Ty|
    thrust_models::forall(|fin: <I as thrust_models::Model>::Ty|
    thrust_models::forall(|f: thrust_models::model::Closure<F>|
        !I::completed(thrust_models::model::Mut::new(cur, fin))
            || (_iter_spec_map_next_precondition::<I, B, F>(fin, f) && _iter_spec_map_preservation::<I, B, F>(fin, f)))))
}

#[thrust_macros::context]
impl<I, B, F> IteratorSpec for core::iter::Map<I, F>
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        I::inv(self.0)
            && _iter_spec_map_reinitialize::<I, B, F>()
            && _iter_spec_map_preservation::<I, B, F>(self.0, self.1)
            && _iter_spec_map_next_precondition::<I, B, F>(self.0, self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<B>, o: Self) -> bool {
        thrust_macros::hist_inv!(self.1, o.1)
            && thrust_models::exists(|s: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>,
                                      fs: thrust_models::model::Seq<thrust_models::model::Closure<F>>|
                s.len() == visited.len()
                    && I::produces(self.0, s, o.0)
                    && fs.len() == visited.len() + 1
                    && fs[0] == self.1
                    && fs[visited.len()] == o.1
                    && thrust_models::forall(|k: thrust_models::model::Int|
                        !(0 <= k && k < visited.len())
                            || (thrust_macros::hist_inv!(self.1, fs[k])
                                && thrust_macros::post!(thrust_models::model::Mut::new(fs[k], fs[k + 1])(s[k]), visited[k]))))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(thrust_models::model::Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(
    _iter_spec_map_next_precondition::<I, B, F>(it, f)
        && _iter_spec_map_reinitialize::<I, B, F>()
        && _iter_spec_map_preservation::<I, B, F>(it, f)
)]
#[thrust_macros::ensures(result.0 == it && result.1 == f)]
fn _extern_spec_iterator_map<I, B, F>(it: I, f: F) -> core::iter::Map<I, F>
    where I: IteratorSpec,
          I::Item: thrust_models::Model,
          B: thrust_models::Model,
          F: FnMut(I::Item) -> B
{
    <I as std::iter::Iterator>::map(it, f)
}

// A range of integers yields its start and steps it up to its end, as Creusot's `Range` does
// (creusot-std/src/std/iter/range.rs).
macro_rules! range_iterator_spec {
    ($($t:ty)*) => {
        $(
            #[thrust_macros::context]
            impl IteratorSpec for core::ops::Range<$t> {
                #[thrust_macros::predicate]
                fn inv(self) -> bool {
                    true
                }

                #[thrust_macros::predicate]
                fn produces(self, visited: Vec<$t>, o: Self) -> bool {
                    self.end == o.end
                        && self.start <= o.start
                        && (visited.len() == 0 || o.start <= o.end)
                        && visited.len() == o.start - self.start
                        && thrust_models::forall(|i: thrust_models::model::Int|
                            !(0 <= i && i < visited.len()) || visited[i] == self.start + i)
                }

                #[thrust_macros::predicate]
                fn completed(&mut self) -> bool {
                    (*self).start >= (*self).end && *self == !self
                }

                fn produces_refl(a: &Self) {}

                fn produces_trans(
                    a: &Self,
                    ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
                    b: &Self,
                    bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
                    c: &Self,
                ) {
                }
            }
        )*
    };
}

range_iterator_spec!(i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize);

// `next_back` is specified once, through `produces_back`, as `next` is through `produces`
// (Creusot's `DoubleEndedIteratorSpec`, creusot-std src/std/iter.rs). A type gets a `next_back`
// by implementing the trait.
#[thrust_macros::context]
trait DoubleEndedIteratorSpec: std::iter::DoubleEndedIterator + IteratorSpec
where
    Self::Item: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn produces_back(self, visited: Vec<Self::Item>, o: Self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::inv(*a))]
    #[thrust_macros::ensures(Self::produces_back(*a, thrust_models::model::Seq::empty(), *a))]
    fn produces_back_refl(a: &Self);

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces_back(*a, ab, *b) && Self::produces_back(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces_back(*a, ab.concat(bc), *c))]
    fn produces_back_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    );
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(I::inv(*it))]
#[thrust_macros::ensures(
    I::inv(!it)
        && (result == None ==> I::completed(it))
        && thrust_models::forall(|x: <I::Item as thrust_models::Model>::Ty| result == Some(x)
            ==> I::produces_back(*it, thrust_models::model::Seq::singleton(x), !it))
)]
fn _extern_spec_double_ended_iterator_next_back<I>(it: &mut I) -> Option<I::Item>
    where I: DoubleEndedIteratorSpec,
          I::Item: thrust_models::Model
{
    <I as std::iter::DoubleEndedIterator>::next_back(it)
}

// Creusot's `produces_back` of `Range` (creusot-std src/std/iter/range.rs, 3620de437) bounds the
// length by `o.end - self.end`, which is never positive, and starts the items at `end`; here the
// length is what the end moved down by and the first item is `end - 1`.
macro_rules! range_double_ended_iterator_spec {
    ($($t:ty)*) => {
        $(
            #[thrust_macros::context]
            impl DoubleEndedIteratorSpec for core::ops::Range<$t> {
                #[thrust_macros::predicate]
                fn produces_back(self, visited: Vec<$t>, o: Self) -> bool {
                    self.start == o.start
                        && o.end <= self.end
                        && (visited.len() == 0 || o.start <= o.end)
                        && visited.len() == self.end - o.end
                        && thrust_models::forall(|i: thrust_models::model::Int|
                            !(0 <= i && i < visited.len()) || visited[i] == self.end - 1 - i)
                }

                fn produces_back_refl(a: &Self) {}

                fn produces_back_trans(
                    a: &Self,
                    ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
                    b: &Self,
                    bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
                    c: &Self,
                ) {
                }
            }
        )*
    };
}

range_double_ended_iterator_spec!(i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize);

// An inclusive range is empty once `exhausted` is set or its start passes its end; it then yields
// nothing more, whatever its bounds are. Creusot's `RangeInclusive` (creusot-std
// src/std/iter/range.rs), with the difference of its `range_inclusive_len` split by which of the
// two ranges are empty.
macro_rules! range_inclusive_iterator_spec {
    ($($t:ty)*) => {
        $(
            #[thrust_macros::context]
            impl IteratorSpec for core::ops::RangeInclusive<$t> {
                #[thrust_macros::predicate]
                fn inv(self) -> bool {
                    true
                }

                #[thrust_macros::predicate]
                fn produces(self, visited: Vec<$t>, o: Self) -> bool {
                    (!(self.2 || !(self.0 <= self.1)) || (visited.len() == 0 && (o.2 || !(o.0 <= o.1))))
                        && (self.2 || !(self.0 <= self.1) || o.2 || !(o.0 <= o.1)
                            || (self.1 == o.1 && visited.len() == o.0 - self.0))
                        && (self.2 || !(self.0 <= self.1) || !(o.2 || !(o.0 <= o.1))
                            || visited.len() == self.1 - self.0 + 1)
                        && thrust_models::forall(|i: thrust_models::model::Int|
                            !(0 <= i && i < visited.len()) || visited[i] == self.0 + i)
                }

                #[thrust_macros::predicate]
                fn completed(&mut self) -> bool {
                    ((*self).2 || !((*self).0 <= (*self).1))
                        && ((!self).2 || !((!self).0 <= (!self).1))
                }

                fn produces_refl(a: &Self) {}

                fn produces_trans(
                    a: &Self,
                    ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
                    b: &Self,
                    bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
                    c: &Self,
                ) {
                }
            }

            #[thrust_macros::context]
            impl DoubleEndedIteratorSpec for core::ops::RangeInclusive<$t> {
                #[thrust_macros::predicate]
                fn produces_back(self, visited: Vec<$t>, o: Self) -> bool {
                    (!(self.2 || !(self.0 <= self.1)) || (visited.len() == 0 && (o.2 || !(o.0 <= o.1))))
                        && (self.2 || !(self.0 <= self.1) || o.2 || !(o.0 <= o.1)
                            || (self.0 == o.0 && visited.len() == self.1 - o.1))
                        && (self.2 || !(self.0 <= self.1) || !(o.2 || !(o.0 <= o.1))
                            || visited.len() == self.1 - self.0 + 1)
                        && thrust_models::forall(|i: thrust_models::model::Int|
                            !(0 <= i && i < visited.len()) || visited[i] == self.1 - i)
                }

                fn produces_back_refl(a: &Self) {}

                fn produces_back_trans(
                    a: &Self,
                    ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
                    b: &Self,
                    bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
                    c: &Self,
                ) {
                }
            }
        )*
    };
}

range_inclusive_iterator_spec!(i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize);

// `start..=end` is `RangeInclusive::new(start, end)`.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.0 == start && result.1 == end && !result.2)]
fn _extern_spec_range_inclusive_new<Idx>(start: Idx, end: Idx) -> core::ops::RangeInclusive<Idx>
    where Idx: thrust_models::Model
{
    core::ops::RangeInclusive::new(start, end)
}

// Creusot's `Rev` (creusot-std src/std/iter/rev.rs): the items of the inner iterator taken from
// the back.
#[thrust_macros::context]
impl<I> IteratorSpec for core::iter::Rev<I>
where
    I: DoubleEndedIteratorSpec,
    I::Item: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        I::inv(self)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<I::Item>, o: Self) -> bool {
        I::produces_back(self, visited, o)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(thrust_models::model::Mut::new(*self, !self))
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == it)]
fn _extern_spec_iterator_rev<I>(it: I) -> core::iter::Rev<I>
    where I: DoubleEndedIteratorSpec,
          I::Item: thrust_models::Model
{
    <I as std::iter::Iterator>::rev(it)
}

// Creusot's `Filter` (creusot-std src/std/iter/filter.rs). The predicate has no precondition,
// keeps its captures and answers each item one way (`_iter_spec_filter_closure`), as Creusot
// requires. `produces` takes the inner items `s` and the increasing positions `idx` in `s` of the
// items handed out (Creusot's `Mapping<Int, Int>`): exactly the items on which the predicate
// answers `true`.
#[thrust_macros::predicate]
fn _iter_spec_filter_closure<I, P>() -> bool
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
    P: FnMut(&I::Item) -> bool,
{
    thrust_models::forall(|f: thrust_models::model::Closure<P>, x: <I::Item as thrust_models::Model>::Ty|
        thrust_macros::pre!(f(&x)))
        && thrust_models::forall(|f: thrust_models::model::Closure<P>, g: thrust_models::model::Closure<P>|
            !thrust_macros::hist_inv!(f, g) || f == g)
        && thrust_models::forall(|f: thrust_models::model::Closure<P>,
                                  g: thrust_models::model::Closure<P>,
                                  x: <I::Item as thrust_models::Model>::Ty|
            !(thrust_macros::post!(thrust_models::model::Mut::new(f, g)(&x), true)
                && thrust_macros::post!(thrust_models::model::Mut::new(f, g)(&x), false)))
}

#[thrust_macros::context]
impl<I, P> IteratorSpec for core::iter::Filter<I, P>
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
    P: FnMut(&I::Item) -> bool,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        I::inv(self.0) && _iter_spec_filter_closure::<I, P>()
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<I::Item>, o: Self) -> bool {
        !_iter_spec_filter_closure::<I, P>()
            || (thrust_macros::hist_inv!(self.1, o.1)
                && thrust_models::exists(|s: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>,
                                          idx: thrust_models::model::Seq<thrust_models::model::Int>|
                    I::produces(self.0, s, o.0)
                        && idx.len() == visited.len()
                        && thrust_models::forall(|i: thrust_models::model::Int|
                            !(0 <= i && i < visited.len())
                                || (0 <= idx[i] && idx[i] < s.len() && visited[i] == s[idx[i]]))
                        && thrust_models::forall(|i: thrust_models::model::Int, j: thrust_models::model::Int|
                            !(0 <= i && i < j && j < visited.len()) || idx[i] < idx[j])
                        && thrust_models::forall(|k: thrust_models::model::Int|
                            !(0 <= k && k < s.len())
                                || ((!thrust_models::exists(|j: thrust_models::model::Int|
                                        0 <= j && j < visited.len() && idx[j] == k)
                                    || thrust_macros::post!(thrust_models::model::Mut::new(self.1, self.1)(&s[k]), true))
                                    && (thrust_models::exists(|j: thrust_models::model::Int|
                                        0 <= j && j < visited.len() && idx[j] == k)
                                    || !thrust_macros::post!(thrust_models::model::Mut::new(self.1, self.1)(&s[k]), true))))))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        thrust_models::exists(|s: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>,
                               e: <I as thrust_models::Model>::Ty,
                               e2: <I as thrust_models::Model>::Ty|
            I::produces((*self).0, s, e)
                && I::completed(thrust_models::model::Mut::new(e, e2))
                && thrust_models::forall(|k: thrust_models::model::Int|
                    !(0 <= k && k < s.len())
                        || thrust_macros::post!(thrust_models::model::Mut::new((*self).1, (!self).1)(&s[k]), false)))
            && (*self).1 == (!self).1
    }

    fn produces_refl(a: &Self) {}

    // Trusted: PCSat (fptprove 8746111b4) gives no answer on this law in 200 s. Creusot proves it
    // with an empty body.
    #[thrust::trusted]
    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(_iter_spec_filter_closure::<I, P>())]
#[thrust_macros::ensures(result.0 == it && result.1 == p)]
fn _extern_spec_iterator_filter<I, P>(it: I, p: P) -> core::iter::Filter<I, P>
    where I: IteratorSpec,
          I::Item: thrust_models::Model,
          P: FnMut(&I::Item) -> bool
{
    <I as std::iter::Iterator>::filter(it, p)
}

// `Chain` hands out the first iterator's items, drops that iterator once it completes, then hands
// out the second's (std's `Chain::next`). Creusot has no `Chain`; the form follows its `Fuse` for
// the dropped iterator and its `Zip` for the two parts of the produced sequence.
// `_iter_spec_chain_second` is what the second iterator contributes.
#[thrust_macros::predicate]
fn _iter_spec_chain_second<B>(
    b: Option<B>,
    ys: thrust_models::model::Seq<<B::Item as thrust_models::Model>::Ty>,
    b2: Option<B>,
) -> bool
where
    B: IteratorSpec,
    B::Item: thrust_models::Model,
{
    (b == None && ys.len() == 0 && b2 == None)
        || thrust_models::exists(|x: <B as thrust_models::Model>::Ty, x2: <B as thrust_models::Model>::Ty|
            b == Some(x) && b2 == Some(x2) && B::produces(x, ys, x2))
}

#[thrust_macros::context]
impl<A, B> IteratorSpec for core::iter::Chain<A, B>
where
    A: IteratorSpec,
    B: IteratorSpec<Item = A::Item>,
    A::Item: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        thrust_models::forall(|x: <A as thrust_models::Model>::Ty| self.0 != Some(x) || A::inv(x))
            && thrust_models::forall(|y: <B as thrust_models::Model>::Ty| self.1 != Some(y) || B::inv(y))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<A::Item>, o: Self) -> bool {
        (self.0 == None && o.0 == None && _iter_spec_chain_second::<B>(self.1, visited, o.1))
            || thrust_models::exists(|x: <A as thrust_models::Model>::Ty, x2: <A as thrust_models::Model>::Ty|
                self.0 == Some(x) && o.0 == Some(x2) && A::produces(x, visited, x2) && o.1 == self.1)
            || thrust_models::exists(|x: <A as thrust_models::Model>::Ty,
                                      x2: <A as thrust_models::Model>::Ty,
                                      x3: <A as thrust_models::Model>::Ty,
                                      xs: thrust_models::model::Seq<<A::Item as thrust_models::Model>::Ty>,
                                      ys: thrust_models::model::Seq<<A::Item as thrust_models::Model>::Ty>|
                self.0 == Some(x)
                    && o.0 == None
                    && visited == xs.concat(ys)
                    && A::produces(x, xs, x2)
                    && A::completed(thrust_models::model::Mut::new(x2, x3))
                    && _iter_spec_chain_second::<B>(self.1, ys, o.1))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        ((*self).0 == None
            || thrust_models::exists(|x: <A as thrust_models::Model>::Ty, x2: <A as thrust_models::Model>::Ty|
                (*self).0 == Some(x) && A::completed(thrust_models::model::Mut::new(x, x2))))
            && (!self).0 == None
            && (((*self).1 == None && (!self).1 == None)
                || thrust_models::exists(|y: <B as thrust_models::Model>::Ty, y2: <B as thrust_models::Model>::Ty|
                    (*self).1 == Some(y) && (!self).1 == Some(y2) && B::completed(thrust_models::model::Mut::new(y, y2))))
    }

    fn produces_refl(a: &Self) {}

    // Trusted: PCSat (fptprove 8746111b4) gives no answer on this law. It follows from the laws of
    // `A` and `B` by cases on whether each of the two steps leaves the first iterator in place.
    #[thrust::trusted]
    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    result.0 == Some(it)
        && thrust_models::exists(|y: <U::IntoIter as thrust_models::Model>::Ty|
            result.1 == Some(y) && U::into_iter_is(other, y))
)]
fn _extern_spec_iterator_chain<I, U>(it: I, other: U) -> core::iter::Chain<I, U::IntoIter>
    where I: IteratorSpec,
          I::Item: thrust_models::Model,
          U: IntoIteratorSpec<Item = I::Item>,
          U::IntoIter: IteratorSpec<Item = I::Item>
{
    <I as std::iter::Iterator>::chain(it, other)
}

// Creusot's `&mut I` (creusot-std src/std/iter.rs): stepping the reference steps the iterator it
// points to, whose final value stays that of the reference. Unlike Creusot's, `completed` relates
// the referent before and after this call, not to its value when the reference dies, which a later
// write through the reference can still change.
#[thrust_macros::context]
impl<'a, I> IteratorSpec for &'a mut I
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        I::inv(*self)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<I::Item>, o: Self) -> bool {
        I::produces(*self, visited, *o) && !self == !o
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(thrust_models::model::Mut::new(*(*self), *(!self))) && !(*self) == !(!self)
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == it)]
fn _extern_spec_iterator_by_ref<'a, I>(it: &'a mut I) -> &'a mut I
    where I: IteratorSpec,
          I::Item: thrust_models::Model
{
    <I as std::iter::Iterator>::by_ref(it)
}

// `count` is the number of items produced up to completion. std adds with the checked crate's
// overflow checks, so the count wraps without them; as Creusot's `enumerate` does, the
// precondition bounds what the iterator can produce.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(
    I::inv(it)
        && thrust_models::forall(|s: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>,
                                  i: <I as thrust_models::Model>::Ty|
            !I::produces(it, s, i) || s.len() <= <usize>::MAX)
)]
#[thrust_macros::ensures(
    thrust_models::exists(|s: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>,
                           done: <I as thrust_models::Model>::Ty,
                           fin: <I as thrust_models::Model>::Ty|
        I::produces(it, s, done)
            && I::completed(thrust_models::model::Mut::new(done, fin))
            && result == s.len())
)]
fn _extern_spec_iterator_count<I>(it: I) -> usize
    where I: IteratorSpec,
          I::Item: thrust_models::Model
{
    <I as std::iter::Iterator>::count(it)
}

// `fold` runs the closure along what the iterator produces up to its completion: the closure's
// states `fs` and the accumulators `accs` along the items `s` form a chain in which each step is
// a call's postcondition, in the form of Creusot's `Map` (creusot-std src/std/iter/map.rs).
// tests/ui/pass/creusot/generic/std/fold_map.rs verifies std's body of `fold` against this
// contract.
#[thrust_macros::predicate]
fn _iter_spec_fold_chain<I, B, F>(
    iter: I,
    init: B,
    f: F,
    s: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>,
    it: I,
    accs: thrust_models::model::Seq<<B as thrust_models::Model>::Ty>,
    fs: thrust_models::model::Seq<F>,
) -> bool
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
    B: thrust_models::Model,
    F: FnMut(B, I::Item) -> B,
{
    I::produces(iter, s, it)
        && accs.len() == s.len() + 1
        && fs.len() == s.len() + 1
        && accs[0] == init
        && fs[0] == f
        && thrust_macros::hist_inv!(f, fs[s.len()])
        && thrust_models::forall(|k: thrust_models::model::Int| !(0 <= k && k < s.len())
            || (thrust_macros::hist_inv!(f, fs[k])
                && thrust_macros::post!(thrust_models::model::Mut::new(fs[k], fs[k + 1])(accs[k], s[k]), accs[k + 1])))
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(
    I::inv(it)
        && thrust_models::forall(|s: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>,
                                  it1: <I as thrust_models::Model>::Ty,
                                  accs: thrust_models::model::Seq<<B as thrust_models::Model>::Ty>,
                                  fs: thrust_models::model::Seq<thrust_models::model::Closure<F>>,
                                  x: <I::Item as thrust_models::Model>::Ty,
                                  it2: <I as thrust_models::Model>::Ty|
            !(_iter_spec_fold_chain::<I, B, F>(it, init, f, s, it1, accs, fs)
                && I::produces(it1, thrust_models::model::Seq::singleton(x), it2))
                || thrust_macros::pre!(fs[s.len()](accs[s.len()], x)))
)]
#[thrust_macros::ensures(
    thrust_models::exists(|s: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>,
                           it1: <I as thrust_models::Model>::Ty,
                           accs: thrust_models::model::Seq<<B as thrust_models::Model>::Ty>,
                           fs: thrust_models::model::Seq<thrust_models::model::Closure<F>>,
                           it2: <I as thrust_models::Model>::Ty|
        _iter_spec_fold_chain::<I, B, F>(it, init, f, s, it1, accs, fs)
            && accs[s.len()] == result
            && I::completed(thrust_models::model::Mut::new(it1, it2)))
)]
fn _extern_spec_iterator_fold<I, B, F>(it: I, init: B, f: F) -> B
    where I: IteratorSpec,
          I::Item: thrust_models::Model,
          B: thrust_models::Model,
          F: FnMut(B, I::Item) -> B
{
    <I as std::iter::Iterator>::fold(it, init, f)
}

// `into_iter` is specified once, through `into_iter_is`; a type gets an `into_iter` by
// implementing the trait. An iterator is its own `into_iter`.
#[thrust_macros::context]
trait IntoIteratorSpec: std::iter::IntoIterator + thrust_models::Model
where
    Self::IntoIter: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: Self::IntoIter) -> bool;
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(I::into_iter_is(it, result))]
fn _extern_spec_into_iterator_into_iter<I>(it: I) -> I::IntoIter
    where I: IntoIteratorSpec,
          I::IntoIter: thrust_models::Model
{
    <I as std::iter::IntoIterator>::into_iter(it)
}

// `for` calls `into_iter` on the iterator it is given, which std's blanket
// `impl<I: Iterator> IntoIterator for I` defines as the identity (Creusot states the same,
// creusot-std/src/std/iter.rs).
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == it)]
fn _extern_spec_iterator_into_iter<I>(it: I) -> I
    where I: std::iter::Iterator + thrust_models::Model
{
    <I as std::iter::IntoIterator>::into_iter(it)
}

#[thrust_macros::context]
impl<I> IntoIteratorSpec for I
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: Self) -> bool {
        self == it
    }
}

#[thrust_macros::context]
impl<T> IntoIteratorSpec for Vec<T>
where
    T: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: std::vec::IntoIter<T>) -> bool {
        it.0 == self && it.1 == 0 && <std::vec::IntoIter<T> as IteratorSpec>::inv(it)
    }
}

#[thrust_macros::context]
impl<'a, T> IntoIteratorSpec for &'a Vec<T>
where
    T: thrust_models::Model + 'a,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: core::slice::Iter<'a, T>) -> bool {
        it.0 == *self && it.1 == 0 && <core::slice::Iter<'a, T> as IteratorSpec>::inv(it)
    }
}

#[thrust_macros::context]
impl<'a, T> IntoIteratorSpec for &'a mut Vec<T>
where
    T: thrust_models::Model + 'a,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: core::slice::IterMut<'a, T>) -> bool {
        it.0 == *self && it.1 == !self && it.2 == 0 && (!self).len() == (*self).len()
    }
}

#[thrust_macros::context]
impl<'a, T> IntoIteratorSpec for &'a [T]
where
    T: thrust_models::Model + 'a,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: core::slice::Iter<'a, T>) -> bool {
        it.0 == *self && it.1 == 0 && <core::slice::Iter<'a, T> as IteratorSpec>::inv(it)
    }
}

#[thrust_macros::context]
impl<'a, T> IntoIteratorSpec for &'a mut [T]
where
    T: thrust_models::Model + 'a,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: core::slice::IterMut<'a, T>) -> bool {
        it.0 == *self && it.1 == !self && it.2 == 0 && (!self).len() == (*self).len()
    }
}

#[thrust_macros::context]
impl<'a, T> IntoIteratorSpec for core::slice::IterMut<'a, T>
where
    T: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: Self) -> bool {
        self == it
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(A::into_iter_is(a, result.0) && B::into_iter_is(b, result.1))]
fn _extern_spec_iterator_zip<A, B>(a: A, b: B) -> core::iter::Zip<A::IntoIter, B::IntoIter>
    where A: IntoIteratorSpec,
          B: IntoIteratorSpec,
          A::IntoIter: IteratorSpec,
          B::IntoIter: IteratorSpec,
          A::Item: thrust_models::Model,
          B::Item: thrust_models::Model
{
    std::iter::zip(a, b)
}

// `vec![elem; n]` expands to a call to this function.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    result.len() == n
        && thrust_models::forall(|i: thrust_models::model::Int| (0 <= i && i < n) ==> result[i] == elem)
)]
fn _extern_spec_vec_from_elem<T>(elem: T, n: usize) -> Vec<T>
    where T: thrust_models::Model + Clone
{
    std::vec::from_elem(elem, n)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(at <= (*vec).len())]
#[thrust_macros::ensures(
    !vec == (*vec).subsequence(0, at) && result == (*vec).subsequence(at, (*vec).len())
)]
fn _extern_spec_vec_split_off<T>(vec: &mut Vec<T>, at: usize) -> Vec<T>
    where T: thrust_models::Model
{
    Vec::split_off(vec, at)
}

// Creusot's `Vec::extend` and `FromIterator::from_iter` (creusot-std src/std/vec.rs, whose
// `from_iter_post` is `prod == res@`, and src/std/iter.rs): the iterator runs from what
// `into_iter` gives to completion, and what it produced is appended (`extend`) or is the vector
// (`from_iter`, `collect`). Each step is `next`, which requires `inv`.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(
    thrust_models::forall(|it: <I::IntoIter as thrust_models::Model>::Ty|
        I::into_iter_is(iter, it) ==> <I::IntoIter as IteratorSpec>::inv(it))
)]
#[thrust_macros::ensures(
    thrust_models::exists(|it: <I::IntoIter as thrust_models::Model>::Ty,
                           prod: thrust_models::model::Seq<<T as thrust_models::Model>::Ty>,
                           done: <I::IntoIter as thrust_models::Model>::Ty,
                           fin: <I::IntoIter as thrust_models::Model>::Ty|
        I::into_iter_is(iter, it)
            && <I::IntoIter as IteratorSpec>::produces(it, prod, done)
            && <I::IntoIter as IteratorSpec>::completed(thrust_models::model::Mut::new(done, fin))
            && !vec == (*vec).concat(prod))
)]
fn _extern_spec_vec_extend<T, I>(vec: &mut Vec<T>, iter: I)
    where T: thrust_models::Model,
          I: IntoIteratorSpec<Item = T>, I::IntoIter: IteratorSpec
{
    <Vec<T> as std::iter::Extend<T>>::extend(vec, iter)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(
    thrust_models::forall(|it: <I::IntoIter as thrust_models::Model>::Ty|
        I::into_iter_is(iter, it) ==> <I::IntoIter as IteratorSpec>::inv(it))
)]
#[thrust_macros::ensures(
    thrust_models::exists(|it: <I::IntoIter as thrust_models::Model>::Ty,
                           done: <I::IntoIter as thrust_models::Model>::Ty,
                           fin: <I::IntoIter as thrust_models::Model>::Ty|
        I::into_iter_is(iter, it)
            && <I::IntoIter as IteratorSpec>::produces(it, result, done)
            && <I::IntoIter as IteratorSpec>::completed(thrust_models::model::Mut::new(done, fin)))
)]
fn _extern_spec_vec_from_iter<T, I>(iter: I) -> Vec<T>
    where T: thrust_models::Model,
          I: IntoIteratorSpec<Item = T>, I::IntoIter: IteratorSpec
{
    <Vec<T> as std::iter::FromIterator<T>>::from_iter(iter)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(I::inv(it))]
#[thrust_macros::ensures(
    thrust_models::exists(|done: <I as thrust_models::Model>::Ty, fin: <I as thrust_models::Model>::Ty|
        I::produces(it, result, done) && I::completed(thrust_models::model::Mut::new(done, fin)))
)]
fn _extern_spec_iterator_collect_vec<I, T>(it: I) -> Vec<T>
    where I: IteratorSpec<Item = T>,
          T: thrust_models::Model
{
    <I as std::iter::Iterator>::collect::<Vec<T>>(it)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == array)]
fn _extern_spec_array_into_vec<T, const N: usize>(array: [T; N]) -> Vec<T>
    where T: thrust_models::Model
{
    <[T; N] as Into<Vec<T>>>::into(array)
}

// TODO: The following specs of some trait methods are too restrictive; we should allow for a
//       per-impl spec once we can describe the spec of blanket impls.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*x == *y))]
fn _extern_spec_partialeq_eq<T>(x: &T, y: &T) -> bool
  where T: thrust_models::Model + thrust_models::ModelEq + PartialEq
{
    PartialEq::eq(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == !(*x == *y))]
fn _extern_spec_partialeq_ne<T>(x: &T, y: &T) -> bool
  where T: thrust_models::Model + thrust_models::ModelEq + PartialEq
{
    PartialEq::ne(x, y)
}

// `&mut A` compares the current values, as Creusot's deep model of `&mut T` is that of `*self`.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (**x == **y))]
fn _extern_spec_mut_ref_partialeq_eq<'a, 'b, A>(x: &&'a mut A, y: &&'b mut A) -> bool
  where A: thrust_models::Model + thrust_models::ModelEq + PartialEq
{
    <&'a mut A as PartialEq<&'b mut A>>::eq(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == !(**x == **y))]
fn _extern_spec_mut_ref_partialeq_ne<'a, 'b, A>(x: &&'a mut A, y: &&'b mut A) -> bool
  where A: thrust_models::Model + thrust_models::ModelEq + PartialEq
{
    <&'a mut A as PartialEq<&'b mut A>>::ne(x, y)
}

// Hashing has no model; the spec only records that hashing itself does not
// panic, which lets derived Hash impls be analyzed (they hash field by field).
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn _extern_spec_hash<T, H>(x: &T, state: &mut H)
  where T: std::hash::Hash + thrust_models::Model + ?Sized, H: std::hash::Hasher + thrust_models::Model
{
    std::hash::Hash::hash(x, state)
}

// `assert_receiver_is_total_eq` exists for the type check of `#[derive(Eq)]`: its default body and
// the derived one do nothing at run time.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn _extern_spec_assert_receiver_is_total_eq<T>(x: &T)
  where T: Eq + thrust_models::Model + ?Sized, T::Ty: PartialEq
{
    Eq::assert_receiver_is_total_eq(x)
}

// The hasher's `write*` methods are called by foreign `hash` impls, so a local hasher is checked
// against these.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn _extern_spec_hasher_write<H>(state: &mut H, bytes: &[u8])
  where H: std::hash::Hasher + thrust_models::Model
{
    std::hash::Hasher::write(state, bytes)
}

macro_rules! extern_spec_hasher_write_int {
    ($($spec:ident $method:ident $ty:ty,)*) => {
        $(
            #[thrust::extern_spec_fn]
            #[thrust_macros::requires(true)]
            #[thrust_macros::ensures(true)]
            fn $spec<H>(state: &mut H, i: $ty)
              where H: std::hash::Hasher + thrust_models::Model
            {
                std::hash::Hasher::$method(state, i)
            }
        )*
    };
}

extern_spec_hasher_write_int! {
    _extern_spec_hasher_write_u8 write_u8 u8,
    _extern_spec_hasher_write_u16 write_u16 u16,
    _extern_spec_hasher_write_u32 write_u32 u32,
    _extern_spec_hasher_write_u64 write_u64 u64,
    _extern_spec_hasher_write_u128 write_u128 u128,
    _extern_spec_hasher_write_usize write_usize usize,
    _extern_spec_hasher_write_i8 write_i8 i8,
    _extern_spec_hasher_write_i16 write_i16 i16,
    _extern_spec_hasher_write_i32 write_i32 i32,
    _extern_spec_hasher_write_i64 write_i64 i64,
    _extern_spec_hasher_write_i128 write_i128 i128,
    _extern_spec_hasher_write_isize write_isize isize,
}

// Default values of foreign types are not modeled; the spec only records that
// constructing one does not panic, which lets derived Default impls be analyzed.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn _extern_spec_default<T>() -> T
  where T: Default + thrust_models::Model
{
    T::default()
}

// Values are modeled purely, so a clone is the same value in the model.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == *x)]
fn _extern_spec_clone<T>(x: &T) -> T
  where T: thrust_models::Model + Clone
{
    Clone::clone(x)
}

// Comparison is specified through `PartialOrdSpec`, which relates two values to the outcome of
// comparing them. A type gets the specs of `partial_cmp`, the comparison operators, `cmp`, `max`
// and `min` by implementing it, as Creusot's `OrdLogic` does with `cmp_log`; the relation must
// be functional, and `Ord` types must agree with `partial_cmp`, as std requires. A type with a
// derived `PartialOrd` and no impl has the derive's lexicographic order (`analyze::derive`).
#[thrust_macros::context]
#[thrust::def::partial_ord_spec]
trait PartialOrdSpec: PartialOrd + thrust_models::Model {
    #[thrust_macros::predicate]
    fn compares(self, other: Self, ord: Option<std::cmp::Ordering>) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::compares(*a, *b, x) && Self::compares(*a, *b, y))]
    #[thrust_macros::ensures(x == y)]
    fn compares_functional(
        a: &Self,
        b: &Self,
        x: Option<std::cmp::Ordering>,
        y: Option<std::cmp::Ordering>,
    );
}

macro_rules! int_partial_ord_spec {
    ($T:ty) => {
        #[thrust_macros::context]
        impl PartialOrdSpec for $T {
            #[thrust_macros::predicate]
            fn compares(self, other: Self, ord: Option<std::cmp::Ordering>) -> bool {
                (self < other && ord == Some(std::cmp::Ordering::Less))
                    || (self == other && ord == Some(std::cmp::Ordering::Equal))
                    || (self > other && ord == Some(std::cmp::Ordering::Greater))
            }

            fn compares_functional(
                a: &Self,
                b: &Self,
                x: Option<std::cmp::Ordering>,
                y: Option<std::cmp::Ordering>,
            ) {
            }
        }
    };
}

int_partial_ord_spec!(isize);
int_partial_ord_spec!(i8);
int_partial_ord_spec!(i16);
int_partial_ord_spec!(i32);
int_partial_ord_spec!(i64);
int_partial_ord_spec!(i128);
int_partial_ord_spec!(usize);
int_partial_ord_spec!(u8);
int_partial_ord_spec!(u16);
int_partial_ord_spec!(u32);
int_partial_ord_spec!(u64);
int_partial_ord_spec!(u128);

// `&A` compares its referents.
#[thrust_macros::context]
impl<A> PartialOrdSpec for &A
where
    A: PartialOrdSpec,
{
    #[thrust_macros::predicate]
    fn compares(self, other: Self, ord: Option<std::cmp::Ordering>) -> bool {
        A::compares(*self, *other, ord)
    }

    fn compares_functional(
        a: &Self,
        b: &Self,
        x: Option<std::cmp::Ordering>,
        y: Option<std::cmp::Ordering>,
    ) {
    }
}

// `Option<A>` orders `None` below every `Some`, and two `Some`s by their contents (the derived
// order).
#[thrust_macros::context]
impl<A> PartialOrdSpec for Option<A>
where
    A: PartialOrdSpec,
{
    #[thrust_macros::predicate]
    fn compares(self, other: Self, ord: Option<std::cmp::Ordering>) -> bool {
        (self == None && other == None && ord == Some(std::cmp::Ordering::Equal))
            || (self == None && other != None && ord == Some(std::cmp::Ordering::Less))
            || (self != None && other == None && ord == Some(std::cmp::Ordering::Greater))
            || thrust_models::exists(|a: A::Ty, b: A::Ty|
                self == Some(a) && other == Some(b) && A::compares(a, b, ord))
    }

    fn compares_functional(
        a: &Self,
        b: &Self,
        x: Option<std::cmp::Ordering>,
        y: Option<std::cmp::Ordering>,
    ) {
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(T::compares(*x, *y, result))]
fn _extern_spec_partialord_partial_cmp<T>(x: &T, y: &T) -> Option<std::cmp::Ordering>
    where T: PartialOrdSpec
{
    PartialOrd::partial_cmp(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((result ==> T::compares(*x, *y, Some(std::cmp::Ordering::Less))) && (T::compares(*x, *y, Some(std::cmp::Ordering::Less)) ==> result))]
fn _extern_spec_partialord_lt<T>(x: &T, y: &T) -> bool
    where T: PartialOrdSpec
{
    PartialOrd::lt(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((result ==> T::compares(*x, *y, Some(std::cmp::Ordering::Less)) || T::compares(*x, *y, Some(std::cmp::Ordering::Equal))) && ((T::compares(*x, *y, Some(std::cmp::Ordering::Less)) || T::compares(*x, *y, Some(std::cmp::Ordering::Equal))) ==> result))]
fn _extern_spec_partialord_le<T>(x: &T, y: &T) -> bool
    where T: PartialOrdSpec
{
    PartialOrd::le(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((result ==> T::compares(*x, *y, Some(std::cmp::Ordering::Greater))) && (T::compares(*x, *y, Some(std::cmp::Ordering::Greater)) ==> result))]
fn _extern_spec_partialord_gt<T>(x: &T, y: &T) -> bool
    where T: PartialOrdSpec
{
    PartialOrd::gt(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((result ==> T::compares(*x, *y, Some(std::cmp::Ordering::Greater)) || T::compares(*x, *y, Some(std::cmp::Ordering::Equal))) && ((T::compares(*x, *y, Some(std::cmp::Ordering::Greater)) || T::compares(*x, *y, Some(std::cmp::Ordering::Equal))) ==> result))]
fn _extern_spec_partialord_ge<T>(x: &T, y: &T) -> bool
    where T: PartialOrdSpec
{
    PartialOrd::ge(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(T::compares(*x, *y, Some(result)))]
fn _extern_spec_ord_cmp<T>(x: &T, y: &T) -> std::cmp::Ordering
    where T: Ord + PartialOrdSpec
{
    Ord::cmp(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (T::compares(x, y, Some(std::cmp::Ordering::Greater)) ==> result == x) && (!T::compares(x, y, Some(std::cmp::Ordering::Greater)) ==> result == y)
)]
fn _extern_spec_ord_max<T>(x: T, y: T) -> T
    where T: Ord + PartialOrdSpec
{
    Ord::max(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (T::compares(x, y, Some(std::cmp::Ordering::Greater)) ==> result == y) && (!T::compares(x, y, Some(std::cmp::Ordering::Greater)) ==> result == x)
)]
fn _extern_spec_ord_min<T>(x: T, y: T) -> T
    where T: Ord + PartialOrdSpec
{
    Ord::min(x, y)
}
