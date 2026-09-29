// This file is injected to source code by Thrust

mod thrust_models {
    pub trait Model {
        #[thrust::def::model_ty]
        type Ty;
    }

    pub mod model {
        use std::marker::PhantomData;

        #[thrust::def::int_model]
        pub struct Int;

        impl<T> PartialEq<T> for Int where T: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn eq(&self, _other: &T) -> bool {
                unimplemented!()
            }
        }

        impl<T> PartialOrd<T> for Int where T: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn partial_cmp(&self, _other: &T) -> Option<std::cmp::Ordering> {
                unimplemented!()
            }
        }

        impl<T> std::ops::Add<T> for Int where T: super::Model<Ty = Self> {
            type Output = Self;

            #[thrust::ignored]
            fn add(self, _rhs: T) -> Self::Output {
                unimplemented!()
            }
        }

        impl<T> std::ops::Sub<T> for Int where T: super::Model<Ty = Self> {
            type Output = Self;

            #[thrust::ignored]
            fn sub(self, _rhs: T) -> Self::Output {
                unimplemented!()
            }
        }

        impl<T> std::ops::Mul<T> for Int where T: super::Model<Ty = Self> {
            type Output = Self;

            #[thrust::ignored]
            fn mul(self, _rhs: T) -> Self::Output {
                unimplemented!()
            }
        }

        impl<T> std::ops::Div<T> for Int where T: super::Model<Ty = Self> {
            type Output = Self;

            #[thrust::ignored]
            fn div(self, _rhs: T) -> Self::Output {
                unimplemented!()
            }
        }

        impl<T> std::ops::Rem<T> for Int where T: super::Model<Ty = Self> {
            type Output = Self;

            #[thrust::ignored]
            fn rem(self, _rhs: T) -> Self::Output {
                unimplemented!()
            }
        }

        impl std::ops::Neg for Int {
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

        impl<I, T, U> std::ops::Index<U> for Array<I, T> where U: super::Model<Ty = I> {
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
            pub fn store<U>(&self, _index: U, _value: T) -> Self where U: super::Model<Ty = I> {
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

        #[thrust::def::seq_model]
        pub struct Seq<T: ?Sized>(PhantomData<T>);

        impl<T, U> PartialEq<U> for Seq<T> where U: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn eq(&self, _other: &U) -> bool {
                unimplemented!()
            }
        }

        impl<T, U> std::ops::Index<U> for Seq<T> where U: super::Model<Ty = Int> {
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

            #[allow(dead_code)]
            #[thrust::def::seq_len]
            #[thrust::ignored]
            pub fn len(&self) -> Int {
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
                U: super::Model<Ty = Int>,
            {
                unimplemented!()
            }

            #[allow(dead_code)]
            #[thrust::def::seq_subsequence]
            #[thrust::ignored]
            pub fn subsequence<U, V>(self, _start: U, _end: V) -> Self
            where
                U: super::Model<Ty = Int>,
                V: super::Model<Ty = Int>,
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

    macro_rules! int_model {
        ($T:ty) => {
            impl Model for $T {
                type Ty = model::Int;
            }

            impl PartialEq<model::Int> for $T {
                #[thrust::ignored]
                fn eq(&self, _other: &model::Int) -> bool {
                    unimplemented!()
                }
            }

            impl PartialOrd<model::Int> for $T {
                #[thrust::ignored]
                fn partial_cmp(&self, _other: &model::Int) -> Option<std::cmp::Ordering> {
                    unimplemented!()
                }
            }

            impl std::ops::Add<model::Int> for $T {
                type Output = model::Int;

                #[thrust::ignored]
                fn add(self, _rhs: model::Int) -> Self::Output {
                    unimplemented!()
                }
            }

            impl std::ops::Sub<model::Int> for $T {
                type Output = model::Int;

                #[thrust::ignored]
                fn sub(self, _rhs: model::Int) -> Self::Output {
                    unimplemented!()
                }
            }

            impl std::ops::Mul<model::Int> for $T {
                type Output = model::Int;

                #[thrust::ignored]
                fn mul(self, _rhs: model::Int) -> Self::Output {
                    unimplemented!()
                }
            }

            impl std::ops::Div<model::Int> for $T {
                type Output = model::Int;

                #[thrust::ignored]
                fn div(self, _rhs: model::Int) -> Self::Output {
                    unimplemented!()
                }
            }

            impl std::ops::Rem<model::Int> for $T {
                type Output = model::Int;

                #[thrust::ignored]
                fn rem(self, _rhs: model::Int) -> Self::Output {
                    unimplemented!()
                }
            }
        };
    }

    int_model!(isize);
    int_model!(i32);
    int_model!(i64);
    int_model!(usize);
    int_model!(u32);
    int_model!(u64);
    int_model!(i8);
    int_model!(i16);
    int_model!(i128);
    int_model!(u8);
    int_model!(u16);
    int_model!(u128);

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
        type Ty = (<I as Model>::Ty, model::Int);
    }

    // The two iterators it wraps, in the order of the arguments to `zip`.
    impl<A, B> Model for core::iter::Zip<A, B> where A: Model, B: Model {
        type Ty = (<A as Model>::Ty, <B as Model>::Ty);
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

    #[thrust::def::invariant_marker]
    #[thrust::ignored]
    #[inline(never)]
    pub fn __invariant_marker<F>(_f: F) {
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
    // surface type. These two impls let a formula use such a field as its content too:
    // `Deref` for method calls and `*g`, `PartialEq` for `==`. In the logic both are the
    // identity on the content, as the `ghost_model` arm of `model_adt` has it.
    impl<T: ?Sized> std::ops::Deref for Ghost<T> where T: Model {
        type Target = <T as Model>::Ty;

        #[thrust::ignored]
        fn deref(&self) -> &Self::Target {
            unimplemented!()
        }
    }

    impl<T: ?Sized, U> PartialEq<U> for Ghost<T> where T: Model, U: Model<Ty = <T as Model>::Ty> {
        #[thrust::ignored]
        fn eq(&self, _other: &U) -> bool {
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
fn _extern_spec_box_new<T>(x: T) -> Box<T> where T: thrust_models::Model, T::Ty: PartialEq {
    Box::new(x)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (x == y))]
fn _extern_spec_box_partialeq_eq<T>(x: &Box<T>, y: &Box<T>) -> bool
  where T: thrust_models::Model + PartialEq, T::Ty: PartialEq
{
    <Box<T> as PartialEq>::eq(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*x == !y && *y == !x)]
fn _extern_spec_std_mem_swap<T>(x: &mut T, y: &mut T) where T: thrust_models::Model, T::Ty: PartialEq {
    std::mem::swap(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!dest == src && result == *dest)]
fn _extern_spec_std_mem_replace<T>(dest: &mut T, src: T) -> T where T: thrust_models::Model, T::Ty: PartialEq {
    std::mem::replace(dest, src)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (x == y))]
fn _extern_spec_option_partialeq_eq<T>(x: &Option<T>, y: &Option<T>) -> bool
  where T: thrust_models::Model + PartialEq, T::Ty: PartialEq
{
    <Option<T> as PartialEq>::eq(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(opt != None)]
#[thrust_macros::ensures(Some(result) == opt)]
fn _extern_spec_option_unwrap<T>(opt: Option<T>) -> T where T: thrust_models::Model, T::Ty: PartialEq {
    Option::unwrap(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*opt == None && result == true)
    || (*opt != None && result == false)
)]
fn _extern_spec_option_is_none<T>(opt: &Option<T>) -> bool where T: thrust_models::Model, T::Ty: PartialEq {
    Option::is_none(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*opt == None && result == false)
    || (*opt != None && result == true)
)]
fn _extern_spec_option_is_some<T>(opt: &Option<T>) -> bool where T: thrust_models::Model, T::Ty: PartialEq {
    Option::is_some(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (opt != None && Some(result) == opt)
    || (opt == None && result == default)
)]
fn _extern_spec_option_unwrap_or<T>(opt: Option<T>, default: T) -> T where T: thrust_models::Model, T::Ty: PartialEq {
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
    T: thrust_models::Model, T::Ty: PartialEq,
    U: thrust_models::Model, U::Ty: PartialEq,
    F: FnOnce(T) -> U,
{
    Option::map(opt, f)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(opt != None || thrust_macros::pre!(f()))]
#[thrust_macros::ensures(
    (opt != None && Some(result) == opt)
    || (opt == None && thrust_macros::post!(f(), result))
)]
fn _extern_spec_option_unwrap_or_else<T, F>(opt: Option<T>, f: F) -> T
where
    T: thrust_models::Model, T::Ty: PartialEq,
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
    where T: thrust_models::Model, T::Ty: PartialEq,
          E: thrust_models::Model, E::Ty: PartialEq,
{
    Option::ok_or(opt, err)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!opt == None && result == *opt)]
fn _extern_spec_option_take<T>(opt: &mut Option<T>) -> Option<T> where T: thrust_models::Model, T::Ty: PartialEq {
    Option::take(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!opt == Some(src) && result == *opt)]
fn _extern_spec_option_replace<T>(opt: &mut Option<T>, src: T) -> Option<T>
    where T: thrust_models::Model, T::Ty: PartialEq
{
    Option::replace(opt, src)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x| opt == &Some(x) && result == Some(&x))
    || (opt == &None && result == None)
)]
fn _extern_spec_option_as_ref<T>(opt: &Option<T>) -> Option<&T> where T: thrust_models::Model, T::Ty: PartialEq {
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
  where T: thrust_models::Model, T::Ty: PartialEq
{
    Option::as_mut(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x| opt == Some(x) && result == std::ops::ControlFlow::Continue(x))
    || (opt == None && result == std::ops::ControlFlow::Break(None))
)]
fn _extern_spec_option_branch<T>(opt: Option<T>) -> std::ops::ControlFlow<Option<std::convert::Infallible>, T>
    where T: thrust_models::Model, T::Ty: PartialEq,
{
    <Option<T> as std::ops::Try>::branch(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == None)]
fn _extern_spec_option_from_residual<T>(residual: Option<std::convert::Infallible>) -> Option<T>
    where T: thrust_models::Model, T::Ty: PartialEq,
{
    <Option<T> as std::ops::FromResidual<Option<std::convert::Infallible>>>::from_residual(residual)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x| res == Ok(x) && result == std::ops::ControlFlow::Continue(x))
    || thrust_models::exists(|e| res == Err(e) && result == std::ops::ControlFlow::Break(Err(e)))
)]
fn _extern_spec_result_branch<T, E>(res: Result<T, E>) -> std::ops::ControlFlow<Result<std::convert::Infallible, E>, T>
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
{
    <Result<T, E> as std::ops::Try>::branch(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(thrust_models::exists(|f| result == Err(f)))]
fn _extern_spec_result_from_residual<T, E, F: From<E>>(residual: Result<std::convert::Infallible, E>) -> Result<T, F>
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
        F: thrust_models::Model, F::Ty: PartialEq,
{
    <Result<T, F> as std::ops::FromResidual<Result<std::convert::Infallible, E>>>::from_residual(residual)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == value)]
fn _extern_spec_from_identity<T>(value: T) -> T
    where T: thrust_models::Model, T::Ty: PartialEq,
{
    <T as From<T>>::from(value)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (x == y))]
fn _extern_spec_result_partialeq_eq<T, E>(x: &Result<T, E>, y: &Result<T, E>) -> bool
  where T: thrust_models::Model + PartialEq, T::Ty: PartialEq,
        E: thrust_models::Model + PartialEq, E::Ty: PartialEq,
{
    <Result<T, E> as PartialEq>::eq(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(thrust_models::exists(|x| res == Ok(x)))]
#[thrust_macros::ensures(Ok(result) == res)]
fn _extern_spec_result_unwrap<T, E: std::fmt::Debug>(res: Result<T, E>) -> T
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
{
    Result::unwrap(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(thrust_models::exists(|x| res == Err(x)))]
#[thrust_macros::ensures(Err(result) == res)]
fn _extern_spec_result_unwrap_err<T: std::fmt::Debug, E>(res: Result<T, E>) -> E
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
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
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
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
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
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
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
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
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
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

// The comparisons of primitive integers, which derived `PartialOrd` / `Ord` impls call on
// their fields. The integers define their own `lt`, `le`, `gt` and `ge`, which compare by value.
macro_rules! int_cmp_specs {
    ($T:ty) => {
        const _: () = {
            #[thrust::extern_spec_fn]
            #[thrust_macros::requires(true)]
            #[thrust_macros::ensures(
                (*x < *y && result == Some(std::cmp::Ordering::Less))
                || (*x == *y && result == Some(std::cmp::Ordering::Equal))
                || (*x > *y && result == Some(std::cmp::Ordering::Greater))
            )]
            fn partial_cmp(x: &$T, y: &$T) -> Option<std::cmp::Ordering> {
                <$T as PartialOrd>::partial_cmp(x, y)
            }

            #[thrust::extern_spec_fn]
            #[thrust_macros::requires(true)]
            #[thrust_macros::ensures(
                (*x < *y && result == std::cmp::Ordering::Less)
                || (*x == *y && result == std::cmp::Ordering::Equal)
                || (*x > *y && result == std::cmp::Ordering::Greater)
            )]
            fn cmp(x: &$T, y: &$T) -> std::cmp::Ordering {
                <$T as Ord>::cmp(x, y)
            }

            #[thrust::extern_spec_fn]
            #[thrust_macros::requires(true)]
            #[thrust_macros::ensures(result == (*x < *y))]
            fn lt(x: &$T, y: &$T) -> bool {
                <$T as PartialOrd>::lt(x, y)
            }

            #[thrust::extern_spec_fn]
            #[thrust_macros::requires(true)]
            #[thrust_macros::ensures(result == (*x <= *y))]
            fn le(x: &$T, y: &$T) -> bool {
                <$T as PartialOrd>::le(x, y)
            }

            #[thrust::extern_spec_fn]
            #[thrust_macros::requires(true)]
            #[thrust_macros::ensures(result == (*x > *y))]
            fn gt(x: &$T, y: &$T) -> bool {
                <$T as PartialOrd>::gt(x, y)
            }

            #[thrust::extern_spec_fn]
            #[thrust_macros::requires(true)]
            #[thrust_macros::ensures(result == (*x >= *y))]
            fn ge(x: &$T, y: &$T) -> bool {
                <$T as PartialOrd>::ge(x, y)
            }
        };
    };
}

int_cmp_specs!(isize);
int_cmp_specs!(i8);
int_cmp_specs!(i16);
int_cmp_specs!(i32);
int_cmp_specs!(i64);
int_cmp_specs!(i128);
int_cmp_specs!(usize);
int_cmp_specs!(u8);
int_cmp_specs!(u16);
int_cmp_specs!(u32);
int_cmp_specs!(u64);
int_cmp_specs!(u128);

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
trait TryIntoSpec<U>: TryInto<U> + thrust_models::Model
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
fn _extern_spec_try_into<T, U>(value: T) -> Result<U, <T as TryInto<U>>::Error>
    where T: TryIntoSpec<U>, T::Ty: PartialEq,
          U: thrust_models::Model, U::Ty: PartialEq,
          <T as TryInto<U>>::Error: thrust_models::Model,
          <<T as TryInto<U>>::Error as thrust_models::Model>::Ty: PartialEq,
{
    <T as TryInto<U>>::try_into(value)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (T::fits(value) && thrust_models::exists(|x| result == Ok(x) && T::converts_to(value, x)))
    || (!T::fits(value) && thrust_models::exists(|e| result == Err(e)))
)]
fn _extern_spec_try_from<T, U>(value: T) -> Result<U, <U as TryFrom<T>>::Error>
    where T: TryIntoSpec<U>, T::Ty: PartialEq,
          U: TryFrom<T> + thrust_models::Model, U::Ty: PartialEq,
          <U as TryFrom<T>>::Error: thrust_models::Model,
          <<U as TryFrom<T>>::Error as thrust_models::Model>::Ty: PartialEq,
{
    <U as TryFrom<T>>::try_from(value)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == 0)]
fn _extern_spec_vec_new<T>() -> Vec<T> where T: thrust_models::Model, T::Ty: PartialEq {
    Vec::<T>::new()
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!vec == (*vec).push(elem))]
fn _extern_spec_vec_push<T>(vec: &mut Vec<T>, elem: T)
    where T: thrust_models::Model, T::Ty: PartialEq
{
    Vec::push(vec, elem)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*vec).len())]
fn _extern_spec_vec_len<T>(vec: &Vec<T>) -> usize where T: thrust_models::Model, T::Ty: PartialEq {
    Vec::len(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(I::in_bounds(index, *vec))]
#[thrust_macros::ensures(I::has_value(index, *vec, *result))]
fn _extern_spec_vec_index<T, I>(vec: &Vec<T>, index: I) -> &<I as std::slice::SliceIndex<[T]>>::Output
    where T: thrust_models::Model, T::Ty: PartialEq,
          I: SliceIndexSpec<T>,
          <I as std::slice::SliceIndex<[T]>>::Output: thrust_models::Model,
          <<I as std::slice::SliceIndex<[T]>>::Output as thrust_models::Model>::Ty: PartialEq,
          I::Ty: PartialEq
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
    where T: thrust_models::Model, T::Ty: PartialEq,
          I: SliceIndexSpec<T>,
          <I as std::slice::SliceIndex<[T]>>::Output: thrust_models::Model,
          <<I as std::slice::SliceIndex<[T]>>::Output as thrust_models::Model>::Ty: PartialEq,
          I::Ty: PartialEq
{
    <Vec<T> as std::ops::IndexMut<I>>::index_mut(vec, index)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((!vec).len() == 0)]
fn _extern_spec_vec_clear<T>(vec: &mut Vec<T>) where T: thrust_models::Model, T::Ty: PartialEq {
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
fn _extern_spec_vec_pop<T>(vec: &mut Vec<T>) -> Option<T> where T: thrust_models::Model, T::Ty: PartialEq {
    Vec::pop(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == ((*vec).len() == 0))]
fn _extern_spec_vec_is_empty<T>(vec: &Vec<T>) -> bool where T: thrust_models::Model, T::Ty: PartialEq {
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
    where T: thrust_models::Model, T::Ty: PartialEq,
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
fn _extern_spec_vec_truncate<T>(vec: &mut Vec<T>, len: usize) where T: thrust_models::Model, T::Ty: PartialEq {
    Vec::truncate(vec, len)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*result == *vec)]
fn _extern_spec_vec_as_slice<T>(vec: &Vec<T>) -> &[T]
    where T: thrust_models::Model, T::Ty: PartialEq
{
    Vec::as_slice(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*result == *vec)]
fn _extern_spec_vec_deref<T>(vec: &Vec<T>) -> &[T]
    where T: thrust_models::Model, T::Ty: PartialEq
{
    <Vec<T> as std::ops::Deref>::deref(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*result == *vec && !result == !vec)]
fn _extern_spec_vec_deref_mut<T>(vec: &mut Vec<T>) -> &mut [T]
    where T: thrust_models::Model, T::Ty: PartialEq
{
    <Vec<T> as std::ops::DerefMut>::deref_mut(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*result == *vec)]
fn _extern_spec_vec_as_ref<T>(vec: &Vec<T>) -> &[T]
    where T: thrust_models::Model, T::Ty: PartialEq
{
    <Vec<T> as AsRef<[T]>>::as_ref(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*slice).len())]
fn _extern_spec_slice_len<T>(slice: &[T]) -> usize
    where T: thrust_models::Model, T::Ty: PartialEq
{
    <[T]>::len(slice)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == ((*slice).len() == 0))]
fn _extern_spec_slice_is_empty<T>(slice: &[T]) -> bool
    where T: thrust_models::Model, T::Ty: PartialEq
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
    where T: thrust_models::Model, T::Ty: PartialEq
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
    where T: thrust_models::Model, T::Ty: PartialEq
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
    where T: thrust_models::Model, T::Ty: PartialEq
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
    where T: thrust_models::Model, T::Ty: PartialEq
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
    where T: thrust_models::Model, T::Ty: PartialEq
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
    where T: thrust_models::Model, T::Ty: PartialEq
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
    where T: thrust_models::Model, T::Ty: PartialEq
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
    where T: thrust_models::Model, T::Ty: PartialEq
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
    where T: thrust_models::Model, T::Ty: PartialEq
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
    where T: thrust_models::Model, T::Ty: PartialEq
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
    where T: thrust_models::Model, T::Ty: PartialEq,
          I: SliceIndexSpec<T>,
          <I as std::slice::SliceIndex<[T]>>::Output: thrust_models::Model,
          <<I as std::slice::SliceIndex<[T]>>::Output as thrust_models::Model>::Ty: PartialEq,
          I::Ty: PartialEq
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
    where T: thrust_models::Model, T::Ty: PartialEq,
          I: SliceIndexSpec<T>,
          <I as std::slice::SliceIndex<[T]>>::Output: thrust_models::Model,
          <<I as std::slice::SliceIndex<[T]>>::Output as thrust_models::Model>::Ty: PartialEq,
          I::Ty: PartialEq
{
    <[T] as std::ops::IndexMut<I>>::index_mut(slice, index)
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
    where T: thrust_models::Model, T::Ty: PartialEq
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
        && <core::slice::IterMut<'_, T> as IteratorSpec>::inv(result)
)]
fn _extern_spec_slice_iter_mut<T>(slice: &mut [T]) -> core::slice::IterMut<'_, T>
    where T: thrust_models::Model, T::Ty: PartialEq
{
    <[T]>::iter_mut(slice)
}

// `next` is specified once, through the predicates of `IteratorSpec`; a type gets a `next` by
// implementing the trait. `next` is total: `completed` covers every position at or past the end.
// `inv` is the state invariant, Creusot's type invariant: `produces_refl` holds at the states that
// satisfy it. The laws are Creusot's; they let a loop over a type parameter accumulate what
// `next` produced.
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
    fn produces_refl(a: &Self)
    where
        <Self::Item as thrust_models::Model>::Ty: PartialEq;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b) && Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    )
    where
        <Self::Item as thrust_models::Model>::Ty: PartialEq;
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (I::inv(*it) ==> I::inv(!it))
        && (result == None ==> I::completed(it))
        && thrust_models::forall(|x: <I::Item as thrust_models::Model>::Ty| result == Some(x)
            ==> I::produces(*it, thrust_models::model::Seq::singleton(x), !it))
)]
fn _extern_spec_iterator_next<I>(it: &mut I) -> Option<I::Item>
    where I: IteratorSpec,
          I::Item: thrust_models::Model,
          I::Ty: PartialEq,
          <I::Item as thrust_models::Model>::Ty: PartialEq
{
    <I as std::iter::Iterator>::next(it)
}

// The predicate accepted the item found in some state of it; which state, and that it rejected
// the items before, is not stated: that needs the sequence of its states across the calls, on
// which PCSat fails.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(
    thrust_models::forall(|c: thrust_models::model::Closure<P>|
        thrust_models::forall(|x: <I::Item as thrust_models::Model>::Ty| thrust_macros::pre!(c(&x))))
)]
#[thrust_macros::ensures(
    (result == None
        && thrust_models::exists(|visited: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>, mid: I::Ty|
            I::produces(*it, visited, mid) && I::completed(thrust_models::model::Mut::new(mid, !it))))
    || thrust_models::exists(|visited: thrust_models::model::Seq<<I::Item as thrust_models::Model>::Ty>,
                              x: <I::Item as thrust_models::Model>::Ty|
        result == Some(x)
            && I::produces(*it, visited.push(x), !it)
            && thrust_models::exists(|c: thrust_models::model::Closure<P>, d: thrust_models::model::Closure<P>|
                thrust_macros::post!(thrust_models::model::Mut::new(c, d)(&x), true)))
)]
fn _extern_spec_iterator_find<I, P>(it: &mut I, predicate: P) -> Option<I::Item>
    where I: IteratorSpec,
          I::Item: thrust_models::Model,
          I::Ty: PartialEq,
          <I::Item as thrust_models::Model>::Ty: PartialEq,
          P: FnMut(&I::Item) -> bool
{
    <I as std::iter::Iterator>::find(it, predicate)
}

#[thrust_macros::context]
impl<'a, T> IteratorSpec for core::slice::Iter<'a, T>
where
    T: thrust_models::Model,
    T::Ty: PartialEq,
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

// The element handed out is the `Mut` pair of the current and final sequences at the cursor. The
// tail the loop has not reached yet keeps its prophecy unconstrained, so dropping the iterator
// early leaves the caller unable to say the untouched elements are unchanged; running it to
// exhaustion is what the specification supports.
#[thrust_macros::context]
impl<'a, T> IteratorSpec for core::slice::IterMut<'a, T>
where
    T: thrust_models::Model,
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        self.2 <= self.0.len()
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<&'a mut T>, o: Self) -> bool {
        self.0 == o.0
            && self.1 == o.1
            && self.2 <= o.2
            && o.2 <= self.0.len()
            && visited.len() == o.2 - self.2
            && thrust_models::forall(|i: thrust_models::model::Int|
                !(0 <= i && i < visited.len()) || visited[i] == thrust_models::model::Mut::new(
                    self.0[self.2 + i],
                    self.1[self.2 + i],
                ))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).2 >= (*self).0.len() && *self == !self
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
    T::Ty: PartialEq,
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
    I::Ty: PartialEq,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
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
                    && thrust_models::forall(|i: thrust_models::model::Int|
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
          I::Item: thrust_models::Model,
          I::Ty: PartialEq,
          <I::Item as thrust_models::Model>::Ty: PartialEq
{
    <I as std::iter::Iterator>::enumerate(it)
}

#[thrust_macros::context]
impl<A, B> IteratorSpec for core::iter::Zip<A, B>
where
    A: IteratorSpec,
    B: IteratorSpec,
    A::Item: thrust_models::Model,
    B::Item: thrust_models::Model,
    A::Ty: PartialEq,
    B::Ty: PartialEq,
    <A::Item as thrust_models::Model>::Ty: PartialEq,
    <B::Item as thrust_models::Model>::Ty: PartialEq,
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
          I::IntoIter: thrust_models::Model,
          I::Ty: PartialEq,
          <I::IntoIter as thrust_models::Model>::Ty: PartialEq
{
    <I as std::iter::IntoIterator>::into_iter(it)
}

#[thrust_macros::context]
impl<T> IntoIteratorSpec for Vec<T>
where
    T: thrust_models::Model,
    T::Ty: PartialEq,
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
    T::Ty: PartialEq,
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
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: core::slice::IterMut<'a, T>) -> bool {
        it.0 == *self && it.1 == !self && it.2 == 0 && (!self).len() == (*self).len()
            && <core::slice::IterMut<'a, T> as IteratorSpec>::inv(it)
    }
}

#[thrust_macros::context]
impl<'a, T> IntoIteratorSpec for &'a [T]
where
    T: thrust_models::Model + 'a,
    T::Ty: PartialEq,
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
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: core::slice::IterMut<'a, T>) -> bool {
        it.0 == *self && it.1 == !self && it.2 == 0 && (!self).len() == (*self).len()
            && <core::slice::IterMut<'a, T> as IteratorSpec>::inv(it)
    }
}

#[thrust_macros::context]
impl<'a, T> IntoIteratorSpec for core::slice::Iter<'a, T>
where
    T: thrust_models::Model,
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: Self) -> bool {
        self == it
    }
}

#[thrust_macros::context]
impl<'a, T> IntoIteratorSpec for core::slice::IterMut<'a, T>
where
    T: thrust_models::Model,
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: Self) -> bool {
        self == it
    }
}

#[thrust_macros::context]
impl<T> IntoIteratorSpec for std::vec::IntoIter<T>
where
    T: thrust_models::Model,
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: Self) -> bool {
        self == it
    }
}

#[thrust_macros::context]
impl<I> IntoIteratorSpec for core::iter::Enumerate<I>
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
    I::Ty: PartialEq,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: Self) -> bool {
        self == it
    }
}

#[thrust_macros::context]
impl<A, B> IntoIteratorSpec for core::iter::Zip<A, B>
where
    A: IteratorSpec,
    B: IteratorSpec,
    A::Item: thrust_models::Model,
    B::Item: thrust_models::Model,
    A::Ty: PartialEq,
    B::Ty: PartialEq,
    <A::Item as thrust_models::Model>::Ty: PartialEq,
    <B::Item as thrust_models::Model>::Ty: PartialEq,
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
          A::Ty: PartialEq,
          B::Ty: PartialEq,
          <A::IntoIter as thrust_models::Model>::Ty: PartialEq,
          <B::IntoIter as thrust_models::Model>::Ty: PartialEq,
          A::Item: thrust_models::Model,
          B::Item: thrust_models::Model,
          <A::Item as thrust_models::Model>::Ty: PartialEq,
          <B::Item as thrust_models::Model>::Ty: PartialEq
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
    where T: thrust_models::Model + Clone, T::Ty: PartialEq
{
    std::vec::from_elem(elem, n)
}

// Only the lengths are specified; the element-wise description of the two
// halves needs quantifiers the solvers do not handle well yet.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(at <= (*vec).len())]
#[thrust_macros::ensures((!vec).len() == at && result.len() == (*vec).len() - at)]
fn _extern_spec_vec_split_off<T>(vec: &mut Vec<T>, at: usize) -> Vec<T>
    where T: thrust_models::Model, T::Ty: PartialEq
{
    Vec::split_off(vec, at)
}

// The iterator's items are not visible in this vocabulary, so only the old contents kept as a
// prefix are stated.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (!vec).len() >= (*vec).len()
        && thrust_models::forall(|i: thrust_models::model::Int|
            (0 <= i && i < (*vec).len()) ==> (!vec)[i] == (*vec)[i])
)]
fn _extern_spec_vec_extend<T, I>(vec: &mut Vec<T>, iter: I)
    where T: thrust_models::Model, T::Ty: PartialEq,
          I: IntoIterator<Item = T> + thrust_models::Model, I::Ty: PartialEq
{
    <Vec<T> as std::iter::Extend<T>>::extend(vec, iter)
}

// Nothing about the collected items is visible in this vocabulary, so the result is any `Vec<T>`.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn _extern_spec_vec_from_iter<T, I>(iter: I) -> Vec<T>
    where T: thrust_models::Model, T::Ty: PartialEq,
          I: IntoIterator<Item = T> + thrust_models::Model, I::Ty: PartialEq
{
    <Vec<T> as std::iter::FromIterator<T>>::from_iter(iter)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == array)]
fn _extern_spec_array_into_vec<T, const N: usize>(array: [T; N]) -> Vec<T>
    where T: thrust_models::Model, T::Ty: PartialEq
{
    <[T; N] as Into<Vec<T>>>::into(array)
}

// TODO: The following specs of some trait methods are too restrictive; we should allow for a
//       per-impl spec once we can describe the spec of blanket impls.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*x == *y))]
fn _extern_spec_partialeq_eq<T>(x: &T, y: &T) -> bool
  where T: thrust_models::Model + PartialEq, T::Ty: PartialEq
{
    PartialEq::eq(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == !(*x == *y))]
fn _extern_spec_partialeq_ne<T>(x: &T, y: &T) -> bool
  where T: thrust_models::Model + PartialEq, T::Ty: PartialEq
{
    PartialEq::ne(x, y)
}

// Hashing has no model; the spec only records that hashing itself does not
// panic, which lets derived Hash impls be analyzed (they hash field by field).
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn _extern_spec_hash<T, H>(x: &T, state: &mut H)
  where T: std::hash::Hash + thrust_models::Model + ?Sized, T::Ty: PartialEq, H: std::hash::Hasher + thrust_models::Model, H::Ty: PartialEq
{
    std::hash::Hash::hash(x, state)
}

// Default values of foreign types are not modeled; the spec only records that
// constructing one does not panic, which lets derived Default impls be analyzed.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn _extern_spec_default<T>() -> T
  where T: Default + thrust_models::Model, T::Ty: PartialEq
{
    T::default()
}

// Values are modeled purely, so a clone is the same value in the model.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == *x)]
fn _extern_spec_clone<T>(x: &T) -> T
  where T: thrust_models::Model + Clone, T::Ty: PartialEq
{
    Clone::clone(x)
}

// The provided `lt`, `le`, `gt` and `ge` of `PartialOrd`, which a type takes unless it defines its
// own: they compare through the type's `partial_cmp`.
#[thrust::extern_body_fn]
#[allow(path_statements)]
fn _extern_body_partialord_lt<T, U>(x: &T, y: &U) -> bool
  where T: PartialOrd<U> + ?Sized, U: ?Sized
{
    <T as PartialOrd<U>>::lt;
    matches!(x.partial_cmp(y), Some(std::cmp::Ordering::Less))
}

#[thrust::extern_body_fn]
#[allow(path_statements)]
fn _extern_body_partialord_le<T, U>(x: &T, y: &U) -> bool
  where T: PartialOrd<U> + ?Sized, U: ?Sized
{
    <T as PartialOrd<U>>::le;
    matches!(x.partial_cmp(y), Some(std::cmp::Ordering::Less | std::cmp::Ordering::Equal))
}

#[thrust::extern_body_fn]
#[allow(path_statements)]
fn _extern_body_partialord_gt<T, U>(x: &T, y: &U) -> bool
  where T: PartialOrd<U> + ?Sized, U: ?Sized
{
    <T as PartialOrd<U>>::gt;
    matches!(x.partial_cmp(y), Some(std::cmp::Ordering::Greater))
}

#[thrust::extern_body_fn]
#[allow(path_statements)]
fn _extern_body_partialord_ge<T, U>(x: &T, y: &U) -> bool
  where T: PartialOrd<U> + ?Sized, U: ?Sized
{
    <T as PartialOrd<U>>::ge;
    matches!(x.partial_cmp(y), Some(std::cmp::Ordering::Greater | std::cmp::Ordering::Equal))
}

// `&A` compares its referents.
#[thrust::extern_body_fn]
#[allow(path_statements)]
fn _extern_body_ref_partialord_lt<A, B>(x: &&A, y: &&B) -> bool
  where A: PartialOrd<B> + ?Sized, B: ?Sized
{
    <&A as PartialOrd<&B>>::lt;
    PartialOrd::lt(*x, *y)
}

#[thrust::extern_body_fn]
#[allow(path_statements)]
fn _extern_body_ref_partialord_le<A, B>(x: &&A, y: &&B) -> bool
  where A: PartialOrd<B> + ?Sized, B: ?Sized
{
    <&A as PartialOrd<&B>>::le;
    PartialOrd::le(*x, *y)
}

#[thrust::extern_body_fn]
#[allow(path_statements)]
fn _extern_body_ref_partialord_gt<A, B>(x: &&A, y: &&B) -> bool
  where A: PartialOrd<B> + ?Sized, B: ?Sized
{
    <&A as PartialOrd<&B>>::gt;
    PartialOrd::gt(*x, *y)
}

#[thrust::extern_body_fn]
#[allow(path_statements)]
fn _extern_body_ref_partialord_ge<A, B>(x: &&A, y: &&B) -> bool
  where A: PartialOrd<B> + ?Sized, B: ?Sized
{
    <&A as PartialOrd<&B>>::ge;
    PartialOrd::ge(*x, *y)
}
