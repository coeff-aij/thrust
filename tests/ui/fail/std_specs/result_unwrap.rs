//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off --cfg thrust_std_conformance
//@rustc-env: THRUST_NO_INJECT_STD=1 THRUST_TRY_SPECS=1 THRUST_VERIFY_ONLY=std_transcriptions::result_unwrap_transcription::result_unwrap THRUST_SOLVER=tests/thrust-pcsat-wrapper
// std.rs specializes its spec impls, so a crate compiling it as a source file enables
// `specialization` itself.
#![feature(specialization)]
#![feature(try_blocks)]
#![allow(incomplete_features)]

// Fail twin of `tests/ui/pass/std_specs/option.rs`: `unwrap` panics for an `Ok`, which its spec does not allow.

include!("../../../../std.rs");
include!("../../../../std_try.rs");

mod std_transcriptions {
    use crate::thrust_models;
    use std::convert::Infallible;
    use std::ops::ControlFlow;
    use thrust_models::forall;
    use thrust_models::model::{Closure, Seq};
    use thrust_models::Ghost;

    // library/core/src/option.rs, `impl<T: [const] PartialEq> const PartialEq for Option<T>`, `fn eq(&self, other: &Self) -> bool`
    pub fn option_eq<T>(x: &Option<T>, y: &Option<T>) -> bool
    where
        T: thrust_models::Model + thrust_models::ModelEq + PartialEq,
    {
        match (x, y) {
            (Some(l), Some(r)) => *l == *r,
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (None, None) => true,
        }
    }

    // library/core/src/option.rs, `impl<T> const ops::Try for Option<T>`, `fn branch(self) -> ControlFlow<Self::Residual, Self::Output>`
    pub fn option_branch<T>(opt: Option<T>) -> ControlFlow<Option<Infallible>, T> {
        match opt {
            Some(v) => ControlFlow::Continue(v),
            None => ControlFlow::Break(None),
        }
    }

    // library/core/src/option.rs, `impl<T> const ops::Try for Option<T>`, `fn from_output(output: Self::Output) -> Self`
    pub fn option_from_output<T>(output: T) -> Option<T> {
        Some(output)
    }

    // library/core/src/option.rs, `impl<T> const ops::FromResidual<Option<convert::Infallible>> for Option<T>`, `fn from_residual(residual: Option<convert::Infallible>) -> Self`
    pub fn option_from_residual<T>(residual: Option<Infallible>) -> Option<T> {
        match residual {
            None => None,
        }
    }

    // library/core/src/ops/control_flow.rs, `impl<B, C> const ops::Try for ControlFlow<B, C>`, `fn branch(self) -> ControlFlow<Self::Residual, Self::Output>`
    pub fn control_flow_branch<B, C>(cf: ControlFlow<B, C>) -> ControlFlow<ControlFlow<B, Infallible>, C> {
        match cf {
            ControlFlow::Continue(c) => ControlFlow::Continue(c),
            ControlFlow::Break(b) => ControlFlow::Break(ControlFlow::Break(b)),
        }
    }

    // library/core/src/ops/control_flow.rs, `impl<B, C> const ops::Try for ControlFlow<B, C>`, `fn from_output(output: Self::Output) -> Self`
    pub fn control_flow_from_output<B, C>(output: C) -> ControlFlow<B, C> {
        ControlFlow::Continue(output)
    }

    // library/core/src/ops/control_flow.rs, `impl<B, C> const ops::FromResidual<ControlFlow<B, convert::Infallible>> for ControlFlow<B, C>`, `fn from_residual(residual: ControlFlow<B, convert::Infallible>) -> Self`
    pub fn control_flow_from_residual<B, C>(residual: ControlFlow<B, Infallible>) -> ControlFlow<B, C> {
        match residual {
            ControlFlow::Break(b) => ControlFlow::Break(b),
        }
    }

    // library/core/src/ops/control_flow.rs, `impl<B, C> ControlFlow<B, C>`, `fn break_value(self) -> Option<B>`
    pub fn control_flow_break_value<B, C>(cf: ControlFlow<B, C>) -> Option<B> {
        match cf {
            ControlFlow::Continue(..) => None,
            ControlFlow::Break(x) => Some(x),
        }
    }

    // std's `unwrap_failed` and `expect_failed` end in a panic. The specs' preconditions keep
    // them unreachable, which the checks of `unwrap` and `expect` rely on.
    fn unwrap_failed() -> ! {
        panic!()
    }

    fn expect_failed(_msg: &str) -> ! {
        panic!()
    }

    // std's `Result::unwrap` reports through its own `unwrap_failed`, which also ends in a panic (generic
    // over the error, as Thrust reads no `dyn` of a std trait);
    // the spec's precondition keeps it unreachable.
    pub mod result_unwrap_transcription {
        use super::thrust_models;

        fn unwrap_failed<E: std::fmt::Debug>(_msg: &str, _error: &E) -> ! {
            panic!()
        }
        pub fn result_unwrap<T, E>(res: Result<T, E>) -> T
        where
            T: thrust_models::Model,
            E: thrust_models::Model + std::fmt::Debug,
        {
            match res {
                Ok(_) => unwrap_failed("called `Result::unwrap()` on an `Err` value", &0),
                Err(e) => unwrap_failed("called `Result::unwrap()` on an `Err` value", &e),
            }
        }
    }

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn unwrap(self) -> T`
    pub fn option_unwrap<T>(opt: Option<T>) -> T {
        match opt {
            Some(val) => val,
            None => unwrap_failed(),
        }
    }

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn expect(self, msg: &str) -> T`
    pub fn option_expect<T>(opt: Option<T>, msg: &str) -> T {
        match opt {
            Some(val) => val,
            None => expect_failed(msg),
        }
    }

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn unwrap_or(self, default: T) -> T`
    pub fn option_unwrap_or<T>(opt: Option<T>, default: T) -> T {
        match opt {
            Some(x) => x,
            None => default,
        }
    }

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn unwrap_or_else<F>(self, f: F) -> T where F: FnOnce() -> T,`
    pub fn option_unwrap_or_else<T, F>(opt: Option<T>, f: F) -> T
    where
        T: thrust_models::Model,
        F: FnOnce() -> T,
    {
        match opt {
            Some(x) => x,
            None => f(),
        }
    }

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn map<U, F>(self, f: F) -> Option<U> where F: FnOnce(T) -> U,`
    pub fn option_map<T, U, F>(opt: Option<T>, f: F) -> Option<U>
    where
        T: thrust_models::Model,
        U: thrust_models::Model,
        F: FnOnce(T) -> U,
    {
        match opt {
            Some(x) => Some(f(x)),
            None => None,
        }
    }

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn map_or<U, F>(self, default: U, f: F) -> U where F: FnOnce(T) -> U,`
    pub fn option_map_or<T, U, F>(opt: Option<T>, default: U, f: F) -> U
    where
        T: thrust_models::Model,
        U: thrust_models::Model,
        F: FnOnce(T) -> U,
    {
        match opt {
            Some(t) => f(t),
            None => default,
        }
    }

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn ok_or<E>(self, err: E) -> Result<T, E>`
    pub fn option_ok_or<T, E>(opt: Option<T>, err: E) -> Result<T, E> {
        match opt {
            Some(v) => Ok(v),
            None => Err(err),
        }
    }

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn take(&mut self) -> Option<T>`
    pub fn option_take<T>(opt: &mut Option<T>) -> Option<T> {
        std::mem::replace(opt, None)
    }

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn as_ref(&self) -> Option<&T>`
    pub fn option_as_ref<T>(opt: &Option<T>) -> Option<&T> {
        match *opt {
            Some(ref x) => Some(x),
            None => None,
        }
    }

    // library/core/src/result.rs, `impl<T, E> Result<T, E>`, `fn ok(self) -> Option<T> where T: [const] Destruct, E: [const] Destruct,`
    pub fn result_ok<T, E>(res: Result<T, E>) -> Option<T> {
        match res {
            Ok(_) => None,
            Err(_) => None,
        }
    }

    // The transcriptions of `Iterator`'s methods are methods of a trait impl, where
    // `#[thrust_macros::context]` adds no `<T as Model>::Ty: PartialEq` bounds, which the specs
    // that call them do not have.
    pub trait IteratorMethods<I, F>
    where
        I: crate::IteratorSpec,
        I::Item: thrust_models::Model,
        F: FnMut(I::Item) -> bool,
    {
        fn iterator_all(it: &mut I, f: F) -> bool;
        fn iterator_any(it: &mut I, f: F) -> bool;
    }

    pub trait IteratorFindMethods<I, P>
    where
        I: crate::IteratorSpec,
        I::Item: thrust_models::Model,
        P: FnMut(&I::Item) -> bool,
    {
        fn iterator_find(it: &mut I, predicate: P) -> Option<I::Item>;
    }

    pub trait IteratorFoldMethods<I, B, F>
    where
        I: crate::IteratorSpec,
        I::Item: thrust_models::Model,
        B: thrust_models::Model,
        F: FnMut(B, I::Item) -> B,
    {
        fn iterator_fold(it: I, init: B, f: F) -> B;
    }

    pub trait IteratorTryFoldMethods<I, B, F>
    where
        I: crate::IteratorSpec,
        I::Item: thrust_models::Model,
        B: thrust_models::Model,
        F: FnMut(B, I::Item) -> Option<B>,
    {
        fn iterator_try_fold(it: &mut I, init: B, f: F) -> Option<B>;
    }

    pub trait IteratorTryFoldControlFlowMethods<I, B, C, F>
    where
        I: crate::IteratorSpec,
        I::Item: thrust_models::Model,
        B: thrust_models::Model,
        C: thrust_models::Model,
        F: FnMut(B, I::Item) -> ControlFlow<C, B>,
    {
        fn iterator_try_fold(it: &mut I, init: B, f: F) -> ControlFlow<C, B>;
    }

    pub struct StdBodies;

    #[thrust_macros::context]
    impl<I, B, F> IteratorTryFoldMethods<I, B, F> for StdBodies
    where
        I: crate::IteratorSpec,
        I::Item: thrust_models::Model,
        B: thrust_models::Model,
        F: FnMut(B, I::Item) -> Option<B>,
    {
        // library/core/src/iter/traits/iterator.rs, `pub trait Iterator`, `fn try_fold<B, F, R>(&mut self, init: B, mut f: F) -> R where Self: Sized, F: FnMut(B, Self::Item) -> R, R: Try<Output = B>,`
        // `R` is `Option<B>`. The ghosts `gs`, `gaccs` and `gfs` are the items taken, the accumulators and the closure's states before each call.
        fn iterator_try_fold(it: &mut I, init: B, mut f: F) -> Option<B> {
            let mut accum = init;
            let mut gs = thrust_macros::ghost!(|| -> Vec<I::Item> { Seq::empty() });
            let mut gaccs = thrust_macros::ghost!(|accum: B| -> Seq<<B as thrust_models::Model>::Ty> { Seq::singleton(accum) });
            let mut gfs = thrust_macros::ghost!(|f: F| -> Seq<Closure<F>> { Seq::singleton(f) });
            while let Some(x) = it.next() {
                thrust_macros::invariant!(
                    |it: &mut I, accum: B, f: F, gs: Ghost<Vec<I::Item>>, gaccs: Ghost<Seq<<B as thrust_models::Model>::Ty>>, gfs: Ghost<Seq<Closure<F>>>, old!(it): &mut I, old!(init): B, old!(f): F|
                    !it == !old!(it)
                        && I::inv(*it)
                        && crate::_iter_spec_try_fold_chain::<I, B, F>(*old!(it), old!(init), old!(f), gs, *it, gaccs, gfs)
                        && gaccs[gs.len()] == accum
                        && gfs[gs.len()] == f
                        && forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>, it1: <I as thrust_models::Model>::Ty,
                                   accs: Seq<<B as thrust_models::Model>::Ty>, fs: Seq<Closure<F>>,
                                   x: <I::Item as thrust_models::Model>::Ty, it2: <I as thrust_models::Model>::Ty|
                            (crate::_iter_spec_try_fold_chain::<I, B, F>(*old!(it), old!(init), old!(f), s, it1, accs, fs)
                                && I::produces(it1, Seq::singleton(x), it2))
                                ==> thrust_macros::pre!(fs[s.len()](accs[s.len()], x)))
                );
                let gx = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
                accum = f(accum, x)?;
                gs = thrust_macros::ghost!(|gs: Ghost<Vec<I::Item>>, gx: Ghost<I::Item>| -> Vec<I::Item> { gs.push(gx) });
                gaccs = thrust_macros::ghost!(|gaccs: Ghost<Seq<<B as thrust_models::Model>::Ty>>, accum: B| -> Seq<<B as thrust_models::Model>::Ty> { gaccs.push(accum) });
                gfs = thrust_macros::ghost!(|gfs: Ghost<Seq<Closure<F>>>, f: F| -> Seq<Closure<F>> { gfs.push(f) });
            }
            try { accum }
        }
    }

    #[thrust_macros::context]
    impl<I, B, C, F> IteratorTryFoldControlFlowMethods<I, B, C, F> for StdBodies
    where
        I: crate::IteratorSpec,
        I::Item: thrust_models::Model,
        B: thrust_models::Model,
        C: thrust_models::Model,
        F: FnMut(B, I::Item) -> ControlFlow<C, B>,
    {
        // library/core/src/iter/traits/iterator.rs, `pub trait Iterator`, `fn try_fold<B, F, R>(&mut self, init: B, mut f: F) -> R where Self: Sized, F: FnMut(B, Self::Item) -> R, R: Try<Output = B>,`
        // `R` is `ControlFlow<C, B>`. The ghosts `gs`, `gaccs` and `gfs` are the items taken, the accumulators and the closure's states before each call.
        fn iterator_try_fold(it: &mut I, init: B, mut f: F) -> ControlFlow<C, B> {
            let mut accum = init;
            let mut gs = thrust_macros::ghost!(|| -> Vec<I::Item> { Seq::empty() });
            let mut gaccs = thrust_macros::ghost!(|accum: B| -> Seq<<B as thrust_models::Model>::Ty> { Seq::singleton(accum) });
            let mut gfs = thrust_macros::ghost!(|f: F| -> Seq<Closure<F>> { Seq::singleton(f) });
            while let Some(x) = it.next() {
                thrust_macros::invariant!(
                    |it: &mut I, accum: B, f: F, gs: Ghost<Vec<I::Item>>, gaccs: Ghost<Seq<<B as thrust_models::Model>::Ty>>, gfs: Ghost<Seq<Closure<F>>>, old!(it): &mut I, old!(init): B, old!(f): F|
                    !it == !old!(it)
                        && I::inv(*it)
                        && crate::_iter_spec_try_fold_control_flow_chain::<I, B, C, F>(*old!(it), old!(init), old!(f), gs, *it, gaccs, gfs)
                        && gaccs[gs.len()] == accum
                        && gfs[gs.len()] == f
                        && forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>, it1: <I as thrust_models::Model>::Ty,
                                   accs: Seq<<B as thrust_models::Model>::Ty>, fs: Seq<Closure<F>>,
                                   x: <I::Item as thrust_models::Model>::Ty, it2: <I as thrust_models::Model>::Ty|
                            (crate::_iter_spec_try_fold_control_flow_chain::<I, B, C, F>(*old!(it), old!(init), old!(f), s, it1, accs, fs)
                                && I::produces(it1, Seq::singleton(x), it2))
                                ==> thrust_macros::pre!(fs[s.len()](accs[s.len()], x)))
                );
                let gx = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
                accum = f(accum, x)?;
                gs = thrust_macros::ghost!(|gs: Ghost<Vec<I::Item>>, gx: Ghost<I::Item>| -> Vec<I::Item> { gs.push(gx) });
                gaccs = thrust_macros::ghost!(|gaccs: Ghost<Seq<<B as thrust_models::Model>::Ty>>, accum: B| -> Seq<<B as thrust_models::Model>::Ty> { gaccs.push(accum) });
                gfs = thrust_macros::ghost!(|gfs: Ghost<Seq<Closure<F>>>, f: F| -> Seq<Closure<F>> { gfs.push(f) });
            }
            try { accum }
        }
    }

    #[thrust_macros::context]
    impl<I, B, F> IteratorFoldMethods<I, B, F> for StdBodies
    where
        I: crate::IteratorSpec,
        I::Item: thrust_models::Model,
        B: thrust_models::Model,
        F: FnMut(B, I::Item) -> B,
    {
        // library/core/src/iter/traits/iterator.rs, `pub trait Iterator`, `fn fold<B, F>(mut self, init: B, mut f: F) -> B where Self: Sized, F: FnMut(B, Self::Item) -> B,`
        // The ghosts `gs`, `gaccs` and `gfs` are the items taken, the accumulators and the closure's states before each call.
        fn iterator_fold(mut it: I, init: B, mut f: F) -> B {
            let mut accum = init;
            let mut gs = thrust_macros::ghost!(|| -> Vec<I::Item> { Seq::empty() });
            let mut gaccs = thrust_macros::ghost!(|accum: B| -> Seq<<B as thrust_models::Model>::Ty> { Seq::singleton(accum) });
            let mut gfs = thrust_macros::ghost!(|f: F| -> Seq<Closure<F>> { Seq::singleton(f) });
            while let Some(x) = it.next() {
                thrust_macros::invariant!(
                    |it: I, accum: B, f: F, gs: Ghost<Vec<I::Item>>, gaccs: Ghost<Seq<<B as thrust_models::Model>::Ty>>, gfs: Ghost<Seq<Closure<F>>>, old!(it): I, old!(init): B, old!(f): F|
                    I::inv(it)
                        && crate::_iter_spec_fold_chain::<I, B, F>(old!(it), old!(init), old!(f), gs, it, gaccs, gfs)
                        && gaccs[gs.len()] == accum
                        && gfs[gs.len()] == f
                        && forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>, it1: <I as thrust_models::Model>::Ty,
                                   accs: Seq<<B as thrust_models::Model>::Ty>, fs: Seq<Closure<F>>,
                                   x: <I::Item as thrust_models::Model>::Ty, it2: <I as thrust_models::Model>::Ty|
                            (crate::_iter_spec_fold_chain::<I, B, F>(old!(it), old!(init), old!(f), s, it1, accs, fs)
                                && I::produces(it1, Seq::singleton(x), it2))
                                ==> thrust_macros::pre!(fs[s.len()](accs[s.len()], x)))
                );
                let gx = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
                accum = f(accum, x);
                gs = thrust_macros::ghost!(|gs: Ghost<Vec<I::Item>>, gx: Ghost<I::Item>| -> Vec<I::Item> { gs.push(gx) });
                gaccs = thrust_macros::ghost!(|gaccs: Ghost<Seq<<B as thrust_models::Model>::Ty>>, accum: B| -> Seq<<B as thrust_models::Model>::Ty> { gaccs.push(accum) });
                gfs = thrust_macros::ghost!(|gfs: Ghost<Seq<Closure<F>>>, f: F| -> Seq<Closure<F>> { gfs.push(f) });
            }
            accum
        }
    }

    #[thrust_macros::context]
    impl<I, P> IteratorFindMethods<I, P> for StdBodies
    where
        I: crate::IteratorSpec,
        I::Item: thrust_models::Model,
        P: FnMut(&I::Item) -> bool,
    {
        // library/core/src/slice/iter/macros.rs, `impl<'a, T> Iterator for $name<'a, T>`, `fn find<P>(&mut self, mut predicate: P) -> Option<Self::Item> where Self: Sized, P: FnMut(&Self::Item) -> bool,`
        // core's default `find` calls `try_fold` with a closure that breaks where this loop returns.
        // The ghosts `s` and `fs` are the items taken and the predicate's states before each.
        fn iterator_find(it: &mut I, mut predicate: P) -> Option<I::Item> {
            let mut s = thrust_macros::ghost!(|| -> Vec<I::Item> { Seq::empty() });
            let mut fs = thrust_macros::ghost!(|predicate: P| -> Seq<Closure<P>> { Seq::singleton(predicate) });
            while let Some(x) = it.next() {
                thrust_macros::invariant!(
                    |it: &mut I, predicate: P, s: Ghost<Vec<I::Item>>, fs: Ghost<Seq<Closure<P>>>, old!(it): &mut I, old!(predicate): P|
                    !it == !old!(it)
                        && I::inv(*it)
                        && crate::_iter_spec_find_chain::<I, P>(*old!(it), old!(predicate), s, *it, fs)
                        && fs[s.len()] == predicate
                        && forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>, it1: <I as thrust_models::Model>::Ty,
                                   fs: Seq<Closure<P>>, x: <I::Item as thrust_models::Model>::Ty,
                                   it2: <I as thrust_models::Model>::Ty|
                            (crate::_iter_spec_find_chain::<I, P>(*old!(it), old!(predicate), s, it1, fs)
                                && I::produces(it1, Seq::singleton(x), it2))
                                ==> thrust_macros::pre!(fs[s.len()](&x)))
                );
                let gx = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
                if predicate(&x) {
                    return Some(x);
                }
                s = thrust_macros::ghost!(|s: Ghost<Vec<I::Item>>, gx: Ghost<I::Item>| -> Vec<I::Item> { s.push(gx) });
                fs = thrust_macros::ghost!(|fs: Ghost<Seq<Closure<P>>>, predicate: P| -> Seq<Closure<P>> { fs.push(predicate) });
            }
            None
        }
    }

    #[thrust_macros::context]
    impl<I, F> IteratorMethods<I, F> for StdBodies
    where
        I: crate::IteratorSpec,
        I::Item: thrust_models::Model,
        F: FnMut(I::Item) -> bool,
    {
        // library/core/src/slice/iter/macros.rs, `impl<'a, T> Iterator for $name<'a, T>`, `fn all<F>(&mut self, mut f: F) -> bool where Self: Sized, F: FnMut(Self::Item) -> bool,`
        // core's default `all` calls `try_fold` with a closure that breaks where this loop returns.
        // The ghosts `s` and `fs` are the items taken and the predicate's states before each.
        fn iterator_all(it: &mut I, mut f: F) -> bool {
            let mut s = thrust_macros::ghost!(|| -> Vec<I::Item> { Seq::empty() });
            let mut fs = thrust_macros::ghost!(|f: F| -> Seq<Closure<F>> { Seq::singleton(f) });
            while let Some(x) = it.next() {
                thrust_macros::invariant!(
                    |it: &mut I, f: F, s: Ghost<Vec<I::Item>>, fs: Ghost<Seq<Closure<F>>>, old!(it): &mut I, old!(f): F|
                    !it == !old!(it)
                        && I::inv(*it)
                        && crate::_iter_spec_short_circuit_chain::<I, F>(*old!(it), old!(f), s, *it, fs, false)
                        && fs[s.len()] == f
                        && forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>, it1: <I as thrust_models::Model>::Ty,
                                   fs: Seq<Closure<F>>, x: <I::Item as thrust_models::Model>::Ty,
                                   it2: <I as thrust_models::Model>::Ty|
                            (crate::_iter_spec_short_circuit_chain::<I, F>(*old!(it), old!(f), s, it1, fs, false)
                                && I::produces(it1, Seq::singleton(x), it2))
                                ==> thrust_macros::pre!(fs[s.len()](x)))
                );
                let gx = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
                if !f(x) {
                    return false;
                }
                s = thrust_macros::ghost!(|s: Ghost<Vec<I::Item>>, gx: Ghost<I::Item>| -> Vec<I::Item> { s.push(gx) });
                fs = thrust_macros::ghost!(|fs: Ghost<Seq<Closure<F>>>, f: F| -> Seq<Closure<F>> { fs.push(f) });
            }
            true
        }

        // library/core/src/slice/iter/macros.rs, `impl<'a, T> Iterator for $name<'a, T>`, `fn any<F>(&mut self, mut f: F) -> bool where Self: Sized, F: FnMut(Self::Item) -> bool,`
        // core's default `any` calls `try_fold` with a closure that breaks where this loop returns.
        // The ghosts `s` and `fs` are the items taken and the predicate's states before each.
        fn iterator_any(it: &mut I, mut f: F) -> bool {
            let mut s = thrust_macros::ghost!(|| -> Vec<I::Item> { Seq::empty() });
            let mut fs = thrust_macros::ghost!(|f: F| -> Seq<Closure<F>> { Seq::singleton(f) });
            while let Some(x) = it.next() {
                thrust_macros::invariant!(
                    |it: &mut I, f: F, s: Ghost<Vec<I::Item>>, fs: Ghost<Seq<Closure<F>>>, old!(it): &mut I, old!(f): F|
                    !it == !old!(it)
                        && I::inv(*it)
                        && crate::_iter_spec_short_circuit_chain::<I, F>(*old!(it), old!(f), s, *it, fs, true)
                        && fs[s.len()] == f
                        && forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>, it1: <I as thrust_models::Model>::Ty,
                                   fs: Seq<Closure<F>>, x: <I::Item as thrust_models::Model>::Ty,
                                   it2: <I as thrust_models::Model>::Ty|
                            (crate::_iter_spec_short_circuit_chain::<I, F>(*old!(it), old!(f), s, it1, fs, true)
                                && I::produces(it1, Seq::singleton(x), it2))
                                ==> thrust_macros::pre!(fs[s.len()](x)))
                );
                let gx = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
                if f(x) {
                    return true;
                }
                s = thrust_macros::ghost!(|s: Ghost<Vec<I::Item>>, gx: Ghost<I::Item>| -> Vec<I::Item> { s.push(gx) });
                fs = thrust_macros::ghost!(|fs: Ghost<Seq<Closure<F>>>, f: F| -> Seq<Closure<F>> { fs.push(f) });
            }
            false
        }
    }
}

fn main() {}
