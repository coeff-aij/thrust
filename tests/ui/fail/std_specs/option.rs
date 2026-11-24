//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off --cfg thrust_std_conformance
//@rustc-env: THRUST_NO_INJECT_STD=1 THRUST_TRY_SPECS=1 THRUST_VERIFY_ONLY=std_transcriptions::** THRUST_SOLVER=tests/thrust-pcsat-wrapper
// std.rs specializes its spec impls, so a crate compiling it as a source file enables
// `specialization` itself.
#![feature(specialization)]
#![allow(incomplete_features)]

// Fail twin of `tests/ui/pass/std_specs/option.rs`: `branch` breaks for `Some`, which its
// spec does not allow.

include!("../../../../std.rs");
include!("../../../../std_try.rs");

mod std_transcriptions {
    use crate::thrust_models;
    use std::convert::Infallible;
    use std::mem;
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
            Some(_) => ControlFlow::Break(None),
            None => ControlFlow::Break(None),
        }
    }

    // library/core/src/option.rs, `impl<T> const ops::FromResidual<Option<convert::Infallible>> for Option<T>`, `fn from_residual(residual: Option<convert::Infallible>) -> Self`
    pub fn option_from_residual<T>(residual: Option<Infallible>) -> Option<T> {
        match residual {
            None => None,
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

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn unwrap_or(self, default: T) -> T where T: [const] Destruct,`
    pub fn option_unwrap_or<T>(opt: Option<T>, default: T) -> T {
        match opt {
            Some(x) => x,
            None => default,
        }
    }

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn unwrap_or_else<F>(self, f: F) -> T where F: [const] FnOnce() -> T + [const] Destruct,`
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

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn map<U, F>(self, f: F) -> Option<U> where F: [const] FnOnce(T) -> U + [const] Destruct,`
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

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn map_or<U, F>(self, default: U, f: F) -> U where F: [const] FnOnce(T) -> U + [const] Destruct, U: [const] Destruct,`
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

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn ok_or<E: [const] Destruct>(self, err: E) -> Result<T, E>`
    pub fn option_ok_or<T, E>(opt: Option<T>, err: E) -> Result<T, E> {
        match opt {
            Some(v) => Ok(v),
            None => Err(err),
        }
    }

    // library/core/src/option.rs, `impl<T> Option<T>`, `fn take(&mut self) -> Option<T>`
    pub fn option_take<T>(opt: &mut Option<T>) -> Option<T> {
        mem::replace(opt, None)
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
            Ok(x) => Some(x),
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

    pub struct StdBodies;

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
