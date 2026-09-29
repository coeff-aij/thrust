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
