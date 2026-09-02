use thrust_models::forall;

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(Self::completed(self) ==> result == None)]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    #[thrust_macros::ensures(forall(|i| Self::step(*self, i, !self) ==> result == Some(i)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
}

pub struct Fuse<I> {
    iter: Option<I>,
}

impl<I> thrust_models::Model for Fuse<I> {
    type Ty = Fuse<I>;
}

#[thrust_macros::context]
impl<I> Iterator for Fuse<I>
where
    I: Iterator + thrust_models::Model,
    <I as Iterator>::Item: thrust_models::Model,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = I::Item;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.is_none()
        // || self.iter.is_some()
        // && self.iter.unwrap().invariant()
        "(or
            ((_ is std.option.Option.None<a0>)
                (tuple_proj<std.option.Option<a0>>.0 self_))
            (and
                ((_ is std.option.Option.Some<a0>)
                    (tuple_proj<std.option.Option<a0>>.0 self_))
                (q_invariant_3ce756bf7a32ffadf2e7f51c913e5b2a<a0>
                    (_getstd.option.Option.Some.0<a0>
                        (tuple_proj<std.option.Option<a0>>.0 self_)))))";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // *self.iter.is_none() || *self.iter.is_some() && !self.iter.is_none() && exists(|i: I| Self::completed(Mut::new(*self.iter.unwrap(), i)))
        "(or
            ((_ is std.option.Option.None<a0>)
                (tuple_proj<std.option.Option<a0>>.0
                    (mut_current<Tuple<std.option.Option<a0>>> self_)
                )
            )
            (and
                ((_ is std.option.Option.Some<a0>)
                    (tuple_proj<std.option.Option<a0>>.0 
                        (mut_current<Tuple<std.option.Option<a0>>> self_)
                    )
                )
                ((_ is std.option.Option.None<a0>)
                    (tuple_proj<std.option.Option<a0>>.0 
                        (mut_final<Tuple<std.option.Option<a0>>> self_)
                    )
                )
                (exists ((i a0))
                    (q_completed_3ce756bf7a32ffadc7440a2381da7e0f<a0>
                        (mut<a0>
                            (_getstd.option.Option.Some.0<a0>
                                (tuple_proj<std.option.Option<a0>>.0
                                    (mut_current<Tuple<std.option.Option<a0>>> self_)
                                )
                            )
                            i
                        )
                    )
                )
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.iter.is_some()
        // && dist.iter.is_some()
        // && self.iter.unwrap().step(item, dist.iter.unwrap())
        "(and
            ((_ is std.option.Option.Some<a0>)
                (tuple_proj<std.option.Option<a0>>.0 self_))
            ((_ is std.option.Option.Some<a0>)
                (tuple_proj<std.option.Option<a0>>.0 dist))
            (q_step_3ce756bf7a32ffad416eeec40eaf9c1a<a0>
                (_getstd.option.Option.Some.0<a0>
                    (tuple_proj<std.option.Option<a0>>.0 self_))
                item
                (_getstd.option.Option.Some.0<a0>
                    (tuple_proj<std.option.Option<a0>>.0 dist))))";
        true
    }

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.iter {
            None => None,
            Some(iter) => match iter.next() {
                None => {
                    self.iter = None;
                    None
                }
                x => x,
            },
        }
    }
}

fn main() {}
