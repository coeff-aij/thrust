//! Expansion of `#[thrust_macros::requires]`, `#[thrust_macros::ensures]`,
//! `#[thrust_macros::predicate]`, and the internal `_requires_ensures` glue.
//!
//! `requires`/`ensures` accumulate their predicates into a single
//! `_requires_ensures` attribute, which expands into `#[thrust::formula_fn]`
//! companions (over `Model::Ty` parameters) plus an extern-spec wrapper that
//! references them.

use proc_macro::TokenStream;
use proc_macro2::{Group, Ident, TokenStream as TokenStream2, TokenTree};
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse_macro_input, punctuated::Punctuated, FnArg, GenericParam, Generics, WherePredicate,
};

use crate::{apit, fn_outer_item::FnOuterItem, FormulaFnTypeLowering};

pub fn expand_predicate(item: TokenStream) -> TokenStream {
    expand_spec_fn(item, SpecFnKind::Predicate)
}

/// Like a predicate, but the return type is any model type: the function is callable in the
/// term position of a specification.
pub fn expand_logic(item: TokenStream) -> TokenStream {
    expand_spec_fn(item, SpecFnKind::Logic)
}

/// `#[variant(e)]` written above `#[logic]` is moved below it, where [`expand_logic`] takes it.
pub fn expand_variant(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = TokenStream2::from(attr);
    let mut func = parse_macro_input!(item as FnItemWithSignature);
    let attrs = func.attrs_mut();
    let Some(logic) = attrs.iter().position(|a| has_last_segment(a, "logic")) else {
        let err = syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[thrust_macros::variant] applies only to a #[thrust_macros::logic] function",
        )
        .to_compile_error();
        return quote! { #err #func }.into();
    };
    attrs.insert(
        logic + 1,
        syn::parse_quote!(#[::thrust_macros::variant(#attr)]),
    );
    func.into_token_stream().into()
}

#[derive(PartialEq)]
enum SpecFnKind {
    Predicate,
    Logic,
}

fn has_last_segment(attr: &syn::Attribute, name: &str) -> bool {
    attr.path()
        .segments
        .last()
        .is_some_and(|segment| segment.ident == name)
}

/// Removes the `#[thrust_macros::variant(e)]` attribute from `attrs`, returning `e`.
fn take_variant(attrs: &mut Vec<syn::Attribute>) -> syn::Result<Option<TokenStream2>> {
    let mut variants = attrs.iter().filter(|a| has_last_segment(a, "variant"));
    let variant = variants.next().map(|a| a.parse_args()).transpose()?;
    if let Some(extra) = variants.next() {
        return Err(syn::Error::new_spanned(
            extra,
            "a logic function takes one variant",
        ));
    }
    attrs.retain(|a| !has_last_segment(a, "variant"));
    Ok(variant)
}

fn expand_spec_fn(item: TokenStream, kind: SpecFnKind) -> TokenStream {
    let mut func = parse_macro_input!(item as FnItemWithSignature);
    let marker = match kind {
        SpecFnKind::Predicate => quote!(#[thrust::predicate]),
        SpecFnKind::Logic => quote!(#[thrust::logic]),
    };
    let variant = match take_variant(func.attrs_mut()) {
        Ok(Some(_)) if kind != SpecFnKind::Logic => {
            let err = syn::Error::new_spanned(
                &func.sig().ident,
                "#[thrust_macros::variant] applies only to a #[thrust_macros::logic] function",
            )
            .to_compile_error();
            return quote! { #err #func }.into();
        }
        Ok(variant) => variant,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };
    let impl_trait_names = apit::take_names(func.attrs_mut());
    let outer_context = match extract_outer_context(&func) {
        Ok(ctx) => ctx,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };

    let name = &func.sig().ident;
    let sig = apit::desugar_signature(func.sig(), &impl_trait_names);
    let def_generics = generic_params_tokens(&sig.generics);
    let turbofish = generic_turbofish(&sig.generics);
    let type_lowering = if let Some(outer_context) = &outer_context {
        FormulaFnTypeLowering::with_outer_context(&sig, outer_context)
    } else {
        FormulaFnTypeLowering::new(&sig)
    };
    let model_ty_params = type_lowering.lower_params(&sig.inputs);
    let model_ret = type_lowering.lower_return_type(&sig.output);

    let model_preds = type_lowering.model_where_predicates();
    let extended_where = extended_where_clause(&func, &model_preds);

    // A predicate body written as a Rust expression is translated through the
    // `formula_fn` pipeline; a raw SMT-LIB2 string-literal body is not.
    let is_rust_body = func.block().is_some_and(|block| !is_raw_smt2_body(block));
    let formula_fn_attr = if is_rust_body {
        quote! {
            #[thrust::formula_fn]
        }
    } else {
        quote!()
    };

    let vis = func.vis();
    let sig = quote! {
        #[allow(dead_code)]
        #formula_fn_attr
        #marker
        #vis fn #name #def_generics(#model_ty_params) -> #model_ret #extended_where
    };
    let Some(block) = func.block() else {
        return quote! { #sig; }.into();
    };
    let mut block = block.clone();
    // The receiver `self` is lowered to a named `self_` parameter, so rewrite
    // references in the (Rust) body to match.
    if is_rust_body {
        rewrite_self_in_block(&mut block);
    }
    if is_rust_body && kind == SpecFnKind::Logic {
        wrap_result_literals_in_block(&mut block);
    }
    let Some(mut variant) = variant else {
        return quote! { #sig #block }.into();
    };
    if func.sig().receiver().is_some() {
        variant = variant
            .into_iter()
            .map(|tt| rewrite_self_in_tokens(tt, &format_ident!("self_")))
            .collect();
    }
    let variant = crate::formula::expand(variant);
    let variant_name = format_ident!("_thrust_variant_{}", name);
    let path_prefix = outer_context.as_ref().map(|_| quote!(Self::));
    quote! {
        #[allow(path_statements)]
        #sig {
            #[thrust::variant_path]
            #path_prefix #variant_name #turbofish;
            #block
        }

        #[allow(dead_code, unused_variables, non_snake_case)]
        #[thrust::formula_fn]
        #[thrust::logic]
        fn #variant_name #def_generics(#model_ty_params)
            -> impl crate::thrust_models::Model<Ty: crate::thrust_models::model::Integer>
            #extended_where
        {
            #variant
        }
    }
    .into()
}

/// Writes each unsuffixed integer literal that a logic function's body returns as
/// `int_lit(n)`, which takes the model of the result type where a bare literal is an `i32`.
fn wrap_result_literals(expr: &mut syn::Expr) {
    match expr {
        syn::Expr::If(e) => {
            wrap_result_literals_in_block(&mut e.then_branch);
            if let Some((_, else_branch)) = &mut e.else_branch {
                wrap_result_literals(else_branch);
            }
        }
        syn::Expr::Match(e) => {
            for arm in &mut e.arms {
                wrap_result_literals(&mut arm.body);
            }
        }
        syn::Expr::Block(e) => wrap_result_literals_in_block(&mut e.block),
        syn::Expr::Paren(e) => wrap_result_literals(&mut e.expr),
        _ if is_unsuffixed_int_literal(expr) => {
            *expr = syn::parse_quote!(crate::thrust_models::model::int_lit(#expr));
        }
        _ => {}
    }
}

fn wrap_result_literals_in_block(block: &mut syn::Block) {
    if let Some(syn::Stmt::Expr(expr, None)) = block.stmts.last_mut() {
        wrap_result_literals(expr);
    }
}

fn is_unsuffixed_int_literal(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit.suffix().is_empty(),
        syn::Expr::Unary(syn::ExprUnary {
            op: syn::UnOp::Neg(_),
            expr,
            ..
        }) => is_unsuffixed_int_literal(expr),
        _ => false,
    }
}

/// Whether a predicate body is a raw SMT-LIB2 definition, i.e. it contains a
/// string-literal statement such as `"(= ..)"; true`.
fn is_raw_smt2_body(block: &syn::Block) -> bool {
    block.stmts.iter().any(|stmt| {
        matches!(
            stmt,
            syn::Stmt::Expr(
                syn::Expr::Lit(syn::ExprLit {
                    lit: syn::Lit::Str(_),
                    ..
                }),
                _,
            )
        )
    })
}

pub fn expand_law(item: TokenStream) -> TokenStream {
    let mut func = parse_macro_input!(item as FnItemWithSignature);
    func.attrs_mut().push(syn::parse_quote!(#[thrust::law]));
    func.into_token_stream().into()
}

pub fn expand_requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    let expr = crate::formula::expand(attr.into());
    let mut func = parse_macro_input!(item as FnItemWithSignature);

    let (req_expr, ens_expr) = match extract_requires_ensures(&mut func) {
        Ok((req, ens)) => (req, ens),
        Err(e) => return e.to_compile_error().into(),
    };
    func.attrs_mut().push(syn::parse_quote!(
        #[::thrust_macros::_requires_ensures((#req_expr) && (#expr), #ens_expr)]
    ));

    func.into_token_stream().into()
}

pub fn expand_ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    let expr = crate::formula::expand(attr.into());
    let mut func = parse_macro_input!(item as FnItemWithSignature);

    let (req_expr, ens_expr) = match extract_requires_ensures(&mut func) {
        Ok((req, ens)) => (req, ens),
        Err(e) => return e.to_compile_error().into(),
    };
    func.attrs_mut().push(syn::parse_quote!(
        #[::thrust_macros::_requires_ensures(#req_expr, (#ens_expr) && (#expr))]
    ));

    func.into_token_stream().into()
}

pub fn expand_requires_ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    use syn::parse::Parser as _;
    let parser = Punctuated::<syn::Expr, syn::Token![,]>::parse_separated_nonempty;
    let mut exprs = match parser.parse(attr.clone()) {
        Ok(exprs) => exprs,
        Err(e) => return e.to_compile_error().into(),
    };
    if exprs.len() != 2 {
        return syn::Error::new_spanned(
            TokenStream2::from(attr),
            "expected exactly two comma-separated expressions in _requires_ensures attribute",
        )
        .to_compile_error()
        .into();
    }

    let ens_expr = exprs.pop().unwrap();
    let req_expr = exprs.pop().unwrap();

    let func = parse_macro_input!(item as FnItemWithSignature);
    let outer_context = match extract_outer_context(&func) {
        Ok(ctx) => ctx,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };
    let mut tokens = ExpandedTokens::new(func, req_expr, ens_expr);
    if let Some(ctx) = outer_context {
        tokens = tokens.with_outer_context(ctx);
    }
    tokens.into_token_stream().into()
}

#[allow(clippy::enum_variant_names)]
#[derive(Debug, Clone)]
pub enum FnItemWithSignature {
    ItemFn(syn::ItemFn),
    ImplItemFn(syn::ImplItemFn),
    TraitItemFn(syn::TraitItemFn),
}

impl syn::parse::Parse for FnItemWithSignature {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        use syn::parse::discouraged::Speculative as _;

        let fork = input.fork();
        if let Ok(item_fn) = fork.parse::<syn::ItemFn>() {
            input.advance_to(&fork);
            return Ok(Self::ItemFn(item_fn));
        }

        let fork = input.fork();
        if let Ok(impl_item_fn) = fork.parse::<syn::ImplItemFn>() {
            input.advance_to(&fork);
            return Ok(Self::ImplItemFn(impl_item_fn));
        }

        let fork = input.fork();
        if let Ok(trait_item_fn) = fork.parse::<syn::TraitItemFn>() {
            input.advance_to(&fork);
            return Ok(Self::TraitItemFn(trait_item_fn));
        }

        Err(input.error("expected a free function, an impl method, or a trait method"))
    }
}

impl quote::ToTokens for FnItemWithSignature {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => item_fn.to_tokens(tokens),
            FnItemWithSignature::ImplItemFn(impl_item_fn) => impl_item_fn.to_tokens(tokens),
            FnItemWithSignature::TraitItemFn(trait_item_fn) => trait_item_fn.to_tokens(tokens),
        }
    }
}

impl FnItemWithSignature {
    pub fn block(&self) -> Option<&syn::Block> {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => Some(&item_fn.block),
            FnItemWithSignature::ImplItemFn(impl_item_fn) => Some(&impl_item_fn.block),
            FnItemWithSignature::TraitItemFn(_) => None,
        }
    }

    pub fn block_mut(&mut self) -> Option<&mut syn::Block> {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => Some(&mut item_fn.block),
            FnItemWithSignature::ImplItemFn(impl_item_fn) => Some(&mut impl_item_fn.block),
            FnItemWithSignature::TraitItemFn(_) => None,
        }
    }

    pub fn vis(&self) -> Option<&syn::Visibility> {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => Some(&item_fn.vis),
            FnItemWithSignature::ImplItemFn(impl_item_fn) => Some(&impl_item_fn.vis),
            FnItemWithSignature::TraitItemFn(_) => None,
        }
    }

    pub fn attrs(&self) -> &[syn::Attribute] {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => &item_fn.attrs,
            FnItemWithSignature::ImplItemFn(impl_item_fn) => &impl_item_fn.attrs,
            FnItemWithSignature::TraitItemFn(trait_item_fn) => &trait_item_fn.attrs,
        }
    }

    pub fn attrs_mut(&mut self) -> &mut Vec<syn::Attribute> {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => &mut item_fn.attrs,
            FnItemWithSignature::ImplItemFn(impl_item_fn) => &mut impl_item_fn.attrs,
            FnItemWithSignature::TraitItemFn(trait_item_fn) => &mut trait_item_fn.attrs,
        }
    }

    pub fn sig(&self) -> &syn::Signature {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => &item_fn.sig,
            FnItemWithSignature::ImplItemFn(impl_item_fn) => &impl_item_fn.sig,
            FnItemWithSignature::TraitItemFn(trait_item_fn) => &trait_item_fn.sig,
        }
    }

    pub fn sig_mut(&mut self) -> &mut syn::Signature {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => &mut item_fn.sig,
            FnItemWithSignature::ImplItemFn(impl_item_fn) => &mut impl_item_fn.sig,
            FnItemWithSignature::TraitItemFn(trait_item_fn) => &mut trait_item_fn.sig,
        }
    }
}

fn extract_requires_ensures(func: &mut FnItemWithSignature) -> syn::Result<(syn::Expr, syn::Expr)> {
    let mut result = None;

    let requires_ensures_path: syn::Path = syn::parse_quote!(::thrust_macros::_requires_ensures);

    for attr in func.attrs() {
        if attr.path() == &requires_ensures_path {
            if result.is_some() {
                return Err(syn::Error::new_spanned(
                    attr,
                    "multiple _requires_ensures attributes found; expected at most one",
                ));
            }

            let parser = Punctuated::<syn::Expr, syn::Token![,]>::parse_separated_nonempty;
            let mut exprs = attr.parse_args_with(parser)?;
            if exprs.len() != 2 {
                return Err(syn::Error::new_spanned(
                    attr,
                    "expected exactly two comma-separated expressions in _requires_ensures attribute",
                ));
            }
            let ens_expr = exprs.pop().unwrap();
            let req_expr = exprs.pop().unwrap();
            result = Some((req_expr, ens_expr));
        }
    }

    func.attrs_mut()
        .retain(|attr| attr.path() != &requires_ensures_path);

    if let Some((req_expr, ens_expr)) = result {
        Ok((req_expr, ens_expr))
    } else {
        Ok((syn::parse_quote!(true), syn::parse_quote!(true)))
    }
}

fn extract_outer_context(func: &FnItemWithSignature) -> syn::Result<Option<FnOuterItem>> {
    let outer_context = crate::extract_outer_context(func.attrs())?;
    if mentions_self(func.sig()) && outer_context.is_none() {
        return Err(syn::Error::new_spanned(
            func.sig().ident.clone(),
            "Wrap the surrounding impl block or trait definition with #[thrust_macros::context] to annotate methods",
        ));
    }
    Ok(outer_context)
}

struct ExpandedTokens {
    func: FnItemWithSignature,
    /// `func`'s signature with argument-position `impl Trait` desugared into named
    /// generic parameters (see [`mod@crate::apit`]); the source of every generated
    /// companion's parameters and generics. Equal to `func`'s own signature unless it
    /// has such a parameter.
    sig: syn::Signature,

    requires_name: syn::Ident,
    ensures_name: syn::Ident,
    req_expr: syn::Expr,
    ens_expr: syn::Expr,

    def_generics: TokenStream2,
    /// Turbofish instantiating a companion, over `sig`'s generics.
    turbofish: TokenStream2,
    /// Turbofish for the call to the annotated function itself: empty when it takes an
    /// argument-position `impl Trait`, since rustc rejects explicit generic arguments
    /// for such a function and infers them from the call's arguments instead.
    target_turbofish: TokenStream2,

    outer_context: Option<FnOuterItem>,
}

impl quote::ToTokens for ExpandedTokens {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        if self.is_extern_spec_fn() {
            self.expand_extern_spec_fn().to_tokens(tokens);
        } else {
            self.expand().to_tokens(tokens);
        }
    }
}

impl ExpandedTokens {
    fn new(
        mut func: FnItemWithSignature,
        mut req_expr: syn::Expr,
        mut ens_expr: syn::Expr,
    ) -> Self {
        let impl_trait_names = apit::take_names(func.attrs_mut());
        let name = &func.sig().ident;
        let requires_name = format_ident!("_thrust_requires_{}", name);
        let ensures_name = format_ident!("_thrust_ensures_{}", name);

        let sig = apit::desugar_signature(func.sig(), &impl_trait_names);
        let def_generics = generic_params_tokens(&sig.generics);
        let turbofish = generic_turbofish(&sig.generics);
        let target_turbofish = if apit::count_arg_position_impl_traits(func.sig()) > 0 {
            quote!()
        } else {
            turbofish.clone()
        };

        if func.sig().receiver().is_some() {
            rewrite_self_in_expr(&mut req_expr);
            rewrite_self_in_expr(&mut ens_expr);
        }

        Self {
            func,
            sig,
            req_expr,
            ens_expr,
            requires_name,
            ensures_name,
            def_generics,
            turbofish,
            target_turbofish,
            outer_context: None,
        }
    }

    fn with_outer_context(mut self, outer_item: FnOuterItem) -> Self {
        self.outer_context = Some(outer_item);
        self
    }

    fn type_lowering(&self) -> FormulaFnTypeLowering<'_> {
        if let Some(outer_context) = &self.outer_context {
            FormulaFnTypeLowering::with_outer_context(&self.sig, outer_context)
        } else {
            FormulaFnTypeLowering::new(&self.sig)
        }
    }

    fn extended_where_clause(&self) -> TokenStream2 {
        let model_preds = self.type_lowering().model_where_predicates();
        extended_where_clause(&self.func, &model_preds)
    }

    fn is_extern_spec_fn(&self) -> bool {
        let extern_spec_fn_path: syn::Path = syn::parse_quote!(thrust::extern_spec_fn);
        self.func
            .attrs()
            .iter()
            .any(|a| a.path() == &extern_spec_fn_path)
    }

    fn requires_fn(&self) -> TokenStream2 {
        let requires_name = &self.requires_name;
        let def_generics = &self.def_generics;
        let model_ty_params = self.type_lowering().lower_params(&self.sig.inputs);
        let extended_where = self.extended_where_clause();
        let req_expr = &self.req_expr;

        quote! {
            #[allow(unused_variables)]
            #[allow(non_snake_case)]
            #[thrust::formula_fn]
            fn #requires_name #def_generics(#model_ty_params) -> bool #extended_where {
                #req_expr
            }
        }
    }

    fn ensures_fn(&self) -> TokenStream2 {
        let ensures_name = &self.ensures_name;
        let def_generics = &self.def_generics;
        let model_ty_params = &self.type_lowering().lower_params(&self.sig.inputs);
        let extended_where = self.extended_where_clause();
        let ret_model_ty = &self.type_lowering().lower_return_type(&self.sig.output);
        let ens_expr = &self.ens_expr;

        quote! {
            #[allow(unused_variables)]
            #[allow(non_snake_case)]
            #[thrust::formula_fn]
            fn #ensures_name #def_generics(result: #ret_model_ty, #model_ty_params) -> bool #extended_where {
                #ens_expr
            }
        }
    }

    fn path_prefix(&self) -> Option<TokenStream2> {
        self.outer_context.as_ref()?;
        Some(quote!(Self::))
    }

    fn expand(&self) -> TokenStream2 {
        let mut func = self.func.clone();
        let trusted_path: syn::Path = syn::parse_quote!(thrust::trusted);
        for attr in func.attrs_mut() {
            if attr.path() == &trusted_path {
                *attr = syn::parse_quote!(#[thrust::ignored]);
            }
        }

        let requires_fn = self.requires_fn();
        let ensures_fn = self.ensures_fn();

        let extern_spec_name = format_ident!("_thrust_extern_spec_{}", self.func.sig().ident);
        let def_generics = &self.def_generics;
        let orig_output = &self.func.sig().output;
        let extended_where = self.extended_where_clause();

        let requires_name = &self.requires_name;
        let ensures_name = &self.ensures_name;
        let turbofish = &self.turbofish;
        let path_prefix = self.path_prefix();

        let name = &self.func.sig().ident;
        let target_turbofish = &self.target_turbofish;
        let (extern_spec_inputs, call_args) = rewrite_inputs_for_call(&self.sig.inputs);

        quote! {
            #func

            #requires_fn
            #ensures_fn

            #[thrust::extern_spec_fn]
            #[allow(path_statements)]
            fn #extern_spec_name #def_generics(#extern_spec_inputs) #orig_output #extended_where {
                #[thrust::requires_path]
                #path_prefix #requires_name #turbofish;

                #[thrust::ensures_path]
                #path_prefix #ensures_name #turbofish;

                #path_prefix #name #target_turbofish(#call_args)
            }
        }
    }

    fn expand_extern_spec_fn(&self) -> TokenStream2 {
        let requires_name = &self.requires_name;
        let ensures_name = &self.ensures_name;
        let turbofish = &self.turbofish;
        let path_prefix = self.path_prefix();

        let mut func = self.func.clone();
        // The marker statements below turbofish the companions with the fresh
        // `impl Trait` parameters, which only a desugared signature can name.
        *func.sig_mut() = self.sig.clone();
        let func_tokens = if let Some(block) = func.block_mut() {
            let orig_stmts = block.stmts.drain(..).collect::<Vec<_>>();
            *block = syn::parse_quote!({
                #[thrust::requires_path]
                #path_prefix #requires_name #turbofish;

                #[thrust::ensures_path]
                #path_prefix #ensures_name #turbofish;

                #(#orig_stmts)*
            });
            quote! {
                #[allow(path_statements)]
                #func
            }
        } else {
            let error = syn::Error::new_spanned(
                func.sig().ident.clone(),
                "extern_spec_fn must have a function body",
            )
            .into_compile_error();
            quote! {
                #error
                #func
            }
        };

        let requires_fn = self.requires_fn();
        let ensures_fn = self.ensures_fn();

        quote! {
            #requires_fn
            #ensures_fn

            #func_tokens
        }
    }
}

fn mentions_self(sig: &syn::Signature) -> bool {
    struct Visitor {
        mentions_self: bool,
    }

    impl syn::visit::Visit<'_> for Visitor {
        fn visit_ident(&mut self, i: &syn::Ident) {
            if i == "self" || i == "Self" {
                self.mentions_self = true;
            }
        }
    }

    let mut visitor = Visitor {
        mentions_self: false,
    };
    use syn::visit::Visit as _;
    visitor.visit_signature(sig);
    visitor.mentions_self
}

struct RewriteSelf;

impl syn::visit_mut::VisitMut for RewriteSelf {
    fn visit_ident_mut(&mut self, ident: &mut syn::Ident) {
        if ident == "self" {
            *ident = format_ident!("self_");
        }
    }

    // syn skips macro token streams, so rewrite `self` inside the
    // `formula!(..)` wrapper by hand.
    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        let self_ = format_ident!("self_");
        mac.tokens = std::mem::take(&mut mac.tokens)
            .into_iter()
            .map(|tt| rewrite_self_in_tokens(tt, &self_))
            .collect();
    }
}

fn rewrite_self_in_expr(expr: &mut syn::Expr) {
    use syn::visit_mut::VisitMut as _;
    RewriteSelf.visit_expr_mut(expr);
}

fn rewrite_self_in_block(block: &mut syn::Block) {
    use syn::visit_mut::VisitMut as _;
    RewriteSelf.visit_block_mut(block);
}

/// Replaces a `self` identifier with `self_`, recursing into groups. Operates on
/// a single token tree so callers can `map` it over a stream.
pub fn rewrite_self_in_tokens(token: impl Into<TokenTree>, self_: &Ident) -> TokenTree {
    match token.into() {
        TokenTree::Ident(id) if id == "self" => TokenTree::Ident(self_.clone()),
        TokenTree::Group(g) => {
            let inner = g
                .stream()
                .into_iter()
                .map(|tt| rewrite_self_in_tokens(tt, self_))
                .collect();
            let mut new_group = Group::new(g.delimiter(), inner);
            new_group.set_span(g.span());
            TokenTree::Group(new_group)
        }
        other => other,
    }
}

/// Returns `<T: Bound, U, 'a>` — the generic param list for function definitions,
/// without a where clause.
pub fn generic_params_tokens(generics: &Generics) -> TokenStream2 {
    if generics.params.is_empty() {
        return quote!();
    }
    let params = &generics.params;
    quote!(<#params>)
}

/// Returns `::<T, U>` for turbofish use, or nothing if no generic params.
pub fn generic_turbofish(generics: &Generics) -> TokenStream2 {
    let args: Vec<TokenStream2> = generics
        .params
        .iter()
        .flat_map(|p| match p {
            GenericParam::Type(tp) => Some(tp.ident.to_token_stream()),
            GenericParam::Lifetime(_) => None,
            GenericParam::Const(cp) => Some(cp.ident.to_token_stream()),
        })
        .collect();
    if args.is_empty() {
        return quote!();
    }
    quote!(::<#(#args),*>)
}

/// For the extern_spec wrapper: replaces every typed parameter with a fresh `_arg_N` ident,
/// returning `(rewritten_inputs_tokens, call_args_tokens)`.
fn rewrite_inputs_for_call(
    inputs: &syn::punctuated::Punctuated<FnArg, syn::token::Comma>,
) -> (TokenStream2, TokenStream2) {
    let mut rewritten: Vec<TokenStream2> = Vec::new();
    let mut call_args: Vec<TokenStream2> = Vec::new();

    for (i, arg) in inputs.iter().enumerate() {
        match arg {
            FnArg::Typed(pt) => {
                let fresh = format_ident!("_arg_{}", i);
                let ty = &pt.ty;
                rewritten.push(quote!(#fresh: #ty));
                call_args.push(fresh.to_token_stream());
            }
            FnArg::Receiver(_) => {
                rewritten.push(arg.to_token_stream());
                call_args.push(quote!(self));
            }
        }
    }

    (quote!(#(#rewritten),*), quote!(#(#call_args),*))
}

/// Builds `where <original predicates>, <model predicates>`.
/// Returns an empty token stream when both sets are empty.
pub fn extended_where_clause(
    func: &FnItemWithSignature,
    model_preds: &Vec<syn::WherePredicate>,
) -> TokenStream2 {
    let existing: Vec<&WherePredicate> = func
        .sig()
        .generics
        .where_clause
        .as_ref()
        .map(|wc| wc.predicates.iter().collect())
        .unwrap_or_default();

    if existing.is_empty() && model_preds.is_empty() {
        return quote!();
    }

    quote! { where #(#existing,)* #(#model_preds),* }
}
