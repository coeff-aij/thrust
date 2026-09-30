//! `#[derive(thrust_macros::Model)]` on a struct `S` declares the model struct `SModel`: the
//! fields of `S` in the same order and under the same names, each of the type
//! `<F as thrust_models::Model>::Ty` of its field. `S` is modelled by `SModel`, and `SModel` by
//! itself.
//!
//! The order matters: a field of `S` is read in the program by its position, and a field of
//! `SModel` in a specification by its name.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

pub fn expand(input: syn::DeriveInput) -> TokenStream {
    let syn::Data::Struct(data) = &input.data else {
        return syn::Error::new_spanned(&input.ident, "`derive(Model)` supports structs only")
            .to_compile_error();
    };
    let vis = &input.vis;
    let name = &input.ident;
    let model_name = format_ident!("{}Model", name);
    let generics = with_model_bounds(&input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let fields = model_fields(&data.fields);
    let body = match &data.fields {
        syn::Fields::Named(_) => quote!(#where_clause #fields),
        syn::Fields::Unnamed(_) => quote!(#fields #where_clause;),
        syn::Fields::Unit => quote!(#where_clause;),
    };
    let params = &generics.params;
    let eq_impl = partial_eq_impl(&generics, &model_name);

    quote! {
        #[allow(dead_code)]
        #vis struct #model_name<#params> #body

        impl #impl_generics crate::thrust_models::Model for #name #ty_generics #where_clause {
            type Ty = #model_name #ty_generics;
        }

        impl #impl_generics crate::thrust_models::Model for #model_name #ty_generics #where_clause {
            type Ty = Self;
        }

        #eq_impl
    }
}

fn with_model_bounds(generics: &syn::Generics) -> syn::Generics {
    let mut generics = generics.clone();
    let type_params: Vec<syn::Ident> = generics.type_params().map(|p| p.ident.clone()).collect();
    let where_clause = generics.make_where_clause();
    for param in type_params {
        where_clause
            .predicates
            .push(syn::parse_quote!(#param: crate::thrust_models::Model));
    }
    generics
}

fn model_fields(fields: &syn::Fields) -> syn::Fields {
    let mut fields = fields.clone();
    for field in fields.iter_mut() {
        let ty = &field.ty;
        field.ty = syn::parse_quote!(<#ty as crate::thrust_models::Model>::Ty);
        field.attrs.clear();
    }
    fields
}

/// Equality with any value of the same model, as the model types of `thrust_models` have it.
fn partial_eq_impl(generics: &syn::Generics, model_name: &syn::Ident) -> TokenStream {
    let (_, ty_generics, _) = generics.split_for_impl();
    let mut eq_generics = generics.clone();
    eq_generics.params.push(syn::parse_quote!(__ThrustOther));
    eq_generics
        .make_where_clause()
        .predicates
        .push(syn::parse_quote!(__ThrustOther: crate::thrust_models::Model<Ty = Self>));
    let (impl_generics, _, where_clause) = eq_generics.split_for_impl();
    quote! {
        impl #impl_generics PartialEq<__ThrustOther> for #model_name #ty_generics #where_clause {
            #[thrust::ignored]
            fn eq(&self, _other: &__ThrustOther) -> bool {
                unimplemented!()
            }
        }
    }
}
