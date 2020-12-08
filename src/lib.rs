//! Derive macro for [`syn::parse::Parse`]
//!
//! A common pattern when writing custom `syn` parsers is repeating `<name>: input.parse()?` for
//! each field in the output. `#[derive(Parse)]` handles that for you, with some extra helpful
//! customization.
//!
//! ## Usage
//!
//! Using this crate is as simple as adding it to your 'Cargo.toml' and importing the derive macro:
//!
//! ```toml
//! # Cargo.toml
//!
//! [dependencies]
//! derive-syn-parse = "0.1"
//! ```
//!
//! ```
//! // your_file.rs
//! use derive_syn_parse::Parse;
//!
//! #[derive(Parse)]
//! struct CustomParsable {
//!     // ...
//! }
//! ```
//!
//! The derived implementation of `Parse` always parses in the order that the fields are given.
//! **Note that deriving `Parse` is also available on enums.** For more information, see the
//! [dedicated section](#enum-parsing).
//!
//! This crate is intended for users who are already making heavy use of `syn`.
//!
//! ## Motivation
//!
//! When writing rust code that makes heavy use of `syn`'s parsing functionality, we often end up
//! writing things like:
//! ```
//! use syn::parse::{Parse, ParseStream};
//! use syn::{Ident, Token, Type};
//!
//! // A simplified struct field
//! //
//! //     x: i32
//! struct MyField {
//!     ident: Ident,
//!     colon_token: Token![:],
//!     ty: Type,
//! }
//!
//! impl Parse for MyField {
//!     fn parse(input: ParseStream) -> syn::Result<Self> {
//!         Ok(MyField {
//!             ident: input.parse()?,
//!             colon_token: input.parse()?,
//!             ty: input.parse()?,
//!         })
//!     }
//! }
//! ```
//! This is really repetitive! Ideally, we'd like to just `#[derive(Parse)]` and have it work. And
//! so we can! (for the most part) Adding `#[derive(Parse)]` to the previous struct produces an
//! equivalent implementation of `Parse`:
//! ```
//! use syn::{Ident, Token, Type};
//! use derive_syn_parse::Parse;
//!
//! #[derive(Parse)]
//! struct MyField {
//!     ident: Ident,
//!     colon_token: Token![:],
//!     ty: Type,
//! }
//! ```
//!
//! Of course, there are more complicated cases. This is mainly covered below in the 'Advanced
//! usage' section.
//!
//! ## Enum parsing
//!
//! Parsing `enum`s is a complex feature. When writing manual implementations of `Parse`, it
//! doesn't come up as often, but there are also typically *many* ways to do it: `syn` provides
//! both forking the `ParseBuffer` *and* peeking in order to handle this, with peeking to be
//! preferred if possible.
//!
//! This library does not support forking; it tends to suffer from poor error messages and general
//! inefficiency. That being said, manual implementations of `Parse` can and should be written when
//! this library is insufficient.
//!
//! We *do* support peeking - in two different ways. These are handled by the `#[peek]` and
//! `#[peek_with]` attributes, which are required on- and only available for `enum` variants. The
//! general syntax can be thought of as:
//!
//! ```text
//! #[peek($TYPE, name = $NAME)]
//! ```
//! and
//! ```text
//! #[peek_with($EXPR, name = $NAME)]
//! ```
//! where `$TYPE`, `$EXPR`, and `$NAME` are meta-variables that correspond to the particular input
//! given to the attribute.
//!
//! These can be thought of as translating literally to:
//! ```ignore
//! if input.peek($TYPE) {
//!     // parse variant
//! } else {
//!     // parse other variants
//! }
//! ```
//! and
//! ```ignore
//! if ($EXPR)(input) {
//!     // parse variant
//! } else {
//!     // parse other variants
//! }
//! ```
//! respectively. If no variant matches, we produce an error message, using the names that were
//! provided for each type.
//!
//! ## Advanced usage
//!
//! There's a moderate collection of helper attributes that can be applied to fields to customize
//! the generated implementation of `Parse`. Each of these are demonstrated with the
//! implementation that they produce. Please note that the produced implementation is typically
//! *not* identical to what's shown here.
//!
//! All of the examples are fairly contrived, I know. The reality of the matter is that - if you
//! would find this useful - it's probably true that your use-case is much more complicated than
//! would make sense for a short example. (If it isn't, let me know! It would be great to include
//! it here!)
//!
//! ### List of helper attributes
//! - [`#[paren]`](#paren--bracket--brace)
//! - [`#[bracket]`](#paren--braket--brace)
//! - [`#[brace]`](#paren--bracket--brace)
//! - [`#[inside]`](#inside)
//! - [`#[call]`](#call)
//! - [`#[parse_terminated]`](#parse_terminated)
//! - [`#[peek]`](#enum-parsing)
//! - [`#[peek_with]`](#enum-parsing)
//!
//! ### `#[paren]` / `#[bracket]` / `#[brace]`
//!
//! Because the derive macro has no fool-proof method for determining by itself whether a field type
//! is any of `syn::token::{Paren, Bracket, Brace}`, these three serve to provide that information
//! instead.
//!
//! These are typically used in conjunction with [`#[inside]`](#inside).
//!
//! ```
//! # use syn::{Ident, token::Paren, Expr};
//! # use derive_syn_parse::Parse;
//!
//! // A single-argument function call
//! //
//! //     so_long(and_thanks + for_all * the_fish)
//! #[derive(Parse)]
//! struct SingleArgFn {
//!     ident: Ident,
//!     #[paren]
//!     paren_token: Paren,
//!     #[inside(paren_token)]
//!     arg: Expr,
//! }
//! ```
//! produces
//! ```
//! # use syn::parse::{Parse, ParseStream};
//! # use syn::{Ident, token::Paren, Expr};
//! # struct SingleArgFn { ident: Ident, paren_token: Paren, arg: Expr }
//!
//! impl Parse for SingleArgFn {
//!     fn parse(input: ParseStream) -> syn::Result<Self> {
//!         let paren;
//!         Ok(SingleArgFn {
//!             ident: input.parse()?,
//!             paren_token: syn::parenthesized!(paren in input),
//!             arg: paren.parse()?,
//!         })
//!     }
//! }
//! ```
//!
//! ### `#[inside(..)]`
//!
//! This is a companion to `#[paren]`/`#[bracket]`/`#[brace]` - given a field name to use, this
//! attribute indicates that the field should be parsed using a previous field as the source.
//!
//! ```
//! # use derive_syn_parse::Parse;
//! use syn::{Type, Token, Expr};
//! use syn::token::Bracket;
//!
//! // An array type required to have a length
//! //
//! //     [i32; 4]
//! #[derive(Parse)]
//! struct KnownLengthArrayType {
//!     #[bracket]
//!     bracket_token: Bracket,
//!
//!     // Note that `#[inside(..)]` must be applied to all of the fields that
//!     // are in the brackets!
//!     #[inside(bracket_token)]
//!     ty: Type,
//!     #[inside(bracket_token)]
//!     semi_token: Token![;],
//!     #[inside(bracket_token)]
//!     expr: Expr,
//! }
//! ```
//! produces
//! ```
//! # use syn::parse::{Parse, ParseStream};
//! # use syn::{Type, Token, Expr};
//! # use syn::token::Bracket;
//! # struct KnownLengthArrayType { bracket_token: Bracket, ty: Type, semi_token: Token![;], expr: Expr }
//!
//! impl Parse for KnownLengthArrayType {
//!     fn parse(input: ParseStream) -> syn::Result<Self> {
//!         let bracket;
//!         Ok(KnownLengthArrayType {
//!             bracket_token: syn::bracketed!(bracket in input),
//!             ty: bracket.parse()?,
//!             semi_token: bracket.parse()?,
//!             expr: bracket.parse()?,
//!         })
//!     }
//! }
//! ```
//!
//! ### `#[call(..)]`
//!
//! Given a path to a function, this attribute specifies that the value of the field should be
//! instead calculated by a call to `input.parse(..)` with a given path. The best example is taken
//! straight from the [`syn` documentation itself](syn::parse::ParseBuffer::call):
//! ```
//! # use derive_syn_parse::Parse;
//! use syn::{Attribute, Ident, Token};
//!
//! // Parses a unit struct with attributes.
//! //
//! //     #[path = "s.tmpl"]
//! //     struct S;
//! #[derive(Parse)]
//! struct UnitStruct {
//!     #[call(Attribute::parse_outer)]
//!     attrs: Vec<Attribute>,
//!     struct_token: Token![struct],
//!     name: Ident,
//!     semi_token: Token![;],
//! }
//! ```
//! produces
//! ```
//! # use syn::parse::{Parse, ParseStream};
//! # use syn::{Attribute, Ident, Token};
//! # struct UnitStruct { attrs: Vec<Attribute>, struct_token: Token![struct], name: Ident, semi_token: Token![;] }
//!
//! impl Parse for UnitStruct {
//!     fn parse(input: ParseStream) -> syn::Result<Self> {
//!         Ok(UnitStruct {
//!             attrs: input.call(Attribute::parse_outer)?,
//!             struct_token: input.parse()?,
//!             name: input.parse()?,
//!             semi_token: input.parse()?,
//!         })
//!     }
//! }
//! ```
//!
//!
//! ### `#[parse_terminated(..)]`
//!
//! Just as we have [`#[call(..)]`](#call) for [`ParseStream::call`], we have `#[parse_terminated]`
//! for [`ParseStream::parse_terminated`]. Here's the same example that the `ParseStream` method
//! uses:
//!
//! ```
//! # use syn::{Ident, token, Token, Type, punctuated::Punctuated};
//! # use derive_syn_parse::Parse;
//!
//! // Parse a simplified tuple struct syntax like:
//! //
//! //     struct S(A, B);
//! #[derive(Parse)]
//! struct TupleStruct {
//!     struct_token: Token![struct],
//!     ident: Ident,
//!     #[paren]
//!     paren_token: token::Paren,
//!     #[inside(paren_token)]
//!     #[parse_terminated(Type::parse)]
//!     fields: Punctuated<Type, Token![,]>,
//!     semi_token: Token![;],
//! }
//! ```
//! produces
//! ```
//! # use syn::parse::{Parse, ParseStream};
//! # use syn::{Ident, token, Token, Type, punctuated::Punctuated, parenthesized};
//! # struct TupleStruct {
//! #     struct_token: Token![struct], ident: Ident, paren_token: token::Paren, fields: Punctuated<Type, Token![,]>, semi_token: Token![;],
//! # }
//!
//! impl Parse for TupleStruct {
//!     fn parse(input: ParseStream) -> syn::Result<Self> {
//!         let content;
//!         Ok(TupleStruct {
//!             struct_token: input.parse()?,
//!             ident: input.parse()?,
//!             paren_token: parenthesized!(content in input),
//!             fields: content.parse_terminated(Type::parse)?,
//!             semi_token: input.parse()?,
//!         })
//!     }
//! }
//!
//! ```
//!
//! [`Punctuated`]: syn::punctuated::Punctuated
//!
//! [`ParseStream::call`]: syn::parse::ParseBuffer::call
//! [`ParseStream::parse_terminated`]: syn::parse::ParseBuffer::parse_terminated
//! [`ParseStream::peek`]: syn::parse::ParseBuffer::peek
//! [`ParseStream::fork`]: syn::parse::ParseBuffer::fork

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;
use syn::{parse_macro_input, AttrStyle, Attribute, Data, DeriveInput, Ident, Result};

#[macro_use]
mod error_macros;

mod fields;
#[cfg(test)]
mod tests;
mod variants;

#[proc_macro_derive(
    Parse,
    attributes(
        paren,
        bracket,
        brace,
        inside,
        call,
        parse_terminated,
        peek,
        peek_with,
        no_parse_bound
    )
)]
pub fn derive_parse(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(item as DeriveInput);
    derive_parse_internal(input).into()
}

// Pulled into a separate function so we can test it
pub(crate) fn derive_parse_internal(input: DeriveInput) -> TokenStream {
    // The generic parameters following `impl`
    let mut generics_intro = TokenStream::new();
    // The generic arguments following the name of the type
    let mut generics_args = TokenStream::new();

    let where_clause = input.generics.where_clause;

    let generic_params: Vec<_> = input.generics.params.into_iter().collect();
    if !generic_params.is_empty() {
        let generics_intros: Vec<_> = handle_syn_result! {
            generic_params.iter()
                .map(require_impl_parse_if_type)
                .collect()
        };
        generics_intro = quote!( < #( #generics_intros ),* > );
        let generics_args_list: Vec<_> = generic_params.into_iter().map(convert_to_arg).collect();
        generics_args = quote!( < #( #generics_args_list ),* > );
    }

    let ident = input.ident;

    let parse_impl = match input.data {
        Data::Union(u) => invalid_input_kind!(u.union_token),
        Data::Struct(s) => handle_syn_result! {
            @default_impl_from(generics_intro, ident, generics_args, where_clause),
            fields::generate_fn_body(&ident, s.fields, false)
        },
        Data::Enum(e) => handle_syn_result! {
            @default_impl_from(generics_intro, ident, generics_args, where_clause),
            variants::generate_impl(e.variants.into_iter())
        },
    };

    let parse_input = parse_input();
    quote!(
        impl #generics_intro syn::parse::Parse for #ident #generics_args #where_clause {
            fn parse(#parse_input: syn::parse::ParseStream) -> syn::Result<Self> {
                #parse_impl
            }
        }
    )
}

// Produces the tokens for the generic parameter, adding `+ syn::parse::Parse`
fn require_impl_parse_if_type(param: &syn::GenericParam) -> Result<TokenStream> {
    use syn::GenericParam::Type;
    use syn::TypeParam;

    let TypeParam {
        attrs,
        ident,
        colon_token,
        bounds,
        eq_token,
        default,
    } = match param {
        Type(t) if !any_attr_allows_no_parse(&t.attrs)? => t,
        param => return Ok(param.to_token_stream()),
    };

    // If we have `struct Foo<T>`,      we need to add `: Parse`, but
    // if we have `struct Foo<T: Bar>`, we need to add `+ Parse`
    let parse_bound = if colon_token.is_some() {
        quote_spanned! {
            ident.span()=>
            + syn::parse::Parse
        }
    } else {
        quote_spanned! {
            ident.span()=>
            : syn::parse::Parse
        }
    };

    Ok(quote! {
        #( #attrs )*
        #ident #colon_token #bounds #parse_bound #eq_token #default
    })
}

// Returns true if and only if there's an attribute that's exactly `#[no_parse_bound]`
fn any_attr_allows_no_parse(attrs: &[Attribute]) -> Result<bool> {
    attrs
        .iter()
        .try_fold(false, |acc, a| Ok(acc || attr_allows_no_parse(a)?))
}

// Returns true if and only if the attribute is `#[no_parse_bound]`
fn attr_allows_no_parse(attr: &Attribute) -> Result<bool> {
    if let AttrStyle::Inner(_) = &attr.style {
        return Err(syn::Error::new(
            attr.span(),
            "`#[no_parse_bound]` must be an outer attribute",
        ));
    }

    let Attribute { path, tokens, .. } = attr;
    if path.get_ident().map(ToString::to_string) != Some("no_parse_bound".into()) {
        return Ok(false);
    }

    if !tokens.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "`#[no_parse_bound]` does not expect arguments",
        ));
    }

    Ok(true)
}

fn convert_to_arg(param: syn::GenericParam) -> TokenStream {
    use syn::GenericParam::{Const, Lifetime, Type};

    match param {
        Type(ty) => ty.ident.to_token_stream(),
        Lifetime(lifetime) => lifetime.to_token_stream(),
        Const(con) => {
            let ident = &con.ident;
            quote_spanned!(con.span()=> { #ident })
        }
    }
}

// A helper macro to give the identifier used to represent the ParseStream used as input to the
// macro
fn parse_input() -> Ident {
    Ident::new("__parse_input", Span::call_site())
}
