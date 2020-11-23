//! Handling for generating a `Parse` implementation using fields

use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, quote_spanned, ToTokens};
use std::convert::{TryFrom, TryInto};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{parenthesized, AttrStyle, Attribute, Expr, Fields, Ident, Path, Result, Token};

pub(crate) fn generate_fn_body(
    base_tyname: &impl ToTokens,
    fields: Fields,
    with_return: bool,
) -> Result<TokenStream> {
    let initialize_self = initialize_type_or_variant(base_tyname, &fields);
    let parse_fields = fields
        .into_iter()
        .enumerate()
        .map(parse_field)
        .collect::<Result<Vec<_>>>()?;

    let maybe_return = match with_return {
        true => Token![return](Span::call_site()).into_token_stream(),
        false => TokenStream::new(),
    };

    Ok(quote! {
        #( #parse_fields )*

        #maybe_return Ok(#initialize_self)
    })
}

enum FieldAttr {
    Inside(Ident),
    Tree(TreeKind),
    Call(Path),
    ParseTerminated(Path),
    Peek(PeekAttr),
}

enum TreeKind {
    Paren,
    Bracket,
    Brace,
}

enum ParseMethod {
    Tree(TreeKind, Span),
    Call(Path),
    ParseTerminated(Path),
    Default,
}

enum PeekAttr {
    Peek(Expr),
    PeekWith(Expr),
}

impl ParseMethod {
    fn is_default(&self) -> bool {
        matches!(self, Self::Default)
    }
}

struct FieldAttrs {
    inside: Option<Ident>,
    parse_method: ParseMethod,
    peek: Option<PeekAttr>,
}

struct ParseField {
    required_var_defs: Option<Ident>,
    parse_expr: TokenStream,
    // input_source: Ident,
    // parse_method: TokenStream,
}

// This needs to return tokenstreams because tuple structs use integer indices as field names
//
// For example: We'd end up writing the following
//   Ok(Self {
//       0: _field_0,
//       1: _field_1,
//       ...
//   })
//
// Otherwise, we would totally just return a list of identifiers
fn initialize_type_or_variant(name: &impl ToTokens, fields: &syn::Fields) -> TokenStream {
    use syn::Fields::{Named, Unit, Unnamed};

    match fields {
        Unit => name.to_token_stream(),
        Named(fields) => {
            let iter = fields.named.iter().map(|f| {
                f.ident
                    .as_ref()
                    .expect("named field was unnamed! the impossible is now possible!")
            });
            quote! {
                #name { #( #iter, )* }
            }
        }
        Unnamed(fields) => {
            let iter = fields
                .unnamed
                .iter()
                .enumerate()
                .map(|(i, f)| field_name_for_idx(i, f.span()));
            quote! {
                #name( #( #iter, )* )
            }
        }
    }
}

fn field_name_for_idx(idx: usize, span: Span) -> Ident {
    format_ident!("_field_{}", idx, span = span)
}

fn parse_field((idx, field): (usize, syn::Field)) -> Result<TokenStream> {
    let span = field.span();

    let assigned_name = field.ident.unwrap_or_else(|| field_name_for_idx(idx, span));

    let attrs = (field.attrs)
        .into_iter()
        .filter_map(try_as_field_attr)
        .collect::<Result<Vec<_>>>()?
        .try_into()?;

    let ParseField {
        required_var_defs,
        parse_expr,
    } = handle_field_attrs(&assigned_name, field.ty.span(), attrs);

    // convert the Option to an iterator, so we can declare variables conditionally:
    let required_var_defs = required_var_defs.into_iter();
    Ok(quote_spanned! {
        span=>
        #( let #required_var_defs; )*
        let #assigned_name = #parse_expr;
    })
}

fn try_as_field_attr(attr: Attribute) -> Option<Result<(FieldAttr, Span)>> {
    let name = attr.path.get_ident()?.to_string();
    let span = attr.span();

    macro_rules! expect_outer_attr {
        () => {{
            if let AttrStyle::Inner(_) = attr.style {
                return Some(Err(syn::Error::new(
                    span,
                    "this parsing attribute can only be used as an outer attribute",
                )));
            }
        }};
    }

    #[rustfmt::skip]
    macro_rules! expect_no_attr_args {
        ($name:expr) => {{
            if !attr.tokens.is_empty() {
                return Some(Err(syn::Error::new(
                    span,
                    concat!("the ", $name, " parsing attribute does not expect any arguments"),
                )));
            }
        }};
    }

    struct Inside<T: Parse> {
        _paren_token: syn::token::Paren,
        inner: T,
    }

    impl<T: Parse> Parse for Inside<T> {
        fn parse(input: ParseStream) -> Result<Self> {
            let paren;
            Ok(Inside {
                _paren_token: parenthesized!(paren in input),
                inner: paren.parse()?,
            })
        }
    }

    match name.as_str() {
        "inside" => {
            expect_outer_attr!();
            Some(
                syn::parse2(attr.tokens)
                    .map(move |id: Inside<_>| (FieldAttr::Inside(id.inner), span)),
            )
        }
        "call" => {
            expect_outer_attr!();
            Some(
                syn::parse2(attr.tokens)
                    .map(move |id: Inside<_>| (FieldAttr::Call(id.inner), span)),
            )
        }
        "parse_terminated" => {
            expect_outer_attr!();
            Some(
                syn::parse2(attr.tokens)
                    .map(move |id: Inside<_>| (FieldAttr::ParseTerminated(id.inner), span)),
            )
        }
        "paren" => {
            expect_outer_attr!();
            expect_no_attr_args!("`#[paren]`");
            Some(Ok((FieldAttr::Tree(TreeKind::Paren), span)))
        }
        "bracket" => {
            expect_outer_attr!();
            expect_no_attr_args!("`#[bracket]`");
            Some(Ok((FieldAttr::Tree(TreeKind::Bracket), span)))
        }
        "brace" => {
            expect_outer_attr!();
            expect_no_attr_args!("`#[brace]`");
            Some(Ok((FieldAttr::Tree(TreeKind::Brace), span)))
        }
        "peek" => {
            expect_outer_attr!();
            Some(
                syn::parse2(attr.tokens)
                    .map(move |id: Inside<_>| (FieldAttr::Peek(PeekAttr::Peek(id.inner)), span)),
            )
        }
        "peek_with" => {
            expect_outer_attr!();
            Some(
                syn::parse2(attr.tokens).map(move |id: Inside<_>| {
                    (FieldAttr::Peek(PeekAttr::PeekWith(id.inner)), span)
                }),
            )
        }
        _ => None,
    }
}

impl TryFrom<Vec<(FieldAttr, Span)>> for FieldAttrs {
    type Error = syn::Error;

    fn try_from(vec: Vec<(FieldAttr, Span)>) -> Result<Self> {
        use FieldAttr::{Call, Inside, ParseTerminated, Peek, Tree};

        let mut inside = None;
        let mut peek = None;
        let mut parse_method = ParseMethod::Default;

        for (attr, span) in vec {
            match attr {
                Tree(_) | Call(_) | ParseTerminated(_) if !parse_method.is_default() => {
                    return Err(syn::Error::new(span, "parsing method specified twice"));
                }
                Inside(_) if inside.is_some() => {
                    return Err(syn::Error::new(
                        span,
                        "containing parse stream is specified twice",
                    ));
                }
                Peek(_) if peek.is_some() => {
                    return Err(syn::Error::new(span, "peeking can only be specified once"));
                }

                Call(path) => parse_method = ParseMethod::Call(path),
                ParseTerminated(path) => parse_method = ParseMethod::ParseTerminated(path),
                Tree(kind) => parse_method = ParseMethod::Tree(kind, span),
                Inside(name) => inside = Some(name),
                Peek(p) => peek = Some(p),
            }
        }

        Ok(FieldAttrs {
            inside,
            parse_method,
            peek,
        })
    }
}

fn handle_field_attrs(field_name: &Ident, ty_span: Span, attrs: FieldAttrs) -> ParseField {
    use ParseMethod::{Call, Default, ParseTerminated, Tree};

    let input_source = attrs
        .inside
        .as_ref()
        .map(tree_name)
        .unwrap_or_else(crate::parse_input);

    let required_var_defs;
    let mut parse_expr;

    match attrs.parse_method {
        Default => {
            required_var_defs = None;
            parse_expr = quote_spanned! { ty_span=> #input_source.parse()? };
        }
        Call(path) => {
            required_var_defs = None;
            parse_expr = quote_spanned! { path.span()=> #input_source.call(#path)? };
        }
        ParseTerminated(path) => {
            required_var_defs = None;
            parse_expr = quote_spanned! { path.span()=> #input_source.parse_terminated(#path)? };
        }
        Tree(tree_kind, span) => {
            required_var_defs = Some(tree_name(field_name));

            let macro_name = tree_kind.macro_name();
            let tree_name = tree_name(field_name);
            parse_expr = quote_spanned! { span=> syn::#macro_name!(#tree_name in #input_source) };
        }
    }

    if let Some(p) = attrs.peek {
        parse_expr = match p {
            PeekAttr::Peek(expr) => quote_spanned!(expr.span()=> match #input_source.peek(#expr) {
                true => Some(#parse_expr),
                false => None,
            }),
            PeekAttr::PeekWith(expr) => quote_spanned!(expr.span()=> match (#expr)(#input_source) {
                true => Some(#parse_expr),
                false => None,
            }),
        };
    }

    ParseField {
        required_var_defs,
        parse_expr,
    }
}

fn tree_name(field_name: &Ident) -> Ident {
    format_ident!("__{}_backing_token_stream", field_name)
}

impl TreeKind {
    // Gives the name of the syn macro that corresponds to attempting parse the next token as a
    // certain group
    fn macro_name(&self) -> Ident {
        let span = Span::call_site();
        match self {
            TreeKind::Paren => Ident::new("parenthesized", span),
            TreeKind::Bracket => Ident::new("bracketed", span),
            TreeKind::Brace => Ident::new("braced", span),
        }
    }
}
