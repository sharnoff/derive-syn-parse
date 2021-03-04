use quote::ToTokens;
use syn::{parse2, parse_str, DeriveInput, ItemImpl};

macro_rules! test_all {
    ($($test_name:ident: { $input:expr, $output:expr $(,)? }),* $(,)?) => {
        $(
        #[test]
        fn $test_name() {
            let input: DeriveInput = parse_str($input).expect("failed to parse input");
            let expected: ItemImpl = parse_str($output).expect("failed to parse expected output");
            let output_tokens = crate::derive_parse_internal(input);
            let output: ItemImpl = parse2(output_tokens.clone())
                .unwrap_or_else(|err| panic!(
                    "failed to parse output: {}\noutput_tokens = {:?}",
                    err,
                    output_tokens.to_string(),
                ));

            if output != expected {
                panic!(
                    "output != expected\noutput = {:?},\nexpected = {:?}",
                    output.to_token_stream().to_string(),
                    expected.to_token_stream().to_string(),
                )
            }
        }
        )*
    }
}

test_all! {
    simple_input: {
        "struct Foo {
            bar: Bar,
            baz: Baz,
        }",
        "impl ::syn::parse::Parse for Foo {
            fn parse(__parse_input: ::syn::parse::ParseStream) -> ::syn::Result<Self> {
                let bar: Bar = __parse_input.parse()?;
                let baz: Baz = __parse_input.parse()?;

                Ok(Foo {
                    bar,
                    baz,
                })
            }
        }",
    },
    generic_struct: {
        "struct Foo<B, Q: Quack>
        where <B as Bar>::Qux: Quack,
        {
            bar: B,
            baz: Baz,
            quacker: Q,
        }",
        "impl<B: ::syn::parse::Parse, Q: Quack + ::syn::parse::Parse> ::syn::parse::Parse for Foo<B, Q>
        where <B as Bar>::Qux: Quack,
        {
            fn parse(__parse_input: ::syn::parse::ParseStream) -> ::syn::Result<Self> {
                let bar: B = __parse_input.parse()?;
                let baz: Baz = __parse_input.parse()?;
                let quacker: Q = __parse_input.parse()?;

                Ok(Foo {
                    bar,
                    baz,
                    quacker,
                })
            }
        }",
    },
    simple_attrs: {
        "struct Foo {
            bar: Bar,
            #[paren]
            paren: syn::token::Paren,
            #[inside(paren)]
            baz: Baz,
        }",
        "impl ::syn::parse::Parse for Foo {
            fn parse(__parse_input: ::syn::parse::ParseStream) -> ::syn::Result<Self> {
                let bar: Bar = __parse_input.parse()?;

                let __paren_backing_token_stream;
                let paren: syn::token::Paren =
                    ::syn::parenthesized!(__paren_backing_token_stream in __parse_input);
                let baz: Baz =
                    __paren_backing_token_stream.parse()?;

                Ok(Foo {
                    bar,
                    paren,
                    baz,
                })
            }
        }",
    },
    nested_attrs: {
        "struct Foo {
            bar: Bar,
            #[bracket]
            fst: syn::token::Bracket,
            #[inside(fst)]
            #[brace]
            snd: syn::token::Brace,
            #[inside(snd)]
            baz: Baz,
        }",
        "impl ::syn::parse::Parse for Foo {
            fn parse(__parse_input: ::syn::parse::ParseStream) -> ::syn::Result<Self> {
                let bar: Bar = __parse_input.parse()?;

                let __fst_backing_token_stream;
                let fst: syn::token::Bracket =
                    ::syn::bracketed!(__fst_backing_token_stream in __parse_input);

                let __snd_backing_token_stream;
                let snd: syn::token::Brace =
                    ::syn::braced!(__snd_backing_token_stream in __fst_backing_token_stream);

                let baz: Baz = __snd_backing_token_stream.parse()?;

                Ok(Foo {
                    bar,
                    fst,
                    snd,
                    baz,
                })
            }
        }",
    },
    struct_peek: {
        "struct Foo {
            bar: Bar,
            #[peek_with(|p| !p.is_empty())]
            baz: Baz,
        }",
        "impl ::syn::parse::Parse for Foo {
            fn parse(__parse_input: ::syn::parse::ParseStream) -> ::syn::Result<Self> {
                let bar: Bar = __parse_input.parse()?;
                
                let baz: Baz = match (|p| !p.is_empty())(__parse_input) {
                    true => Some(__parse_input.parse()?),
                    false => None,
                };

                Ok(Foo {
                    bar,
                    baz,
                })
            }
        }"
    },
    parse_if_peek: {
        "struct Foo {
            at_symbol: Option<Token![@]>,
            #[parse_if(at_symbol.is_some())]
            name: Ident,
        }",
        "impl ::syn::parse::Parse for Foo {
            fn parse(__parse_input: ::syn::parse::ParseStream) -> ::syn::Result<Self> {
                let at_symbol: Option<Token![@]> = __parse_input.parse()?;

                let name: Ident = match at_symbol.is_some() {
                    true => Some(__parse_input.parse()?),
                    false => None,
                };
                
                Ok(Foo {
                    at_symbol,
                    name,
                })
            }
        }"
    },
}
