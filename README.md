![crates.io](https://img.shields.io/crates/v/derive-syn-parse.svg)
![docs.rs](https://docs.rs/derive-syn-parse/badge.svg)

# A derive macro for `syn`'s `Parse` trait

This is a relatively simple derive macro that produces an implementation `syn::parse::Parse` for the
type it's applied to.

A common pattern when writing custom `syn` parsers is repeating `<name>: input.parse()?` for
each field in the output. `#[derive(Parse)]` handles that for you, with some extra helpful
customization.

## Usage

Using this crate is as simple as adding it to your 'Cargo.toml' and importing the derive macro:

```toml
# Cargo.toml

[dependencies]
syn-derive-parse = "0.1"
```

```rust
// your_file.rs
use syn_derive_parse::Parse;

#[derive(Parse)]
struct CustomParseable {
    // ...
}
```

The derived implementation of `Parse` always parses in the order that the fields are given.

This crate is intended for users who are already making heavy use of `syn`.

## Motivation

When writing rust code that makes heavy use of `syn`'s parsing functionality, we often end up
writing things like:
```rust
use syn::parse::{Parse, ParseStream};
use syn::{Ident, Token, Type};

// A simplified struct field
//
//     x: i32
struct MyField {
    ident: Ident,
    colon_token: Token![:],
    ty: Type,
}

impl Parse for MyField {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(MyField {
            ident: input.parse()?,
            colon_token: input.parse()?,
            ty: input.parse()?,
        })
    }
}
```
This is really repetetive! Ideally, we'd like to just `#[derive(Parse)]` and have it work. And
so we can! (for the most part):
implementation:
```rust
use syn::{Ident, Token, Type};
use syn_derive_parse::Parse;

#[derive(Parse)]
struct MyField {
    ident: Ident,
    colon_token: Token![:],
    ty: Type,
}
```

Of course, there are more complicated cases. This is mainly covered immediately below in the
'Advanced usage' section.

## Advanced usage

There's a moderate collection of helper attributes that can be applied to fields and generic
parameters to customize the generated implementation of `Parse`. Each of these are demonstrated
with the implementation that they produce. Please note that the produced implementation is
typically *not* identical to what's shown here.

All of the examples are fairly contrived, I know. The reality of the matter is that - if you
would find this useful - it's probably true that your use-case is much more complicated than
would make sense for a short example. (If it isn't, let me know! It would be great to include
it here!)

### List of helper attributes
- [`#[paren]`](#paren--bracket--brace)
- [`#[bracket]`](#paren--braket--brace)
- [`#[brace]`](#paren--bracket--brace)
- [`#[inside]`](#inside)
- [`#[call]`](#call)
- [`#[parse_terminated]`](#parse_terminated)
- [`#[no_parse_bound]`](#no_parse_bound)

### `#[paren]` / `#[bracket]` / `#[brace]`

Because the derive macro has no fool-proof method for determining by itself whether a field type
is any of `syn::token::{Paren, Bracket, Brace}`, these three serve to provide that information
instead.

These are typically used in conjunction with [`#[inside]`](#inside).

```rust
// A single-argument function call
//
//     so_long(and_thanks + for_all * the_fish)
#[derive(Parse)]
struct SingleArgFn {
    ident: Ident,
    #[paren]
    paren_token: Paren,
    #[inside(paren_token)]
    arg: Expr,
}
```
produces
```rust
impl Parse for SingleArgFn {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let paren;
        Ok(SingleArgFn {
            ident: input.parse()?,
            paren_token: syn::parenthesized!(paren in input),
            arg: paren.parse()?,
        })
    }
}
```

### `#[inside(..)]`

This is a companion to `#[paren]`/`#[bracket]`/`#[brace]` - given a field name to use, this
attribute indicates that the field should be parsed using a previous field as the source.

```rust
use syn::token::Bracket;
use syn::{Type, Token, Expr};

// An array type required to have a length
//
//     [i32; 4]
#[derive(Parse)]
struct KnownLengthArrayType {
    #[bracket]
    bracket_token: Bracket,

    // Note that `#[inside(..)]` must be applied to all of the fields that
    // are in the brackets!
    #[inside(bracket_token)]
    ty: Type,
    #[inside(bracket_token)]
    semi_token: Token![;],
    #[inside(bracket_token)]
    expr: Expr,
}
```
produces
```rust
impl Parse for KnownLengthArrayType {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let bracket;
        Ok(KnownLengthArrayType {
            bracket_token: syn::braced!(bracket in input),
            ty: bracket.parse()?,
            semi_token: bracket.parse()?,
            expr: bracket.parse()?,
        })
    }
}
```

### `#[call(..)]`

Given a path to a function, this attribute specifies that the value of the field should be
instead calculated by a call to `input.parse(..)` with a given path. The best example is taken
straight from the `syn` documentation itself:
```rust
use syn::{Attribute, Ident, Token};

// Parses a unit struct with attributes.
//
//     #[path = "s.tmpl"]
//     struct S;
#[derive(Parse)]
struct UnitStruct {
    #[call(Attribute::parse_outer)]
    attrs: Vec<Attribute>,
    struct_token: Token![struct],
    name: Ident,
    semi_token: Token![;],
}
```
produces
```rust
impl Parse for UnitStruct {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(UnitStruct {
            attrs: input.call(Attribute::parse_outer)?,
            struct_token: input.parse()?,
            name: input.parse()?,
            semi_token: input.parse()?,
        })
    }
}
```


### `#[parse_terminated(..)]`

Just as we have [`#[call(..)]`](#call) for `ParseStream::call`, we have `#[parse_terminated]`
for `ParseStream::parse_terminated`. Here's the same example that the `ParseStream` method
uses:

```rust
// Parse a simplified tuple struct syntax like:
//
//     struct S(A, B);
struct TupleStruct {
    struct_token: Token![struct],
    ident: Ident,
    #[paren]
    paren_token: token::Paren,
    #[inside(paren_token)]
    #[parse_terminated(Type::parse)]
    fields: Punctuated<Type, Token![,]>,
    semi_token: Token![;],
}
```
produces
```rust
impl Parse for TupleStruct {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        Ok(TupleStruct {
            struct_token: input.parse()?,
            ident: input.parse()?,
            paren_token: parenthesized!(content in input),
            fields: content.parse_terminated(Type::parse)?,
            semi_token: input.parse()?,
        })
    }
}

```

### `#[no_parse_bound]`

By default, all type parameters in the source struct are required to implement `Parse`. The
`#[no_parse_bound]` attribute can be applied to them to lift that restriction. This is perhaps
less applicable, but available for certain use-cases:

```rust
use std::marker::PhantomData;

// [pretend this has an implementation of `Parse` that does nothing]
struct ParseablePhantomData<T>(PhantomData<T>);

#[derive(Parse)]
struct Foo<#[no_parse_bound] T, S> {
    bar: S,
    _marker: ParseablePhantomData<T>,
}
```
produces
```rust
impl<T, S: Parse> Parse for Foo<T, S> {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Foo {
            bar: input.parse()?,
            _marker: input.parse()?,
        })
    }
}
```

## Known limitations

The derive macro is only available for structs. While actually possible, it's currently
considered outside of the scope of this crate to generate implementations of `Parse` for enums.
This is because they will always require some kind of lookahead (either via
`ParseStream::peek` or `ParseStream::fork`).
