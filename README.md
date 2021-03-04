[![crates.io](https://img.shields.io/crates/v/derive-syn-parse.svg)](https://crates.io/crates/derive-syn-parse)
[![docs.rs](https://docs.rs/derive-syn-parse/badge.svg)](https://docs.rs/derive-syn-parse)

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
derive-syn-parse = "0.1"
```

```rust
// your_file.rs
use derive_syn_parse::Parse;

#[derive(Parse)]
struct CustomParsable {
    // ...
}
```

The derived implementation of `Parse` always parses in the order that the fields are given.
**Note that deriving `Parse` is also available on enums.** For more information, see the
[dedicated section](#enum-parsing).

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
This is really repetitive! Ideally, we'd like to just `#[derive(Parse)]` and have it work. And
so we can! (for the most part) Adding `#[derive(Parse)]` to the previous struct produces an
equivalent implementation of `Parse`:
```rust
use syn::{Ident, Token, Type};
use derive_syn_parse::Parse;

#[derive(Parse)]
struct MyField {
    ident: Ident,
    colon_token: Token![:],
    ty: Type,
}
```

Of course, there are more complicated cases. This is mainly covered below in the 'Advanced
usage' section.

## Enum parsing

Parsing `enum`s is a complex feature. When writing manual implementations of `Parse`, it
doesn't come up as often, but there are also typically *many* ways to do it: `syn` provides
both forking the `ParseBuffer` *and* peeking in order to handle this, with peeking to be
preferred if possible.

This library does not support forking; it tends to suffer from poor error messages and general
inefficiency. That being said, manual implementations of `Parse` can and should be written when
this library is insufficient.

We *do* support peeking - in two different ways. These are handled by the `#[peek]` and
`#[peek_with]` attributes, which are required on- and only available for `enum` variants. The
general syntax can be thought of as:

```
#[peek($TYPE, name = $NAME)]
```
and
```
#[peek_with($EXPR, name = $NAME)]
```
where `$TYPE`, `$EXPR`, and `$NAME` are meta-variables that correspond to the particular input
given to the attribute.

These can be thought of as translating literally to:
```rust
if input.peek($TYPE) {
    // parse variant
} else {
    // parse other variants
}
```
and
```rust
if ($EXPR)(input) {
    // parse variant
} else {
    // parse other variants
}
```
respectively. If no variant matches, we produce an error message, using the names that were
provided for each type.

## Advanced usage

There's a moderate collection of helper attributes that can be applied to fields to customize
the generated implementation of `Parse`. Each of these are demonstrated with the
implementation that they produce. Please note that the produced implementation is typically
*not* identical to what's shown here.

All of the examples are fairly contrived, I know. The reality of the matter is that - if you
would find this useful - it's probably true that your use-case is much more complicated than
would make sense for a short example. (If it isn't, let me know! It would be great to include
it here!)

### List of helper attributes
- [`#[paren]`](#paren--bracket--brace)
- [`#[bracket]`](#paren--braket--brace)
- [`#[brace]`](#paren--bracket--brace)
- [`#[inside]`](#inside)
- [`#[parse_if]`](#conditional-parsing)
- [`#[call]`](#call)
- [`#[parse_terminated]`](#parse_terminated)
- [`#[peek]`](#enum-parsing)
- [`#[peek_with]`](#enum-parsing)

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
use syn::{Type, Token, Expr};
use syn::token::Bracket;

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
            bracket_token: syn::bracketed!(bracket in input),
            ty: bracket.parse()?,
            semi_token: bracket.parse()?,
            expr: bracket.parse()?,
        })
    }
}
```

### Conditional parsing

When implementing `Parse` for structs, it is occasionally the case that certain fields are
optional - or should only be parsed under certain circumstances. There are attributes for that!

Say we want to represent `enum`s with the following, different syntax:
```rust
enum Foo {
    Bar: Baz,
    Qux,
}
```
where the equivalent Rust code would be:
```rust
enum Foo {
    Bar(Baz),
    Qux,
}
```

There's two ways we could parse the variants here -- either with a colon (and following type),
or without! To handle this, we can write:

```rust
#[derive(Parse)]
struct Variant {
    name: Ident,
    // `syn` already supports optional parsing of simple tokens
    colon: Option<Token![:]>,
    // We only want to parse the trailing type if there's a colon:
    #[parse_if(colon.is_some())]
    ty: Option<Type>,
}
```

Note that in this case, `ty` *must* be an `Option`. In addition to conditional parsing based on
the values of what's already been parsed, we can also peek - just as described above in the
section on [parsing enums](#enum-parsing). The only difference here is that we do not need to
provide a name for the optional field. We could have equally implemented the above as:

```rust
struct Variant {
    name: Ident,
    #[peek(Token![:], name = "`:` <type>")]
    ty: Option<VariantType>,
}

#[derive(Parse)]
struct VariantType {
    colon: Token![:],
    ty: Type,
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
#[derive(Parse)]
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
    fn parse(input: ParseStream) -> syn::Result<Self> {
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
