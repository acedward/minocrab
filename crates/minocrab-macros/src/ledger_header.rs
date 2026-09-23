//! `#[derive(LedgerHeader)]`: a unit struct, or a struct of single-field
//! ledger slots, becomes a STANDARD — a slot type that claims `root[0]` of
//! any `#[derive(Ledger)]` block it is declared in (notes/ledger-header.org).
//!
//! For
//!
//! ```ignore
//! #[derive(LedgerHeader)]
//! struct Versioned {
//!     version: LedgerCell<Uint<8, Public>>,
//!     admin: LedgerCell<B32<Public>>,
//! }
//! impl LedgerHeader for Versioned { const MAGIC: [u8; 32] = pad32(b"…"); }
//! ```
//!
//! the expansion is (`S` standing for `::minocrab_std::v3`)
//!
//! ```ignore
//! impl S::LedgerWidth for Versioned {
//!     const WIDTH: usize = 0;
//!     const PLACEMENT: S::Placement = S::Placement::RootHeader;
//! }
//! impl Versioned {
//!     pub const fn at_layout(layout: S::BlockLayout, _start: usize) -> Self {
//!         S::__derive::assert_headed(layout);
//!         Versioned {
//!             version: <LedgerCell<Uint<8, Public>>>::at_path(&[0u8, 1u8]),
//!             admin: <LedgerCell<B32<Public>>>::at_path(&[0u8, 2u8]),
//!         }
//!     }
//!     pub const fn magic(&self) -> S::Magic { S::Magic::at_path(&[0u8, 0u8]) }
//! }
//! const _: () = S::__derive::assert_magic(&<Versioned as S::LedgerHeader>::MAGIC);
//! const _: () = S::__derive::assert_header_fields(&[<… as W>::WIDTH, …], &[… KINDS …], &[… PLACEMENT …]);
//! const _: () = { S::__derive::header_field::<LedgerCell<Uint<8, Public>>>(); … };
//! ```
//!
//! and for a unit struct `struct Mip0099;` the magic is a Cell at `[0]`,
//! `at_layout` returns the unit value and there are no fields to check.
//!
//! WIDTH ZERO is the whole layout story: `#[derive(Ledger)]`'s width sums
//! leave the standard out, so its body is laid out as if it were absent,
//! and `PLACEMENT = RootHeader` is what makes that block's layout headed.
//! The header's own paths do not depend on the block at all — a standard
//! is at `root[0]` in every contract — so `at_layout` ignores `start`.
//!
//! The magic is NOT a field: it is `LedgerHeader::MAGIC`, written by the
//! standard's author in a hand-written impl, and `magic()` hands out a
//! `minocrab_std::v3::Magic`, which has a path and no write. The impl
//! being missing is E0277 at the `assert_magic` item, with
//! `LedgerHeader`'s own message.
//!
//! THINNESS RULE: paths and `const` checks only; no `Circuit3` call.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput, Fields};

/// The most named fields a standard may have: the header is one Array at
/// `root[0]`, the magic takes entry 0, and the ledger's Array bound is
/// sixteen (onchain-state `state.rs`).
const MAX_HEADER_FIELDS: usize = 15;

pub fn expand(input: DeriveInput) -> syn::Result<TokenStream> {
    let name = &input.ident;

    if !input.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &input.generics,
            "#[derive(LedgerHeader)] takes no generic parameters: a standard is one \
             fixed header at root[0], with one magic",
        ));
    }

    let data = match &input.data {
        Data::Struct(data) => data,
        Data::Enum(e) => {
            return Err(syn::Error::new_spanned(
                e.enum_token,
                "#[derive(LedgerHeader)] is for a struct: a unit struct (magic only) or \
                 a struct of single-field ledger slots",
            ))
        }
        Data::Union(u) => {
            return Err(syn::Error::new_spanned(
                u.union_token,
                "#[derive(LedgerHeader)] is for a struct: a unit struct (magic only) or \
                 a struct of single-field ledger slots",
            ))
        }
    };

    let s = quote!(::minocrab_std::v3);
    let width = quote!(#s::LedgerWidth);

    // The magic's path, and the fields after it.
    let (magic_path, construct, field_types): (TokenStream, TokenStream, Vec<&syn::Type>) =
        match &data.fields {
            Fields::Unit => (quote!(&[0u8]), quote!(#name), Vec::new()),
            Fields::Named(named) if named.named.is_empty() => {
                return Err(syn::Error::new_spanned(
                    &data.fields,
                    "a magic-only standard is a unit struct: write `struct Name;` — a \
                     standard with fields is an Array at root[0], and one with none \
                     is a Cell",
                ))
            }
            Fields::Named(named) => {
                if named.named.len() > MAX_HEADER_FIELDS {
                    let extra = named
                        .named
                        .iter()
                        .nth(MAX_HEADER_FIELDS)
                        .expect("more than MAX_HEADER_FIELDS fields");
                    return Err(syn::Error::new_spanned(
                        extra,
                        "a standard has at most 15 named fields: its header is one Array \
                         at root[0] holding the magic and one entry per field, and the \
                         ledger's Array bound is sixteen",
                    ));
                }
                if let Some(magic) = named
                    .named
                    .iter()
                    .find(|f| f.ident.as_ref().is_some_and(|i| i == "magic"))
                {
                    return Err(syn::Error::new_spanned(
                        magic,
                        "the magic is not a field: it is `LedgerHeader::MAGIC`, written \
                         at deploy and read-only at `magic()`. A field named `magic` \
                         would be an ordinary, writable slot at [0, i]; rename it",
                    ));
                }
                let inits = named.named.iter().enumerate().map(|(i, field)| {
                    let ident = &field.ident;
                    let ty = &field.ty;
                    let entry = (i + 1) as u8;
                    quote!(#ident: <#ty>::at_path(&[0u8, #entry]))
                });
                let construct = quote!(#name { #(#inits),* });
                let types = named.named.iter().map(|f| &f.ty).collect();
                (quote!(&[0u8, 0u8]), construct, types)
            }
            Fields::Unnamed(_) => {
                return Err(syn::Error::new_spanned(
                    &data.fields,
                    "#[derive(LedgerHeader)] needs named fields (or none, for a magic-only \
                     unit struct): the field names are the standard's",
                ))
            }
        };

    let field_checks = if field_types.is_empty() {
        quote!()
    } else {
        let types = &field_types;
        quote! {
            // Each field is ONE ledger field, settles no Signet kind and is
            // not itself a standard — as a missing impl (E0277, the
            // `HeaderField` message) and, in the layout's own terms, as
            // E0080.
            const _: () = {
                #( #s::__derive::header_field::<#types>(); )*
            };
            const _: () = #s::__derive::assert_header_fields(
                &[ #( <#types as #width>::WIDTH ),* ],
                &[ #( <#types as #width>::KINDS ),* ],
                &[ #( <#types as #width>::PLACEMENT ),* ],
            );
        }
    };

    Ok(quote! {
        // WIDTH 0: the block's body sums leave the standard out.
        // RootHeader: the block's layout is headed, root[0] is this.
        impl #width for #name {
            const WIDTH: usize = 0;
            const PLACEMENT: #s::Placement = #s::Placement::RootHeader;
        }

        impl #name {
            /// The standard at `root[0]` — what `#[derive(Ledger)]` emits.
            /// Its paths are the same in every block, so `_start` (the
            /// body index the derive threads to every slot) is unused.
            pub const fn at_layout(layout: #s::BlockLayout, _start: usize) -> Self {
                #s::__derive::assert_headed(layout);
                #construct
            }

            /// The standard's magic: its path, and no write.
            pub const fn magic(&self) -> #s::Magic {
                #s::Magic::at_path(#magic_path)
            }
        }

        // The magic is not all zero (E0080), and the standard names one
        // (E0277 with `LedgerHeader`'s message if the impl is missing).
        const _: () = #s::__derive::assert_magic(&<#name as #s::LedgerHeader>::MAGIC);

        #field_checks
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expansion(input: DeriveInput) -> String {
        expand(input).expect("expands").to_string()
    }

    /// THINNESS RULE: paths and const checks, no circuit.
    #[test]
    fn the_expansion_calls_no_circuit_method() {
        let expanded = expansion(syn::parse_quote! {
            struct Versioned {
                version: LedgerCell<Uint<8, Public>>,
                admin: LedgerCell<B32<Public>>,
            }
        });
        assert!(!expanded.contains("c ."), "{expanded}");
        assert!(!expanded.contains("Circuit3"), "{expanded}");
    }

    /// A unit struct is magic-only: `[0]`, width 0, root header.
    #[test]
    fn a_unit_struct_is_a_magic_cell_at_the_root() {
        let expanded = expansion(syn::parse_quote! { struct Mip0099; });
        assert!(expanded.contains("const WIDTH : usize = 0"), "{expanded}");
        assert!(
            expanded.contains(
                "const PLACEMENT : :: minocrab_std :: v3 :: Placement = :: minocrab_std :: v3 :: Placement :: RootHeader"
            ),
            "{expanded}"
        );
        assert!(
            expanded.contains("Magic :: at_path (& [0u8])"),
            "{expanded}"
        );
        assert!(
            expanded.contains(
                "assert_magic (& < Mip0099 as :: minocrab_std :: v3 :: LedgerHeader > :: MAGIC)"
            ),
            "{expanded}"
        );
        assert!(!expanded.contains("assert_header_fields"), "{expanded}");
    }

    /// Named fields: the magic at `[0, 0]`, field `i` at `[0, i + 1]`, and
    /// every field checked.
    #[test]
    fn named_fields_follow_the_magic_in_the_header_array() {
        let expanded = expansion(syn::parse_quote! {
            struct Versioned {
                version: LedgerCell<Uint<8, Public>>,
                admin: LedgerCell<B32<Public>>,
            }
        });
        assert!(
            expanded.contains("Magic :: at_path (& [0u8 , 0u8])"),
            "{expanded}"
        );
        assert!(
            expanded.contains(
                "version : < LedgerCell < Uint < 8 , Public > > > :: at_path (& [0u8 , 1u8])"
            ),
            "{expanded}"
        );
        assert!(
            expanded
                .contains("admin : < LedgerCell < B32 < Public > > > :: at_path (& [0u8 , 2u8])"),
            "{expanded}"
        );
        assert!(
            expanded.contains("header_field :: < LedgerCell < Uint < 8 , Public > > > ()"),
            "{expanded}"
        );
        assert!(expanded.contains("assert_header_fields"), "{expanded}");
        assert!(expanded.contains("assert_headed (layout)"), "{expanded}");
    }

    fn named(n: usize) -> DeriveInput {
        let fields = (0..n).map(|i| {
            let ident = quote::format_ident!("f{i}");
            quote!(#ident: LedgerField)
        });
        syn::parse_quote! { struct Wide { #(#fields),* } }
    }

    /// Fifteen fields fit (the last at `[0, 15]`); sixteen do not, and the
    /// error names the rule.
    #[test]
    fn sixteen_named_fields_are_rejected_with_the_rule() {
        let expanded = expansion(named(15));
        assert!(
            expanded.contains("f14 : < LedgerField > :: at_path (& [0u8 , 15u8])"),
            "{expanded}"
        );
        let error = expand(named(16)).expect_err("sixteen fields are rejected");
        assert!(
            error.to_string().contains("at most 15 named fields"),
            "{error}"
        );
    }

    /// `magic` is not a field name a standard may use.
    #[test]
    fn a_field_named_magic_is_rejected() {
        let error = expand(syn::parse_quote! {
            struct S { magic: LedgerCell<B32<Public>> }
        })
        .expect_err("a `magic` field is rejected");
        assert!(
            error.to_string().contains("the magic is not a field"),
            "{error}"
        );
    }

    /// The shapes that are not a standard.
    #[test]
    fn other_shapes_are_rejected() {
        let generic =
            expand(syn::parse_quote! { struct S<T> { t: LedgerCell<T> } }).expect_err("generic");
        assert!(
            generic.to_string().contains("no generic parameters"),
            "{generic}"
        );
        let tuple = expand(syn::parse_quote! { struct S(LedgerField); }).expect_err("tuple");
        assert!(tuple.to_string().contains("named fields"), "{tuple}");
        let empty = expand(syn::parse_quote! { struct S {} }).expect_err("empty braces");
        assert!(empty.to_string().contains("unit struct"), "{empty}");
        let an_enum = expand(syn::parse_quote! { enum S { A } }).expect_err("enum");
        assert!(an_enum.to_string().contains("is for a struct"), "{an_enum}");
    }
}
