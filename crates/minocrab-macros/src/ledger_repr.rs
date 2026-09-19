//! `#[derive(LedgerRepr)]`: a struct of ledger-storable fields becomes a
//! ledger-storable value — a `Map` value, a `Cell` type — with its atoms and
//! limbs in DECLARATION ORDER.
//!
//! For
//!
//! ```ignore
//! #[derive(LedgerRepr)]
//! struct DepositEnv {
//!     depositor: UserCommitment<Public>,
//!     amount: Uint<64, Public>,
//! }
//! ```
//!
//! the expansion is
//!
//! ```ignore
//! impl LedgerRepr for DepositEnv {
//!     fn atoms() -> Vec<AlignmentAtom> {
//!         let mut a = Vec::new();
//!         a.extend(<UserCommitment<Public>>::atoms());
//!         a.extend(<Uint<64, Public>>::atoms());
//!         a
//!     }
//!     fn push_limbs(&self, c, limbs) {
//!         self.depositor.push_limbs(c, limbs);
//!         self.amount.push_limbs(c, limbs);
//!     }
//!     fn from_limbs(limbs) -> Self {
//!         let mut limbs = limbs.into_iter();
//!         Self {
//!             depositor: <UserCommitment<Public>>::from_limbs(take(&mut limbs, repr_limbs::<UserCommitment<Public>>())),
//!             amount:    <Uint<64, Public>>::from_limbs(take(&mut limbs, repr_limbs::<Uint<64, Public>>())),
//!         }
//!     }
//! }
//! ```
//!
//! EVERY FIELD IS PUBLIC BY CONSTRUCTION: `LedgerRepr` is implemented for
//! the `Public` leaves only (a stored value is on-chain state), so a field
//! written `B32<Private>` has no impl and the derive fails to type-check —
//! which is the whole reason `signet_flow::Pending`'s environment is
//! declared through this derive: nothing private can be captured across a
//! request/settle suspension by accident.
//!
//! THINNESS RULE: the expansion calls no `Circuit3` method; `c` is threaded
//! to the fields' own impls.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput, Fields};

pub fn expand(input: DeriveInput) -> syn::Result<TokenStream> {
    let name = &input.ident;

    if !input.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &input.generics,
            "#[derive(LedgerRepr)] takes no generic parameters: a stored value \
             is public state, so write its fields at `Public`",
        ));
    }

    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(named) => &named.named,
            _ => {
                return Err(syn::Error::new_spanned(
                    &data.fields,
                    "#[derive(LedgerRepr)] needs named fields",
                ))
            }
        },
        Data::Enum(e) => {
            return Err(syn::Error::new_spanned(
                e.enum_token,
                "#[derive(LedgerRepr)] is for a struct: a stored value has one \
                 fixed shape",
            ))
        }
        Data::Union(u) => {
            return Err(syn::Error::new_spanned(
                u.union_token,
                "#[derive(LedgerRepr)] is for a struct",
            ))
        }
    };

    let root = quote!(::minocrab_std::v3::__derive);
    let idents: Vec<_> = fields.iter().map(|f| &f.ident).collect();
    let types: Vec<_> = fields.iter().map(|f| &f.ty).collect();

    Ok(quote! {
        impl #root::ProofWires for #name {
            fn push_wires(&self, out: &mut ::std::vec::Vec<#root::Val>) {
                #( #root::ProofWires::push_wires(&self.#idents, out); )*
            }
        }

        impl #root::LedgerRepr for #name {
            fn atoms() -> ::std::vec::Vec<#root::AlignmentAtom> {
                let mut atoms = ::std::vec::Vec::new();
                #( atoms.extend(<#types as #root::LedgerRepr>::atoms()); )*
                atoms
            }

            fn push_limbs(
                &self,
                c: &mut #root::Circuit3,
                limbs: &mut ::std::vec::Vec<#root::Wire3<#root::FieldT, #root::Public>>,
            ) {
                #( #root::LedgerRepr::push_limbs(&self.#idents, c, limbs); )*
            }

            fn from_limbs(
                limbs: ::std::vec::Vec<#root::Wire3<#root::FieldT, #root::Public>>,
            ) -> Self {
                let mut limbs = limbs.into_iter();
                let value = Self {
                    #( #idents: <#types as #root::LedgerRepr>::from_limbs(
                        limbs.by_ref().take(#root::repr_limbs::<#types>()).collect()
                    ), )*
                };
                ::core::assert!(
                    limbs.next().is_none(),
                    "{}::from_limbs was handed more limbs than its fields take",
                    ::core::stringify!(#name)
                );
                value
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_expansion_calls_no_circuit_method() {
        let expanded = expand(syn::parse_quote! {
            struct Env { a: B32<Public>, b: Uint<64, Public> }
        })
        .expect("expands")
        .to_string();
        assert!(!expanded.contains("c ."), "{expanded}");
        assert!(expanded.contains("repr_limbs :: < B32 < Public > >"), "{expanded}");
    }

    #[test]
    fn generics_are_rejected() {
        let error = expand(syn::parse_quote! {
            struct Env<V: Vis3> { a: B32<V> }
        })
        .expect_err("generics are rejected");
        assert!(error.to_string().contains("Public"), "{error}");
    }
}
