//! `#[derive(Ledger)]`: a struct mirroring the Compact `export ledger` block
//! becomes the contract's ledger handle, with each field's PATH computed from
//! its DECLARATION ORDER the way compactc computes it.
//!
//! For
//!
//! ```ignore
//! #[derive(Ledger)]
//! struct Vault {
//!     sign_bidirectional_event_map: LedgerMap<B32<Public>, VaultRecord>,  // 0
//!     signet_signer: LedgerField,                                        // 1
//!     signet_request_nonce: LedgerCounter,                               // 2
//! }
//! ```
//!
//! the expansion is
//!
//! ```ignore
//! impl Vault {
//!     pub const fn new() -> Self {
//!         Vault {
//!             sign_bidirectional_event_map:
//!                 <LedgerMap<B32<Public>, VaultRecord>>::at_path(&[0u8]),
//!             signet_signer: <LedgerField>::at_path(&[1u8]),
//!             signet_request_nonce: <LedgerCounter>::at_path(&[2u8]),
//!         }
//!     }
//! }
//! impl Default for Vault { fn default() -> Self { Self::new() } }
//! ```
//!
//! — nothing but the paths, which is the whole point: the one place a ledger
//! field's number is written down is the order it is declared in. By the
//! THINNESS RULE the expansion contains no `Circuit3` call; every operation
//! is a method on the slot types, in minocrab-std.
//!
//! A PATH AND NOT AN INDEX, because a ledger block is SEGMENTED at fifteen
//! fields (`maximum-ledger-segment-length`, langs.ss:851): a sixteen-field
//! block gives every field a two-element path and every `Cell` write in it is
//! a nested write. See [`field_paths`], which is that pass transcribed.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput, Fields};

pub fn expand(input: DeriveInput) -> syn::Result<TokenStream> {
    let name = &input.ident;

    if !input.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &input.generics,
            "#[derive(Ledger)] takes no generic parameters: a ledger block is \
             one contract's state, not a family of them",
        ));
    }

    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(named) => &named.named,
            _ => {
                return Err(syn::Error::new_spanned(
                    &data.fields,
                    "#[derive(Ledger)] needs named fields: the field names are \
                     the ledger field names",
                ))
            }
        },
        Data::Enum(e) => {
            return Err(syn::Error::new_spanned(
                e.enum_token,
                "#[derive(Ledger)] is for a struct mirroring the `export ledger` block",
            ))
        }
        Data::Union(u) => {
            return Err(syn::Error::new_spanned(
                u.union_token,
                "#[derive(Ledger)] is for a struct mirroring the `export ledger` block",
            ))
        }
    };

    if fields.len() > usize::from(u8::MAX) + 1 {
        return Err(syn::Error::new_spanned(
            name,
            "a ledger block has at most 256 fields (the index is a byte)",
        ));
    }

    let width = quote!(::minocrab_std::v3::LedgerWidth);
    let types: Vec<&syn::Type> = fields.iter().map(|f| &f.ty).collect();
    // The block's field count and each slot's first flat index are SUMS OF
    // WIDTHS, evaluated at compile time: a slot that is a group of fields
    // (`LedgerWidth::WIDTH > 1`) shifts everything after it, and the type
    // says by how much — nothing is counted by hand.
    let total = quote!(0usize #( + <#types as #width>::WIDTH )*);

    // THE SIGNET BLOCK, THREADED (M37 rung B, notes/evm-calls.org §3). An
    // `evm_flow::Pending` slot reads the contract's Signet configuration —
    // the MPC key, the nonce, the two chain ids — so it needs that block's
    // own start offset, and the ONE place that knows it is here: a block
    // has exactly one `Signet` field, and its offset is the same width sum
    // every other field's is. Threading it is what lets `request` /
    // `complete` / `refund` take no `&SELF.signet` argument.
    let signets: Vec<usize> = (0..fields.len()).filter(|i| named_as(types[*i], "Signet")).collect();
    // `Pending`, `Fired` and `Outbox` alike: all three are `evm_flow` slots
    // that read the block's Signet configuration, and none takes a
    // `&SELF.signet`.
    let pendings: Vec<usize> = (0..fields.len())
        .filter(|i| is_signet_slot(types[*i]))
        .collect();
    if signets.len() > 1 {
        let second = fields.iter().nth(signets[1]).expect("index from this list");
        return Err(syn::Error::new_spanned(
            second,
            "#[derive(Ledger)] wants EXACTLY ONE `Signet` field per block: it \
             is the contract's one Sig Network configuration (signer, MPC key, \
             request nonce, caip2 id, chain id), and every `Pending` and \
             `Fired` slot is built against its offset. Two of them would give \
             one contract two \
             MPC keys and two nonce sequences; delete this one.",
        ));
    }
    if signets.is_empty() && !pendings.is_empty() {
        let first = fields.iter().nth(pendings[0]).expect("index from this list");
        return Err(syn::Error::new_spanned(
            first,
            "a `Pending` or `Fired` slot needs the block's `Signet` field, and \
             this block has none. Add `pub signet: Signet,` to the ledger \
             block — it is \
             the signer address, the MPC response key, the request nonce and \
             the two chain identifiers a request reads from context.",
        ));
    }
    let signet_start = signets.first().map(|i| {
        let before = &types[..*i];
        quote!(0usize #( + <#before as #width>::WIDTH )*)
    });

    let inits = fields.iter().enumerate().map(|(i, field)| {
        let ident = &field.ident;
        let ty = &field.ty;
        let before = &types[..i];
        let start = quote!(0usize #( + <#before as #width>::WIDTH )*);
        match (&signet_start, is_signet_slot(ty)) {
            (Some(signet_start), true) => {
                quote!(#ident: <#ty>::at_block_with_signet(__TOTAL, #start, #signet_start))
            }
            _ => quote!(#ident: <#ty>::at_block(__TOTAL, #start)),
        }
    });

    Ok(quote! {
        impl #name {
            /// The ledger block: every field at its DECLARATION-ORDER index.
            ///
            /// `const`, so a contract's ledger handle is a `const` item and
            /// costs nothing at run time.
            pub const fn new() -> Self {
                const __TOTAL: usize = #total;
                #name { #(#inits),* }
            }
        }

        impl ::core::default::Default for #name {
            fn default() -> Self {
                Self::new()
            }
        }

        // No two slots of one block settle under the same Signet response
        // kind (E0080 if they do). A Signet slot's `KINDS` is a one-element
        // list holding its `evm::Filing::KIND` — the DEPLOYMENT's protocol
        // byte, which since M38 rung A is named by the slot's filing rather
        // than by the library call it files.
        const _: () = ::minocrab_std::v3::assert_distinct_kinds(&[
            #( <#types as #width>::KINDS ),*
        ]);
    })
}

/// Is this field one of the `evm_flow` slots built against the block's
/// `Signet` — `Pending`, `Fired` or `Outbox`?
///
/// Spelling, like [`named_as`]: the derive sees tokens, not resolutions.
fn is_signet_slot(ty: &syn::Type) -> bool {
    named_as(ty, "Pending") || named_as(ty, "Fired") || named_as(ty, "Outbox")
}

/// Is this type SPELLED `name` — is the last segment of its path that
/// identifier? Spelling, not resolution: a proc macro sees tokens, and a
/// `use` alias or a fully-qualified `signet_flow::Pending` both read as
/// `Pending` here, which is the intended latitude.
fn named_as(ty: &syn::Type, name: &str) -> bool {
    let syn::Type::Path(path) = ty else {
        return false;
    };
    path.path
        .segments
        .last()
        .is_some_and(|segment| segment.ident == name)
}

/// compactc's `maximum-ledger-segment-length` (langs.ss:851).
#[cfg(test)]
const SEGMENT: usize = 15;

/// EVERY FIELD'S PATH, as `determine-ledger-paths.ss` computes it — the
/// reference the expansion's `const` twin (`FieldPath::in_block`, in
/// minocrab-std) is pinned against by the derive tests below.
///
/// A ledger block is not a flat list of fields: `batch` (that pass's own
/// helper, verbatim below) folds the fields into a TREE of segments no wider
/// than fifteen, and the pass then walks the tree handing each leaf the list
/// of indices from the root down. For fifteen fields or fewer the tree is one
/// level and every path is `[i]` — the bare index this derive used to emit.
/// At SIXTEEN it is two levels, and every field's path becomes two elements:
/// `[0, 0]` for the first, `[1, j]` for the rest. A `Cell` write in such a
/// block is a NESTED write, with the `idxp`/`insc` pair compactc suppresses
/// at depth 1 come back to life.
///
/// So the derive has to know the segmentation or a sixteen-field contract
/// silently diverges from compactc — which is exactly what happened before
/// M22 stage B2 (notes/coin-arms-nested-adts.org, stage B1 correction (ii);
/// pinned on the emission side by
/// `a_sixteen_field_contract_makes_every_cell_write_nested`).
///
/// `batch`, transcribed:
///
/// ```text
/// (define (batch k x*)
///   (let f ([x* x*] [n (length x*)])
///     (if (fx<= n k)
///       x*
///       (let-values ([(q r) (div-and-mod n k)])
///         (let ([x** ...chunks of k over (list-tail x* r)...])
///           (if (fx= r 0)
///               (f x** q)
///               (f (cons (list-head x* r) x**) (fx+ q 1))))))))
/// ```
///
/// — the REMAINDER leads, as its own short segment, and the full segments
/// follow; then the list of segments is batched again until it fits.
#[cfg(test)]
fn field_paths(fields: usize) -> Vec<Vec<u8>> {
    /// A segment tree over the field indices: `batch` applied until the top
    /// level fits in one segment.
    enum Tree {
        Leaf(usize),
        Node(Vec<Tree>),
    }

    fn batch(mut level: Vec<Tree>) -> Vec<Tree> {
        let n = level.len();
        if n <= SEGMENT {
            return level;
        }
        let r = n % SEGMENT;
        let rest: Vec<Tree> = level.split_off(r);
        let mut grouped: Vec<Tree> = Vec::new();
        if r != 0 {
            grouped.push(Tree::Node(level));
        }
        let mut rest = rest.into_iter();
        loop {
            let chunk: Vec<Tree> = rest.by_ref().take(SEGMENT).collect();
            if chunk.is_empty() {
                break;
            }
            grouped.push(Tree::Node(chunk));
        }
        batch(grouped)
    }

    fn walk(tree: &Tree, prefix: &mut Vec<u8>, out: &mut Vec<(usize, Vec<u8>)>) {
        match tree {
            Tree::Leaf(field) => out.push((*field, prefix.clone())),
            Tree::Node(children) => {
                for (i, child) in children.iter().enumerate() {
                    prefix.push(i as u8);
                    walk(child, prefix, out);
                    prefix.pop();
                }
            }
        }
    }

    let top = batch((0..fields).map(Tree::Leaf).collect());
    let mut out = Vec::new();
    // The top level is itself the outermost `public-ledger-array`, so its
    // own position is the first path element.
    walk(&Tree::Node(top), &mut Vec::new(), &mut out);
    out.sort_by_key(|(field, _)| *field);
    out.into_iter().map(|(_, path)| path).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expansion(input: DeriveInput) -> String {
        expand(input).expect("expands").to_string()
    }

    /// FIFTEEN OR FEWER: one segment, and every path is the bare declaration
    /// index — the shape every contract in the workspace has.
    #[test]
    fn a_narrow_block_is_one_element_paths() {
        for n in 1..=SEGMENT {
            let paths = field_paths(n);
            assert_eq!(paths.len(), n);
            for (i, path) in paths.iter().enumerate() {
                assert_eq!(path, &vec![i as u8], "{n} fields, field {i}");
            }
        }
    }

    /// SIXTEEN: compactc segments the block, and every field — including the
    /// first — gets a two-element path. Pinned against the pinned compactc's
    /// own artifact for a sixteen-field probe, which compiles `f0 = v` to
    /// `idxp [1,1,0]; push [1,1,1,0]; …` — path `[0, 0]` — and `f15 = v` to
    /// `idxp [1,1,1]; push [1,1,1,14]` — path `[1, 14]`.
    #[test]
    fn sixteen_fields_are_a_remainder_segment_and_a_full_one() {
        let paths = field_paths(16);
        assert_eq!(paths[0], vec![0, 0], "the remainder segment leads");
        for (i, path) in paths.iter().enumerate().skip(1) {
            assert_eq!(path, &vec![1, (i - 1) as u8], "field {i}");
        }
    }

    /// The tree deepens exactly where `batch` says: two levels to 225
    /// (15 × 15), three past it.
    #[test]
    fn the_tree_deepens_at_the_segment_squared() {
        assert!(field_paths(225).iter().all(|p| p.len() == 2));
        assert!(field_paths(226).iter().any(|p| p.len() == 3));
        assert!(field_paths(256).iter().all(|p| p.len() <= 3));
        // Every path is unique — a segmentation that collided would alias
        // two fields onto one slot.
        let mut all = field_paths(256);
        all.sort();
        all.dedup();
        assert_eq!(all.len(), 256);
    }

    /// THINNESS RULE: the expansion builds no circuit — it is indices.
    #[test]
    fn the_expansion_calls_no_circuit_method() {
        let expanded = expansion(syn::parse_quote! {
            struct Vault {
                event_map: LedgerMap<B32<Public>, VaultRecord>,
                initialized: LedgerCounter,
            }
        });
        assert!(
            !expanded.contains("c ."),
            "expansion calls a method on the circuit:\n{expanded}"
        );
        assert!(
            !expanded.contains("Circuit3 ::"),
            "expansion calls a Circuit3 associated function:\n{expanded}"
        );
    }

    /// The index IS the declaration order, and nothing else is generated.
    #[test]
    fn each_field_gets_its_declaration_order_index() {
        let expanded = expansion(syn::parse_quote! {
            struct Vault {
                event_map: LedgerMap<B32<Public>, VaultRecord>,
                signer: LedgerField,
                initialized: LedgerCounter,
            }
        });
        assert!(expanded.contains("event_map : < LedgerMap < B32 < Public > , VaultRecord > > :: at_block (__TOTAL , 0usize)"), "{expanded}");
        assert!(expanded.contains("signer : < LedgerField > :: at_block (__TOTAL , 0usize + < LedgerMap < B32 < Public > , VaultRecord > as :: minocrab_std :: v3 :: LedgerWidth > :: WIDTH)"), "{expanded}");
        assert!(expanded.contains("initialized : < LedgerCounter > :: at_block (__TOTAL , 0usize + < LedgerMap < B32 < Public > , VaultRecord > as :: minocrab_std :: v3 :: LedgerWidth > :: WIDTH + < LedgerField as :: minocrab_std :: v3 :: LedgerWidth > :: WIDTH)"), "{expanded}");
        assert!(expanded.contains("assert_distinct_kinds"), "{expanded}");
        // …over EVERY field's `KINDS`, in declaration order: that is where
        // a `Pending`/`Fired` slot's `Filing::KIND` reaches the check.
        assert!(
            expanded.contains(
                "assert_distinct_kinds (& [< LedgerMap < B32 < Public > , VaultRecord > as \
                 :: minocrab_std :: v3 :: LedgerWidth > :: KINDS , < LedgerField as \
                 :: minocrab_std :: v3 :: LedgerWidth > :: KINDS , < LedgerCounter as \
                 :: minocrab_std :: v3 :: LedgerWidth > :: KINDS])"
            ),
            "{expanded}"
        );
    }

    /// …and a SIXTEEN-field block is laid out by `at_block` over the
    /// block's total, whose `const` segmentation (`FieldPath::in_block`)
    /// is pinned against [`field_paths`] in minocrab-std's tests — stage
    /// B1's correction (ii) on the derive side.
    #[test]
    fn a_sixteen_field_block_is_laid_out_over_its_total() {
        let fields = (0..16u8).map(|i| {
            let ident = quote::format_ident!("f{i}");
            quote!(#ident: LedgerCell<Uint<64, Public>>)
        });
        let expanded = expansion(syn::parse_quote! {
            struct Wide { #(#fields),* }
        });
        assert!(expanded.contains("f0 : < LedgerCell < Uint < 64 , Public > > > :: at_block (__TOTAL , 0usize)"), "{expanded}");
        assert!(expanded.contains("const __TOTAL : usize = 0usize + < LedgerCell < Uint < 64 , Public > > as :: minocrab_std :: v3 :: LedgerWidth > :: WIDTH"), "{expanded}");
    }

    /// A ledger block is one contract's state.
    #[test]
    fn generics_are_rejected() {
        let error = expand(syn::parse_quote! {
            struct Vault<T> {
                event_map: LedgerMap<B32<Public>, T>,
            }
        })
        .expect_err("generics are rejected");
        assert!(error.to_string().contains("no generic parameters"), "{error}");
    }

    /// A tuple struct has no field names, and the names are the ledger's.
    #[test]
    fn a_tuple_struct_is_rejected() {
        let error = expand(syn::parse_quote! {
            struct Vault(LedgerCounter);
        })
        .expect_err("a tuple struct is rejected");
        assert!(error.to_string().contains("named fields"), "{error}");
    }
}
