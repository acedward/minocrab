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
//! the expansion is (`W` standing for `::minocrab_std::v3::LedgerWidth`)
//!
//! ```ignore
//! impl Vault {
//!     pub const fn new() -> Self {
//!         const __TOTAL: usize = 0usize + <LedgerMap<B32<Public>, VaultRecord> as W>::WIDTH
//!             + <LedgerField as W>::WIDTH + <LedgerCounter as W>::WIDTH;
//!         const __HEADERS: usize = ::minocrab_std::v3::standards(&[
//!             <LedgerMap<B32<Public>, VaultRecord> as W>::PLACEMENT,
//!             <LedgerField as W>::PLACEMENT, <LedgerCounter as W>::PLACEMENT,
//!         ]);
//!         const __LAYOUT: ::minocrab_std::v3::BlockLayout =
//!             ::minocrab_std::v3::BlockLayout::of_block(__TOTAL, __HEADERS);
//!         Vault {
//!             sign_bidirectional_event_map:
//!                 <LedgerMap<B32<Public>, VaultRecord>>::at_layout(__LAYOUT, 0usize),
//!             signet_signer: <LedgerField>::at_layout(__LAYOUT, 0usize + <LedgerMap<…> as W>::WIDTH),
//!             signet_request_nonce: <LedgerCounter>::at_layout(__LAYOUT, 0usize + … + <LedgerField as W>::WIDTH),
//!         }
//!     }
//! }
//! impl Vault {
//!     pub fn initial_state() -> ::minocrab_std::v3::StateBuilder {
//!         const __BLOCK: Vault = Vault::new();
//!         let mut __state = ::minocrab_std::v3::StateBuilder::new();
//!         ::minocrab_std::v3::InitialState::contribute(&__BLOCK.sign_bidirectional_event_map, &mut __state);
//!         ::minocrab_std::v3::InitialState::contribute(&__BLOCK.signet_signer, &mut __state);
//!         ::minocrab_std::v3::InitialState::contribute(&__BLOCK.signet_request_nonce, &mut __state);
//!         __state
//!     }
//! }
//! impl Default for Vault { fn default() -> Self { Self::new() } }
//! const _: () = ::minocrab_std::v3::assert_distinct_kinds(&[<… as W>::KINDS, …]);
//! const _: usize = ::minocrab_std::v3::standards(&[<… as W>::PLACEMENT, …]);
//! ```
//!
//! — nothing but width sums, placements and constructor calls, which is the
//! whole point: the one place a ledger field's number is written down is the
//! order it is declared in, and `__LAYOUT` is compactc's layout
//! (`BlockLayout::compactc(__TOTAL)`) for every block without a standard. By
//! the THINNESS RULE the expansion contains no `Circuit3` call; every
//! operation is a method on the slot types, in minocrab-std.
//!
//! A PATH AND NOT AN INDEX, because a ledger block is SEGMENTED at fifteen
//! fields (`maximum-ledger-segment-length`, langs.ss:851): a sixteen-field
//! block gives every field a two-element path and every `Cell` write in it is
//! a nested write. See [`field_paths`], which is that pass transcribed.
//!
//! A STANDARD (`#[derive(LedgerHeader)]`, notes/ledger-header.org) is a
//! field whose type says `PLACEMENT = RootHeader` and `WIDTH = 0`: the width
//! sums skip it, so the body is laid out as if it were absent, and
//! `__HEADERS = 1` makes `__LAYOUT` headed — the body moved one root slot
//! along, `root[0]` the standard's — wherever in the struct it is declared.
//! Two standards are E0080 (one standard per ledger block). Nothing here
//! looks for a standard by name: the type decides, as the owner of the
//! standard intends.
//!
//! THE DEPLOY STATE is the same walk once more: `initial_state()` hands every
//! field to its type's `InitialState::contribute`, which writes the slot's
//! initial value at the path `new()` gave it (minocrab-std `v3::state`). A
//! `StateBuilder` call per field, and nothing computed here.

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

    // 256 body fields and, at most, one standard beside them. The real
    // bound is on the WIDTH sum, and `FieldPath::in_block` asserts it
    // (E0080); this is the early, spanned rejection of a struct no width
    // sum could fit.
    if fields.len() > usize::from(u8::MAX) + 2 {
        return Err(syn::Error::new_spanned(
            name,
            "a ledger block has at most 256 fields (the index is a byte), \
             besides one standard",
        ));
    }

    let width = quote!(::minocrab_std::v3::LedgerWidth);
    let types: Vec<&syn::Type> = fields.iter().map(|f| &f.ty).collect();
    // The block's field count and each slot's first flat index are SUMS OF
    // WIDTHS, evaluated at compile time: a slot that is a group of fields
    // (`LedgerWidth::WIDTH > 1`) shifts everything after it, and the type
    // says by how much — nothing is counted by hand.
    let total = quote!(0usize #( + <#types as #width>::WIDTH )*);
    // …and whether the block carries a standard is a sum too: each slot
    // type says where it sits (`LedgerWidth::PLACEMENT`), and `standards`
    // counts the `RootHeader`s — E0080 above one.
    let placements = quote!(&[ #( <#types as #width>::PLACEMENT ),* ]);

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
                quote!(#ident: <#ty>::at_layout_with_signet(__LAYOUT, #start, #signet_start))
            }
            _ => quote!(#ident: <#ty>::at_layout(__LAYOUT, #start)),
        }
    });

    let idents: Vec<&Option<syn::Ident>> = fields.iter().map(|f| &f.ident).collect();

    Ok(quote! {
        impl #name {
            /// The ledger block: every field at its DECLARATION-ORDER index.
            ///
            /// `const`, so a contract's ledger handle is a `const` item and
            /// costs nothing at run time.
            pub const fn new() -> Self {
                const __TOTAL: usize = #total;
                const __HEADERS: usize = ::minocrab_std::v3::standards(#placements);
                const __LAYOUT: ::minocrab_std::v3::BlockLayout =
                    ::minocrab_std::v3::BlockLayout::of_block(__TOTAL, __HEADERS);
                #name { #(#inits),* }
            }

            /// The block's DEPLOY-TIME state (notes/ledger-header.org): every
            /// slot's initial value at its path — what compactc's generated
            /// `initialState` builds for the same fields — and a standard's
            /// magic, which no circuit writes. `set` what a Compact
            /// constructor would write (an untyped `LedgerField` is left
            /// Null), then `build`.
            pub fn initial_state() -> ::minocrab_std::v3::StateBuilder {
                const __BLOCK: #name = #name::new();
                #[allow(unused_mut)]
                let mut __state = ::minocrab_std::v3::StateBuilder::new();
                #( ::minocrab_std::v3::InitialState::contribute(&__BLOCK.#idents, &mut __state); )*
                __state
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

        // One standard per ledger block (E0080 if two fields claim
        // `root[0]`), checked here as well as in `new`, so the rule holds
        // for a block whose constructor is never evaluated.
        const _: usize = ::minocrab_std::v3::standards(#placements);
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
        assert!(expanded.contains("event_map : < LedgerMap < B32 < Public > , VaultRecord > > :: at_layout (__LAYOUT , 0usize)"), "{expanded}");
        assert!(expanded.contains("signer : < LedgerField > :: at_layout (__LAYOUT , 0usize + < LedgerMap < B32 < Public > , VaultRecord > as :: minocrab_std :: v3 :: LedgerWidth > :: WIDTH)"), "{expanded}");
        assert!(expanded.contains("initialized : < LedgerCounter > :: at_layout (__LAYOUT , 0usize + < LedgerMap < B32 < Public > , VaultRecord > as :: minocrab_std :: v3 :: LedgerWidth > :: WIDTH + < LedgerField as :: minocrab_std :: v3 :: LedgerWidth > :: WIDTH)"), "{expanded}");
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

    /// …and a SIXTEEN-field block is laid out by `at_layout` over the
    /// block's total, whose `const` segmentation (`FieldPath::in_block`
    /// under `BlockLayout::compactc`) is pinned against [`field_paths`] in
    /// minocrab-std's tests — stage B1's correction (ii) on the derive side.
    #[test]
    fn a_sixteen_field_block_is_laid_out_over_its_total() {
        let fields = (0..16u8).map(|i| {
            let ident = quote::format_ident!("f{i}");
            quote!(#ident: LedgerCell<Uint<64, Public>>)
        });
        let expanded = expansion(syn::parse_quote! {
            struct Wide { #(#fields),* }
        });
        assert!(
            expanded.contains(
                "f0 : < LedgerCell < Uint < 64 , Public > > > :: at_layout (__LAYOUT , 0usize)"
            ),
            "{expanded}"
        );
        assert!(expanded.contains("const __TOTAL : usize = 0usize + < LedgerCell < Uint < 64 , Public > > as :: minocrab_std :: v3 :: LedgerWidth > :: WIDTH"), "{expanded}");
    }

    /// THE LAYOUT IS ONE VALUE per block: `__HEADERS` counts the fields
    /// whose type says `PLACEMENT = RootHeader` (E0080 above one, in
    /// `standards`), and `__LAYOUT` is built from it and `__TOTAL` — so a
    /// block without a standard gets `BlockLayout::compactc(__TOTAL)`, and
    /// nothing in the expansion names a standard.
    #[test]
    fn the_layout_is_computed_from_every_fields_placement() {
        let expanded = expansion(syn::parse_quote! {
            struct Vault {
                event_map: LedgerMap<B32<Public>, VaultRecord>,
                initialized: LedgerCounter,
            }
        });
        let placements = "& [< LedgerMap < B32 < Public > , VaultRecord > as :: minocrab_std :: v3 :: LedgerWidth > :: PLACEMENT , < LedgerCounter as :: minocrab_std :: v3 :: LedgerWidth > :: PLACEMENT]";
        assert!(
            expanded.contains(&format!(
                "const __HEADERS : usize = :: minocrab_std :: v3 :: standards ({placements})"
            )),
            "{expanded}"
        );
        assert!(
            expanded.contains(
                "const __LAYOUT : :: minocrab_std :: v3 :: BlockLayout = :: minocrab_std :: v3 :: BlockLayout :: of_block (__TOTAL , __HEADERS)"
            ),
            "{expanded}"
        );
        // …and the rule is checked at module level too, where it holds
        // whether or not `new` is ever evaluated.
        assert!(
            expanded.contains(&format!(
                "const _ : usize = :: minocrab_std :: v3 :: standards ({placements})"
            )),
            "{expanded}"
        );
    }

    /// A Signet-threaded slot takes the same layout value, and its
    /// `signet_start` is a BODY flat index — the width sum before `Signet`,
    /// which a standard (width 0) does not change.
    #[test]
    fn a_signet_slot_is_threaded_under_the_same_layout() {
        let expanded = expansion(syn::parse_quote! {
            struct Treasury {
                signet: Signet,
                transfers: Pending<Transfer, Owned<Amount>, 2>,
            }
        });
        assert!(expanded.contains("transfers : < Pending < Transfer , Owned < Amount > , 2 > > :: at_layout_with_signet (__LAYOUT , 0usize + < Signet as :: minocrab_std :: v3 :: LedgerWidth > :: WIDTH , 0usize)"), "{expanded}");
        assert!(
            expanded.contains("signet : < Signet > :: at_layout (__LAYOUT , 0usize)"),
            "{expanded}"
        );
    }

    /// 256 body fields and one standard is the widest block: the struct
    /// may declare 257 fields (the width sum is the real bound, asserted
    /// by `FieldPath::in_block`), and 258 is rejected here, spanned.
    #[test]
    fn the_field_count_bound_leaves_room_for_one_standard() {
        let fields = |n: usize| {
            let fields = (0..n).map(|i| {
                let ident = quote::format_ident!("f{i}");
                quote!(#ident: LedgerField)
            });
            syn::parse_quote! { struct Wide { #(#fields),* } }
        };
        expand(fields(257)).expect("256 body fields and a standard expand");
        let error = expand(fields(258)).expect_err("258 fields are rejected");
        assert!(error.to_string().contains("at most 256 fields"), "{error}");
    }

    /// THE DEPLOY STATE: `initial_state()` hands every field, in
    /// declaration order, to its type's `InitialState::contribute` against
    /// the block's own `new()` — calls and paths, no circuit.
    #[test]
    fn the_initial_state_is_every_fields_contribution() {
        let expanded = expansion(syn::parse_quote! {
            struct Vault {
                event_map: LedgerMap<B32<Public>, VaultRecord>,
                std: Mip0099,
                initialized: LedgerCounter,
            }
        });
        assert!(
            expanded.contains("pub fn initial_state () -> :: minocrab_std :: v3 :: StateBuilder"),
            "{expanded}"
        );
        assert!(
            expanded.contains("const __BLOCK : Vault = Vault :: new () ;"),
            "{expanded}"
        );
        let calls = ["event_map", "std", "initialized"].map(|f| {
            format!(
                ":: minocrab_std :: v3 :: InitialState :: contribute (& __BLOCK . {f} , & mut __state) ;"
            )
        });
        let mut at = 0;
        for call in &calls {
            let found = expanded[at..]
                .find(call.as_str())
                .unwrap_or_else(|| panic!("{call} in order:\n{expanded}"));
            at += found + call.len();
        }
        assert!(!expanded.contains("Circuit3"), "{expanded}");
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
