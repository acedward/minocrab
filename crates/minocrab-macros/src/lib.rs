//! Derives for the MinoCrab v3 contract API.
//!
//! The crate depends on nothing of ours and emits fully-qualified
//! `::minocrab_std::v3::…` paths (notes/contract-api.org §macros). Its
//! expansions are exactly what phase 2 wrote by hand — impls a reader could
//! have written — and, by the THINNESS RULE, contain no `Circuit3` method
//! call at all: everything goes through `CircuitArg` and `ArgPath`.
//!
//! # Where this sits
//!
//! A leaf of the build graph, off to the side of the stack: it depends on
//! `syn`/`quote` and nothing of ours, and every path it emits is fully
//! qualified into `minocrab-std` and `minocrab-ledger`. Do not depend on this
//! crate directly — `minocrab-std`'s default `macros` feature re-exports each
//! macro next to the trait it implements, which is where they are documented
//! in context.
//!
//! # Start here
//!
//! - [`macro@circuit`] — a `fn` becomes a circuit; the return type is its
//!   disclosure manifest, and a generated test checks the manifest is honest.
//!   `max_k = N` declares a cost budget and generates a second test
//! - [`macro@contract`] — the block that makes a contract's circuit set
//!   derivable
//! - [`macro@interface`] — declare somebody else's deployed contract, so a
//!   cross-contract call is a typed method
//! - [`macro@CircuitArg`] — arguments as a struct; field order is the wire
//!   contract
//! - [`macro@CircuitBorsh`] — the same, plus canonical Borsh over the
//!   fixed-width subset
//! - [`macro@Ledger`] — the ledger block's declaration-order slot indices
//! - [`macro@LedgerHeader`] — a standard: the header a block's `root[0]`
//!   holds, wherever the block declares it

use proc_macro::TokenStream;

mod circuit;
mod contract;
mod circuit_arg;
mod circuit_borsh;
mod interface;
mod ledger;
mod ledger_header;
mod ledger_repr;

/// Derive [`CircuitArg`] (one nested argument) and `CircuitArgs` (a whole
/// argument list) for a struct with named fields.
///
/// **Field order is the wire contract.** The fields are declared and
/// constrained in declaration order, and that order feeds the input schema,
/// the communications commitment and the proof preimage — reordering the
/// struct silently changes the circuit's ABI.
///
/// Each field's label is its name mapped `snake_case` → `lowerCamelCase`
/// (`erc20_address` → `erc20Address`), which is the Compact field name for
/// every argument in the corpus; `#[arg(name = "…")]` overrides one field's
/// segment where the frozen label differs.
///
/// ```ignore
/// #[derive(CircuitArg)]
/// struct DepositRequest {
///     erc20_address: Bytes<20>,   // depositRequest_erc20Address
///     amount: Uint<128>,          // depositRequest_amount
/// }
/// ```
///
/// The `CircuitArgs` impl is the same list with its fields at the root
/// (`evmNonce` rather than `args_evmNonce`), so one derive serves both a
/// circuit's parameter list and a struct nested inside one.
#[proc_macro_derive(CircuitArg, attributes(arg))]
pub fn derive_circuit_arg(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    circuit_arg::expand(input)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

/// Derive `CircuitBorsh` — canonical Borsh, the fixed-width subset — for a
/// struct with named fields, together with the `CircuitArg` family.
///
/// **Field order is the wire contract, and it is the BORSH order.** The
/// fields are serialized, hashed, read and laid out in declaration order, so
/// reordering the struct changes the format.
///
/// ONE DERIVE, BOTH FAMILIES: the argument impls come from the same code path
/// as [`macro@CircuitArg`], so a type never has both derives — deriving both
/// is a conflicting-implementation error, and `#[derive(CircuitBorsh)]` is
/// the one to keep.
///
/// ```ignore
/// #[derive(CircuitBorsh)]
/// #[borsh(spec = spec_types::RespondMisc)]   // generates the schema cross-check test
/// struct RespondPayload<V: Vis3> {
///     request_id: B32<V>,                    // layout path "request_id"
///     #[borsh(name = "big_r_x")]             // where the spec type names it differently
///     bigr_x: B32<V>,
///     recovery_id: Uint<8, V>,
/// }
/// ```
///
/// A plain struct serializes at `Private`; a struct generic in a single
/// visibility parameter (`<V: Vis3>`) serializes at every visibility, and is
/// a circuit argument at `Private` — arguments are witness data.
///
/// Two label namespaces: the ARGUMENT label is `lowerCamelCase` of the field
/// name (`#[arg(name = "…")]` overrides it), while the LAYOUT path is the
/// field name verbatim, because it is compared against borsh's own schema of
/// the spec type (`#[borsh(name = "…")]` overrides that one).
///
/// `#[borsh(spec = …)]` generates a `#[test]` asserting the layout table is
/// `borsh::schema_container_of::<Spec>()` walked into rows; it needs
/// minocrab-std's `borsh-schema` feature, which a test build enables from its
/// own `[dev-dependencies]`.
///
/// Fields whose Borsh encoding is value-dependent are rejected with the
/// subset's replacement named: `Option` ↦ `Flagged`, `Vec`/`String`/maps ↦
/// `[T; K]` plus a count, a data-carrying enum ↦ one record type per kind, a
/// fieldless enum ↦ `Tag<K>`.
#[proc_macro_derive(CircuitBorsh, attributes(arg, borsh))]
pub fn derive_circuit_borsh(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    circuit_borsh::expand(input)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

/// Derive a contract's LEDGER BLOCK from a struct mirroring Compact's
/// `export ledger` declarations.
///
/// ```ignore
/// #[derive(Ledger)]
/// struct Vault {
///     sign_bidirectional_event_map: LedgerMap<B32<Public>, VaultRecord>,  // field 0
///     signet_signer: LedgerField,                                        // field 1
///     signet_request_nonce: LedgerCounter,                               // field 2
///     vault_evm_address: LedgerCell<Bytes<20, Public>>,                  // field 3
/// }
/// const VAULT: Vault = Vault::new();
/// ```
///
/// **Declaration order is the field index**, which is the on-chain contract:
/// the state a deployed contract holds is keyed by position, so reordering
/// the struct repoints every field after the move. That is the one fact the
/// derive states — `Vault::new()` is a `const fn` whose only content is
/// `<FieldTy>::at(index)` per field — and stating it here is what removes the
/// hand-maintained `const REFUND_COMMITMENT: u8 = 9;` table from contracts.
///
/// The field types are the ledger ADTs of `minocrab_std::v3`
/// (`LedgerMap`/`LedgerCell`/`LedgerCounter`, and `LedgerField` for a field
/// this layer does not model yet); anything with a `const fn at(u8) -> Self`
/// works, since that is all the expansion calls.
/// Make a struct of ledger-storable fields a ledger-storable VALUE (a `Map`
/// value, a `Cell` type): atoms and limbs in declaration order. Fields must
/// be `Public` — `LedgerRepr` exists for public leaves only, so a private
/// field is a type error, not a leak.
#[proc_macro_derive(LedgerRepr)]
pub fn derive_ledger_repr(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    ledger_repr::expand(input)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

#[proc_macro_derive(Ledger)]
pub fn derive_ledger(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    ledger::expand(input)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

/// Derive a STANDARD's slot side: `LedgerWidth` with `WIDTH = 0` and
/// `PLACEMENT = Placement::root_header::<Self>()`, `at_layout`, `magic()`,
/// the deploy state (`InitialState`: the magic, then the fields), and the
/// compile-time
/// checks (a non-zero magic; at most 15 named fields, each a single-field
/// std slot). The magic itself is the hand-written
/// `impl LedgerHeader for T { const MAGIC: [u8; 32] = pad32(b"…"); }`.
/// A unit struct is magic-only (`[0]`); named fields follow the magic in
/// the header Array (`[0, i + 1]`).
#[proc_macro_derive(LedgerHeader)]
pub fn derive_ledger_header(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    ledger_header::expand(input)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

/// Turn a plain typed function into a circuit entry point.
///
/// ```ignore
/// #[circuit]
/// pub fn deposit(c: &mut Circuit3, evm_nonce: Uint<64>, deposit_request: DepositRequest) {
///     let one = c.constant(1u64);
///     ..
/// }
/// ```
///
/// The parameters after `c: &mut Circuit3` are the circuit's arguments, in
/// declaration order — **which is the wire contract**, exactly as for
/// [`macro@CircuitArg`]: they become the fields of a hidden argument struct
/// carrying that derive's impls, and `deposit` becomes the familiar
/// `pub fn deposit() -> Compiled3` that declares them, constrains them from
/// their types, and runs the body. Labels are the same mechanical
/// `snake_case` → `lowerCamelCase` rule, with the same
/// `#[arg(name = "…")]` escape hatch, written on the parameter.
///
/// A function returning `()` is Compact's `: []` entry point. One that
/// returns a value discloses it, and names it with
/// `#[circuit(output = "…")]`; only `CircuitOut` types — which are `Public`
/// — can be returned, so a private value has to pass through `disclose`
/// first.
///
/// An unused argument is legitimate (a slot can exist only to be part of the
/// wire shape); silence the warning the way Rust always does, with a leading
/// underscore — the label is unaffected, since `_recovery_id` and
/// `recovery_id` both map to `recoveryId`.
///
/// # `max_k` — a declared cost budget
///
/// ```ignore
/// #[circuit(max_k = 14)]
/// pub fn deposit(c: &mut Circuit3, evm_nonce: Uint<64>) { .. }
/// ```
///
/// generates one more test beside the entry point: build the circuit, price
/// it with minocrab-sim's cost model (Midnight's own), and fail if its `k` —
/// log2 of the proving-table rows — is above the number declared here. `k` is
/// what sets the proving key, the prover's RAM and the wall clock, so a
/// budget is the guard against a change that is free in rows and expensive in
/// powers of two. A circuit UNDER budget passes and says by how much.
///
/// `max_k` combines with `output`, in either order:
/// `#[circuit(output = "event hash", max_k = 9)]`.
///
/// The generated test names `::minocrab_sim`, so a crate that declares a
/// budget needs `minocrab-sim` among its `[dev-dependencies]`. It is the one
/// crate a `#[circuit]` expansion can require beyond minocrab-std, and only
/// when the author asks for a budget.
#[proc_macro_attribute]
pub fn circuit(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = syn::parse_macro_input!(attr as circuit::CircuitAttr);
    let item = syn::parse_macro_input!(item as syn::ItemFn);
    circuit::expand(attr, item)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

/// A contract: its state type, and the circuits it exports.
///
/// ```text
/// #[derive(Ledger)]
/// pub struct Vault { pub balances: LedgerMap<B32<Public>, Uint<128, Public>> }
///
/// #[contract]
/// impl Vault {
///     #[circuit]
///     pub fn deposit(c: &mut Circuit3, amount: Uint<128>) -> Discloses<(Amount,)> { … }
/// }
/// ```
///
/// The circuits are ASSOCIATED FUNCTIONS taking `c: &mut Circuit3` — there is
/// no receiver, and a `self` parameter is a compile error with the reason. A
/// contract's state is a layout rather than a value: a ledger read is a
/// transcript gate and a write is an Impact op, so there is nothing in `self`
/// to borrow, and putting the circuit inside the state value would force
/// either interior mutability or a second calling convention beside the
/// `&mut Circuit3` every gadget below already takes.
///
/// What the block buys is that the LANGUAGE knows the circuit set:
/// `Vault::CIRCUITS` is `[(name, fn() -> Compiled3); N]` in declaration
/// order, derived from the file. Before it, a contract was a module by
/// convention and its circuits were a hand-written list in a test-support
/// module that nothing checked for completeness.
///
/// Each `#[circuit]` inside expands exactly as it does on a free function —
/// same argument struct, same labels, same disclosure declaration, same
/// `max_k` budget — except that its generated tests are emitted BESIDE the
/// `impl`, since a `mod` cannot live inside one.
#[proc_macro_attribute]
pub fn contract(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        let attr = proc_macro2::TokenStream::from(attr);
        return syn::Error::new_spanned(attr, "#[contract] takes no arguments")
            .to_compile_error()
            .into();
    }
    let item = syn::parse_macro_input!(item as syn::ItemImpl);
    contract::expand(item)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

/// Declare another contract's circuits and get a typed calling handle.
///
/// ```ignore
/// #[interface]
/// pub trait Token {
///     /// `circuit deposit(amount: Uint<128>, caller: ContractAddress): Bytes<32>`
///     fn deposit(amount: Uint<128, Public>, caller: ContractAddress<Public>) -> B32<Public>;
///     #[entry_point(name = "depositEmit")]
///     fn deposit_emit(recipient: B32<Public>, amount: Uint<128, Public>);
/// }
///
/// let hash = Token::at_field(TOKEN).deposit(c, amount, me);
/// ```
///
/// The trait is REPLACED by a handle struct with an inherent impl: an
/// `EntryPoint` const per circuit, `at_field(index)` / `at(address)`
/// constructors, and one typed method per circuit over
/// `minocrab_ledger::call`.
///
/// **The entry-point keys are derived, never typed.** A circuit's 32-byte
/// key is `EntryPoint::hash` of its Compact name, which is the method name
/// mapped `snake_case` → `lowerCamelCase`; `#[entry_point(name = "…")]`
/// overrides one where the Compact name is not the mechanical form.
///
/// **Arguments and results are `Public`.** Passing a value to another
/// contract discloses it — it enters the communications commitment the
/// ledger matches in the clear — so a private value must `disclose()`
/// first, and a parameter written at `Private`, or left to default to it,
/// is a compile error that says so.
///
/// **No address appears in the expansion.** `at_field` names a ledger field
/// and `at` takes an address at runtime, so an interface crate is publishable
/// without knowing where its contract is deployed.
///
/// The generated methods take `c: &mut Circuit3` before the callee's own
/// parameters — no guard parameter (notes/edsl-trim.org §B): the call
/// resolves the AMBIENT scope, so a guarded call is `c.when(g, |c|
/// callee.deposit(c, amount, me))`. The expansion needs `minocrab_ledger` and
/// `minocrab_std` in the using crate's dependencies.
#[proc_macro_attribute]
pub fn interface(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        let attr: proc_macro2::TokenStream = attr.into();
        return syn::Error::new_spanned(attr, "#[interface] takes no arguments")
            .into_compile_error()
            .into();
    }
    let item = syn::parse_macro_input!(item as syn::ItemTrait);
    interface::expand(item)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}
