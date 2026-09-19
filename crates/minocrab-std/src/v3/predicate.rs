//! Assertion predicates: `c.assert(less_than(0u64, amount))`.
//!
//! A predicate is an INERT DESCRIPTOR of a check. `less_than(a, b)` builds a
//! value and emits nothing; `c.assert(p)` lowers it — the comparison
//! instruction and the `assert`, at the assert site. An unasserted predicate
//! therefore costs nothing at all and warns ([`Check`] is `#[must_use]`),
//! which is strictly safer than today's unasserted `c.less_than(..)`: that
//! one emits cost, constrains nothing, and no lint says so.
//!
//! WHAT IT BUYS is soundness wearing ergonomics clothing:
//!
//! - **the width comes from the operand TYPES.** `c.less_than(a, b, 128)`
//!   takes the width as a hand-typed number — the same genus of bug as the
//!   hand-written `assert_bits` blocks the typed leaves removed, and just as
//!   invisible to PI equality on honest preimages. `less_than(a, amount)`
//!   with `amount: Uint<128>` reads the 128 off the type. Two typed operands
//!   must agree, and an ordering needs at least one width to run at; both are
//!   inline-`const` asserts, so both are COMPILE errors at the call site
//!   naming the fix, not a silently wrong range and not a panic when the
//!   circuit is built (see [`less_than`]'s neighbours below).
//! - **the constant side is a CHECKED IMMEDIATE.** A literal operand becomes
//!   a v3 inline immediate (`Operand`, phase 7's literals piece — no `Copy`),
//!   and it is checked at build time against the width it is being compared
//!   at: `less_than(byte, 300u64)` on a `Bytes<1>` panics rather than
//!   comparing against a value the width cannot hold. THE ONE REMAINING
//!   PANIC of this module, and it stays one because the magnitude of a
//!   runtime integer is not in the type system: `300u64` is a value, not a
//!   type, so nothing const-evaluable knows it.
//!
//! SCOPE, deliberately hard (notes/contract-api.org §The design): comparisons
//! (`less_than`/`le`/`greater_than`/`ge`/`eq`/`ne`), the combinators
//! [`not`]/[`Check::and`]/[`Check::or`], an optional message
//! ([`Check::message`], Compact's second `assert` argument), the boolean leaf
//! [`is_true`], and [`Check::eval`] for a
//! circuit that wants the boolean wire. The in-branch form is
//! [`Circuit3::when`](minocrab::v3::Circuit3::when): `c.when(g, |c|
//! c.assert(p))` rather than a `Check` method (notes/edsl-trim.org §B). NO
//! deferred
//! ARITHMETIC and no expression templates: `a + b` returning a descriptor
//! would hide emission inside an operator, which is the no-hidden-cost rule
//! this whole layer is built on. And no macros — these are ordinary functions
//! and methods.
//!
//! Two surfaces, one implementation: the free constructors here, and the
//! same names as methods on the typed leaves (`amount.gt(0u64)`), which
//! delegate.
//!
//! Rust fact shaping all of it: `PartialOrd` is hardwired to return `bool`,
//! so `amount > 0` can never be a circuit expression. Named constructors are
//! the ceiling, and they are what this module provides.

use minocrab::v3::{uint_compare_bits, Assertion, Circuit3, FieldT, Operand, Wire3};
use minocrab::{Fr, Meet, Public};

use super::{Bool, BoundedUint, Bytes, Uint, Vis3};

/// The comparison a [`Check`] leaf describes, and how it lowers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Cmp {
    /// `a < b` — `less_than a b bits`.
    Less,
    /// `a == b` — `test_eq a b` (no width needed).
    Equal,
}

/// A deferred check. Build one with [`less_than`] and friends, then
/// `c.assert(p)` (or `p.eval(c)` for the wire).
///
/// `V` is the visibility of the result: comparing a private value against
/// anything is private, and the constant side is public, so the usual
/// [`Meet`] applies.
#[must_use = "a predicate describes a check and emits nothing on its own — \
              assert it with `c.assert(p)`, or evaluate it with `p.eval(c)`"]
pub struct Check<V: Vis3> {
    node: Node<V>,
    message: Option<&'static str>,
}

enum Node<V: Vis3> {
    /// A comparison, with the width already resolved from the operand types.
    Compare {
        cmp: Cmp,
        a: Operand<FieldT, V>,
        b: Operand<FieldT, V>,
        bits: u32,
        /// The lowering ends in `not` (`ne`, `le`, `ge` are negated forms).
        negated: bool,
    },
    /// A boolean that is already a wire ([`is_true`]) — zero instructions.
    Leaf(Wire3<FieldT, V>),
    Not(Box<Node<V>>),
    And(Box<Node<V>>, Box<Node<V>>),
    Or(Box<Node<V>>, Box<Node<V>>),
}

/// One side of a comparison: a typed leaf (which carries the WIDTH), a raw
/// wire (which does not), or a native Rust literal (which becomes an inline
/// immediate, and is range-checked against the width the comparison runs at).
///
/// Implemented for the `Public` leaves at every visibility, because a public
/// value may be compared against a private one — the result is then private,
/// which is what [`Meet`] says.
///
/// An ORDERING needs a WIDTH on top of this — see the note below the impls.
pub trait CheckOperand {
    /// The visibility this operand contributes.
    type Vis: Vis3;

    /// The width this operand's TYPE carries, if any. `None` for a raw wire
    /// and for a literal.
    const BITS: Option<u32>;

    /// The LARGEST VALUE this operand's type admits, if the type says.
    /// `None` for a raw wire, for a literal, and wherever the answer does
    /// not fit a `u128` (a width that wide constrains nothing a literal
    /// could violate).
    ///
    /// Distinct from [`CheckOperand::BITS`], and the distinction is the
    /// whole point: a `BoundedUint<300>` is COMPARED at 9 bits, so a literal
    /// `500` fits the width and is still a value the operand can never take.
    /// Comparing against it is a constant, and constants written as
    /// comparisons are bugs — see `check_literal_within`.
    const MAX: Option<u128> = None;

    /// The value, if it is a literal — what the range check looks at.
    fn literal(&self) -> Option<Fr> {
        None
    }

    /// The operand itself.
    fn operand(self) -> Operand<FieldT, Self::Vis>;
}

impl<V: Vis3> CheckOperand for Wire3<FieldT, V> {
    type Vis = V;
    const BITS: Option<u32> = None;

    fn operand(self) -> Operand<FieldT, V> {
        self.into()
    }
}

impl<const BITS: u32, V: Vis3> CheckOperand for Uint<BITS, V> {
    type Vis = V;
    const BITS: Option<u32> = Some(BITS);
    const MAX: Option<u128> = if BITS >= 128 {
        None
    } else {
        Some((1u128 << BITS) - 1)
    };

    fn operand(self) -> Operand<FieldT, V> {
        self.field().into()
    }
}

/// A bounded value's comparison width is the bit length of its LARGEST
/// LEGAL VALUE (`max(1, intlen(BOUND − 1))`), which is compactc's own rule
/// for an ordering (infer-types.ss:753-771) and NOT the even-rounded width
/// its range constraint runs at: a `Uint<0..70000>` is constrained at 18
/// bits and compared at 17, in the same compactc artifact
/// (notes/bounded-integers.org §2).
///
/// Sound because every legal value is `≤ BOUND − 1 < 2^intlen(BOUND − 1)`.
impl<const BOUND: u128, V: Vis3> CheckOperand for BoundedUint<BOUND, V> {
    type Vis = V;
    const BITS: Option<u32> = Some(uint_compare_bits(BOUND - 1));
    /// The bound is EXCLUSIVE (`Uint<0..BOUND>`), so the largest legal value
    /// is `BOUND - 1` — the correction M14 had to make to three of our own
    /// records (notes/bounded-integers.org).
    const MAX: Option<u128> = Some(BOUND - 1);

    fn operand(self) -> Operand<FieldT, V> {
        self.field().into()
    }
}

impl<const N: usize, V: Vis3> CheckOperand for Bytes<N, V> {
    type Vis = V;
    const BITS: Option<u32> = Some(8 * N as u32);
    const MAX: Option<u128> = if N >= 16 {
        None
    } else {
        Some((1u128 << (8 * N)) - 1)
    };

    fn operand(self) -> Operand<FieldT, V> {
        self.field().into()
    }
}

impl<V: Vis3> CheckOperand for Bool<V> {
    type Vis = V;
    const BITS: Option<u32> = Some(1);
    const MAX: Option<u128> = Some(1);

    fn operand(self) -> Operand<FieldT, V> {
        self.field().into()
    }
}

/// Literals: public, no width of their own, and range-checked against the
/// width of whatever they are compared with.
macro_rules! literal_operand {
    ($($ty:ty),* $(,)?) => {$(
        impl CheckOperand for $ty {
            type Vis = Public;
            const BITS: Option<u32> = None;

            fn literal(&self) -> Option<Fr> {
                Some(Fr::from(u64::from(*self)))
            }

            fn operand(self) -> Operand<FieldT, Public> {
                self.into()
            }
        }
    )*};
}

literal_operand!(u64, u32, u8, bool);

impl CheckOperand for Fr {
    type Vis = Public;
    const BITS: Option<u32> = None;

    fn literal(&self) -> Option<Fr> {
        Some(*self)
    }

    fn operand(self) -> Operand<FieldT, Public> {
        self.into()
    }
}

/// WHERE THE WIDTH COMES FROM, and what happens when it comes from nowhere
/// (dmd 2026-08-15, decision B — M9 phase 8).
///
/// `less_than a b bits` is unsound if either operand exceeds `bits`, so an
/// ORDERING needs a width: a typed leaf carries one in its type, a literal
/// adopts the other side's and is range-checked against it, and a raw `Wire3`
/// carries none. An ordering of TWO widthless operands is therefore rejected
/// — and rejected at COMPILE time, by the inline-`const` assert in each
/// ordering constructor (`error[E0080]`, with the fix in the message), not by
/// a panic when the circuit is built.
///
/// It is not expressed as a missing `CheckOperand` impl for `Wire3`, which
/// would have been the better error, for two reasons that are the same
/// reason: the condition is a property of the PAIR, not of one operand. A
/// raw wire on ONE side of a typed comparison (`amount.gt(zero_wire)`, where
/// `amount: Uint<128>` supplies the 128) is accepted, as it always has been —
/// the direct ports rely on it, since a constant they also need as a WIRE
/// stays named rather than becoming an immediate — and "at least one of A, B
/// carries a width" is not something a trait bound can say without
/// overlapping impls.
///
/// What this layer will NOT do either way is emit the range constraint for
/// you: that would be silent cost, and the author is the one who knows
/// whether the wire is already constrained. The explicit forms are
/// `Uint::<64>::from_field_unchecked(w)` (plus `constrain_input` if nothing has
/// constrained it yet) and `c.less_than(a, b, bits)`.
///
/// The visibility of a comparison of an `A` with a `B`: the meet.
type Joined<A, B> = <<A as CheckOperand>::Vis as Meet<<B as CheckOperand>::Vis>>::Out;

/// Do these two operand types agree on a width? (Either may carry none — a
/// literal never does.) Evaluated in an inline `const`, so a mismatch is a
/// BUILD ERROR at the call site, not a panic when the circuit is built.
const fn widths_agree(a: Option<u32>, b: Option<u32>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => a == b,
        _ => true,
    }
}

/// Does at least one operand type carry a width? An ordering needs one.
const fn some_width(a: Option<u32>, b: Option<u32>) -> bool {
    a.is_some() || b.is_some()
}

/// The comparison constructors. `Joined` is the meet of the two operands'
/// visibilities; the `Meet` bounds are the lattice's commutativity, which
/// rustc cannot derive but every concrete pair satisfies.
macro_rules! comparison {
    ($(
        $(#[$m:meta])*
        $name:ident($a:ident, $b:ident): $kind:ident => $cmp:expr, negated: $neg:expr, order: ($first:ident, $second:ident)
    );* $(;)?) => {$(
        $(#[$m])*
        #[track_caller]
        pub fn $name<A: CheckOperand, B: CheckOperand>($a: A, $b: B) -> Check<Joined<A, B>>
        where
            A::Vis: Meet<B::Vis>,
            B::Vis: Meet<A::Vis, Out = Joined<A, B>>,
            Joined<A, B>: Vis3,
        {
            const {
                assert!(
                    widths_agree(A::BITS, B::BITS),
                    "the two operands of a comparison have different widths, and \
                     the width a comparison runs at comes from the operand types: \
                     give both sides the same type (a `Uint<BITS>`, a `Bytes<N>`), \
                     or widen the narrow one explicitly with `.widen::<BITS>()` — \
                     free for a leaf that is already range-constrained"
                )
            };
            comparison!(@width $kind, A, B);
            compare($cmp, $neg, $first, $second)
        }
    )*};
    (@width ordering, $A:ident, $B:ident) => {
        const {
            assert!(
                some_width($A::BITS, $B::BITS),
                "an ordering comparison needs a width and neither operand's type \
                 carries one: compare TYPED values (a `Uint<BITS>`, a `Bytes<N>`), \
                 which is where the width comes from"
            )
        };
    };
    (@width equality, $A:ident, $B:ident) => {};
}

comparison! {
    /// `a < b`. The width comes from the operand types.
    less_than(a, b): ordering => Cmp::Less, negated: false, order: (a, b);
    /// `a > b` — `less_than(b, a)`, the same instruction with the operands
    /// the other way round.
    greater_than(a, b): ordering => Cmp::Less, negated: false, order: (b, a);
    /// `a <= b` — `!(b < a)`, which is a `less_than` and a `not`.
    le(a, b): ordering => Cmp::Less, negated: true, order: (b, a);
    /// `a >= b` — `!(a < b)`.
    ge(a, b): ordering => Cmp::Less, negated: true, order: (a, b);
    /// `a == b`. No width is needed: `test_eq` compares field elements, so
    /// raw wires are allowed here.
    eq(a, b): equality => Cmp::Equal, negated: false, order: (a, b);
    /// `a != b` — `test_eq` and a `not`.
    ne(a, b): equality => Cmp::Equal, negated: true, order: (a, b);
}

/// The shared body of the constructors: resolve the width from the types,
/// range-check a literal against it, and build the descriptor. `first` and
/// `second` are the operands in the order the INSTRUCTION takes them, which
/// is why `greater_than` is `less_than` with them swapped.
#[track_caller]
fn compare<F: CheckOperand, S: CheckOperand>(
    cmp: Cmp,
    negated: bool,
    first: F,
    second: S,
) -> Check<Joined<F, S>>
where
    F::Vis: Meet<S::Vis>,
    S::Vis: Meet<F::Vis, Out = Joined<F, S>>,
    Joined<F, S>: Vis3,
{
    let bits = width(cmp, F::BITS, S::BITS);
    if let Some(bits) = bits {
        check_literal_fits(first.literal(), bits);
        check_literal_fits(second.literal(), bits);
    }
    // …and the narrower check the width alone cannot make: a literal outside
    // what the OTHER operand's type can hold makes the comparison a constant.
    check_literal_within(first.literal(), S::MAX, S::BITS);
    check_literal_within(second.literal(), F::MAX, F::BITS);
    Check {
        node: Node::Compare {
            cmp,
            a: first.operand().meet::<S::Vis>(),
            b: second.operand().meet::<F::Vis>(),
            bits: bits.unwrap_or(0),
            negated,
        },
        message: None,
    }
}

/// The width a comparison runs at, read off the operand types.
///
/// Both disagreement cases are impossible here — the constructors' inline
/// `const` asserts reject them at COMPILE time, and an ordering over
/// widthless operands cannot be spelled at all ([`OrderOperand`]) — so this
/// is a total function over what can reach it, with `debug_assert`s standing
/// where the diagnostics used to.
fn width(cmp: Cmp, a: Option<u32>, b: Option<u32>) -> Option<u32> {
    match (a, b) {
        (Some(a), Some(b)) => {
            debug_assert_eq!(a, b, "the const assert should have rejected this");
            Some(a)
        }
        (Some(bits), None) | (None, Some(bits)) => Some(bits),
        (None, None) => {
            debug_assert!(cmp == Cmp::Equal, "the const assert should have rejected this");
            None
        }
    }
}


/// A literal compared against a typed operand has to be a value that operand
/// can actually TAKE.
///
/// [`check_literal_fits`] above asks whether the literal fits the comparison
/// WIDTH, which is a weaker question and misses the case bounded integers make
/// common: a `BoundedUint<300>` compares at 9 bits, so `b.lt(500u64)` fits the
/// width and is nonetheless always true, because `b` is at most 299. A
/// comparison whose answer is fixed at build time is a bug in every case we
/// can construct — the author meant a different constant, or a different type.
///
/// BUILD-TIME PANIC, and recorded as one (per dmd's compile-errors-over-panics
/// rule, notes/contract-api.org §"Panics"): a literal's MAGNITUDE is not a
/// type, so there is nothing for an inline `const` assert to look at. dmd
/// authorised this position explicitly on 2026-08-16 — "definitely catch if
/// the literal you're using is larger than the bound if you can, you can fail
/// at compile time or test/IR generation time". Closing it at compile time
/// needs the literal as a const generic (`lit::<500>()`), which is the open
/// API-shape question in the same section and a bigger change than the bug is
/// worth today.
#[track_caller]
fn check_literal_within(literal: Option<Fr>, max: Option<u128>, bits: Option<u32>) {
    let (Some(value), Some(max)) = (literal, max) else {
        return;
    };
    let Some(as_u128) = fr_as_u128(value) else {
        // Wider than a u128 and therefore wider than any `max` we hold; the
        // width check above already rejected it if the width was known.
        return;
    };
    assert!(
        as_u128 <= max,
        "the literal {as_u128} is larger than the largest value the operand it \
         is compared with can hold ({max}), so this comparison has the same \
         answer for every input — fix: compare against a constant in 0..={max}, \
         or widen the operand's type if it should be able to reach {as_u128}\
         {}",
        match bits {
            Some(bits) => format!(" (the comparison itself runs at {bits} bits, which is why the width check above accepts it)"),
            None => String::new(),
        }
    );
}

/// A field element as a `u128`, or `None` if it does not fit one.
fn fr_as_u128(value: Fr) -> Option<u128> {
    let bytes = value.as_le_bytes();
    if bytes.iter().skip(16).any(|&b| b != 0) {
        return None;
    }
    let mut buf = [0u8; 16];
    for (i, &b) in bytes.iter().take(16).enumerate() {
        buf[i] = b;
    }
    Some(u128::from_le_bytes(buf))
}

/// A literal compared at `bits` has to fit in `bits`.
///
/// `#[track_caller]` all the way up — this function, `check_literal_within`,
/// `compare`, the six constructors the `comparison!` macro generates and the
/// six methods `comparison_methods!` generates — so that `amount.lt(300u64)`
/// is blamed on the line that wrote it. A link added to that chain without
/// the attribute silently moves the blame back here.
#[track_caller]
fn check_literal_fits(literal: Option<Fr>, bits: u32) {
    let Some(value) = literal else { return };
    let bytes = value.as_le_bytes();
    let fits = bytes.iter().enumerate().all(|(i, &byte)| {
        let low = (i as u32) * 8;
        if low >= bits {
            byte == 0
        } else {
            let room = bits - low;
            room >= 8 || byte >> room == 0
        }
    });
    assert!(
        fits,
        "the literal {value:?} does not fit the {bits} bits the comparison \
         runs at — a constant compared against a Uint<{bits}> has to be one"
    );
}

/// A boolean that is ALREADY a wire, as a predicate leaf (M9 phase 8,
/// candidate 5) — a map `member` result, an in-branch condition, anything a
/// comparison did not produce.
///
/// Costs ZERO: the lowering is the wire itself, so `c.assert(is_true(b))` and
/// `c.assert(b)` are the same instruction stream. What it buys is that the
/// rest of the surface applies to such a value: `.message(..)`, `.and`/`.or`,
/// [`not`], and the [`Circuit3::when`](minocrab::v3::Circuit3::when) scope —
/// before this, those sites had to drop out of the predicate vocabulary into
/// `c.assert_with(cond, Some(msg))`.
pub fn is_true<V: Vis3>(b: impl Into<Bool<V>>) -> Check<V> {
    let b: Bool<V> = b.into();
    Check {
        node: Node::Leaf(b.field()),
        message: None,
    }
}

/// `!p`.
pub fn not<V: Vis3>(p: Check<V>) -> Check<V> {
    Check {
        node: Node::Not(Box::new(p.node)),
        message: p.message,
    }
}

impl<V: Vis3> Check<V> {
    /// Compact's second `assert` argument: what the check means, surfaced by
    /// the simulator when it fails. Metadata — no instruction, no row.
    pub fn message(self, message: &'static str) -> Self {
        Check {
            message: Some(message),
            ..self
        }
    }

    /// `self && other` — one `mul` over the two lowered booleans.
    pub fn and(self, other: Check<V>) -> Check<V> {
        Check {
            node: Node::And(Box::new(self.node), Box::new(other.node)),
            message: self.message.or(other.message),
        }
    }

    /// `self || other` — De Morgan, `!(!self && !other)`: three `not`s and a
    /// `mul`. Written out rather than folded, because a combinator that
    /// quietly simplified would be hiding cost.
    pub fn or(self, other: Check<V>) -> Check<V> {
        Check {
            node: Node::Or(Box::new(self.node), Box::new(other.node)),
            message: self.message.or(other.message),
        }
    }

    /// Lower to the boolean wire, for a circuit that wants the value (a
    /// branch guard, a `cond_select`) rather than an assertion. This is the
    /// escape hatch; `c.assert(p)` is the normal path.
    pub fn eval(self, c: &mut Circuit3) -> Bool<V> {
        Bool::from_field_unchecked(lower(c, self.node))
    }
}

/// A predicate is what `Circuit3::assert` takes: it lowers HERE, at the
/// assert, and the message rides along as metadata.
impl<V: Vis3> Assertion for Check<V> {
    fn assert_in(self, c: &mut Circuit3) {
        let message = self.message;
        let cond = lower(c, self.node);
        c.assert_with(cond, message);
    }
}

/// A boolean leaf asserts as its wire does.
impl<V: Vis3> Assertion for Bool<V> {
    fn assert_in(self, c: &mut Circuit3) {
        c.assert_with(self.field(), None);
    }
}

/// An assumed boolean asserts as the boolean does.
impl<V: Vis3> Assertion for crate::v3::Assumed<Bool<V>> {
    fn assert_in(self, c: &mut Circuit3) {
        Bool::from(self).assert_in(c)
    }
}

impl<V: Vis3> Check<V> {
    /// Lower this predicate to its wire, for use as a GUARD rather than as
    /// an assertion — see [`Guarded`](crate::v3::Guarded).
    pub fn into_wire(self, c: &mut Circuit3) -> Wire3<FieldT, V> {
        lower(c, self.node)
    }
}

/// A [`Check`] used as a guard, so `when(..)` / `else_when(..)` read the
/// same whether the condition is a wire or the predicate vocabulary.
/// A [`Bool`] used as a guard — the typed spelling, so a `when` site takes
/// the boolean itself rather than its `.field()`. A `Bool` is 0 or 1 by
/// construction (`from_field_checked`, a comparison's output, a constrained
/// argument), which is what an Impact guard and a `cond_select` bit require:
/// the reference circuit converts either to an assigned bit under an
/// equality constraint, so a non-boolean guard is UNSATISFIABLE, never
/// silently wrong.
impl<V: Vis3> minocrab::v3::GuardCond<V> for crate::v3::Bool<V> {
    fn into_guard(self, _c: &mut Circuit3) -> Wire3<FieldT, V> {
        self.field()
    }
}

impl<V: Vis3> minocrab::v3::GuardCond<V> for Check<V> {
    fn into_guard(self, c: &mut Circuit3) -> Wire3<FieldT, V> {
        self.into_wire(c)
    }
}

/// THE LOWERING, and the whole claim of this module: every node emits
/// exactly the instructions the hand-written form emits, in the same order.
fn lower<V: Vis3>(c: &mut Circuit3, node: Node<V>) -> Wire3<FieldT, V> {
    match node {
        Node::Compare {
            cmp,
            a,
            b,
            bits,
            negated,
        } => {
            let value = match cmp {
                Cmp::Less => c.less_than(a, b, bits),
                Cmp::Equal => c.test_eq(a, b),
            };
            if negated {
                c.not(value)
            } else {
                value
            }
        }
        Node::Leaf(w) => w,
        Node::Not(inner) => {
            let value = lower(c, *inner);
            c.not(value)
        }
        Node::And(left, right) => {
            let left = lower(c, *left);
            let right = lower(c, *right);
            c.mul(left, right)
        }
        Node::Or(left, right) => {
            let left = lower(c, *left);
            let left = c.not(left);
            let right = lower(c, *right);
            let right = c.not(right);
            let both = c.mul(left, right);
            c.not(both)
        }
    }
}

// ---- the method surface ------------------------------------------------------
//
// The same predicates as methods on the typed leaves, delegating to the free
// constructors above so there is one implementation. `amount.gt(0u64)` and
// `greater_than(amount, 0u64)` are the same value.

macro_rules! comparison_methods {
    ($self_ty:ty, [$($gen:tt)*], $vis:ident, [$($name:ident => $free:ident, $doc:literal),* $(,)?]) => {
        impl<$($gen)*> $self_ty {
            $(
                #[doc = $doc]
                #[track_caller]
                pub fn $name<B: CheckOperand>(self, other: B) -> Check<<$vis as Meet<B::Vis>>::Out>
                where
                    $vis: Meet<B::Vis>,
                    B::Vis: Meet<$vis, Out = <$vis as Meet<B::Vis>>::Out>,
                    <$vis as Meet<B::Vis>>::Out: Vis3,
                {
                    $free(self, other)
                }
            )*
        }
    };
}

macro_rules! leaf_comparisons {
    ($self_ty:ty, [$($gen:tt)*], $vis:ident) => {
        comparison_methods!($self_ty, [$($gen)*], $vis, [
            lt => less_than, "`self < other` — [`less_than`].",
            gt => greater_than, "`self > other` — [`greater_than`].",
            le => le, "`self <= other` — [`le`].",
            ge => ge, "`self >= other` — [`ge`].",
            eq => eq, "`self == other` — [`eq`].",
            ne => ne, "`self != other` — [`ne`].",
        ]);
    };
}

leaf_comparisons!(Uint<BITS, V>, [const BITS: u32, V: Vis3], V);
leaf_comparisons!(BoundedUint<BOUND, V>, [const BOUND: u128, V: Vis3], V);
leaf_comparisons!(Bytes<N, V>, [const N: usize, V: Vis3], V);
leaf_comparisons!(Bool<V>, [V: Vis3], V);
