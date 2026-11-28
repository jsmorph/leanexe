module

public import Mathlib.Data.Nat.Digits.Lemmas
public import Library.Numerics.MultiPrecision.Spec
public import Library.Numerics.Decimal.Int64Text.Spec
public import Library.Numerics.Bignum.Types

@[expose] public section

/-!
The specification of the arbitrary-precision naturals and integers.

A natural number is an array of limbs, each a word below `2^32`, least significant first, and its
value is MultiPrecision's `value u = Σ u[i] · 2^(32 i)`.  Its canonical form `limbsOf n` holds the
base-`2^32` digits of `n` from Mathlib's `Nat.digits`, so it has no zero limb at the top and zero is
the empty array.  `Canonical u` states that every limb is below `2^32` and that the top limb, when
there is one, is not 0.  An integer is a `BigInt`, a sign and a magnitude, and its canonical form
`BigInt.ofInt z` has the canonical magnitude of `|z|` and the sign `z < 0`, so zero has the one form
`⟨false, #[]⟩`.  `BigInt.Canonical x` states that `x` is the canonical form of the integer it
denotes, which holds exactly when its magnitude is canonical and its sign is false when the
magnitude is empty.

Each library function is specified as the canonical form of the exact result over `ℕ` or `ℤ`, and
the theorems take canonical arguments; the results on other arguments have no meaning.  `natTrim`
takes any array of limbs below `2^32` and returns the canonical form of its value.  Each theorem
also assumes that every array argument has fewer than `2^32` words, which keeps the word
arithmetic on lengths and positions exact; an array in WebAssembly's 32-bit memory has fewer than
`2^29` words, so the call theorems discharge it.

Comparison returns 0, 1, or 2 when the first argument is less than, equal to, or greater than the
second.  Subtraction of naturals returns the flag `a < b` and the canonical limbs of `|a - b|`.
Division of naturals returns the quotient and the remainder.  The signed divisions are Lean's: the
truncated `Int.tdiv` and `Int.tmod`, which round the quotient toward zero and give the remainder
the dividend's sign, and the Euclidean `/` and `%` of `Int`, whose remainder is never negative for
a nonzero divisor.  The library functions follow Lean's total convention at a zero divisor,
`x / 0 = 0` and `x % 0 = x`, for every one of these, so a negative dividend has a negative
remainder at a zero divisor in both signed divisions.

Text is an array of words that hold one byte each, as in leanexe's `Int64Text`.  `printSpec z` is
the bytes of Lean's `toString z`: `-` before the digits of a negative value, no leading zero, and
`0` for zero.  `readSpec s` reads the grammar of `Int64Text.denote`,

```
integer = "0" / [ "-" ] nonzero *digit
```

with no bound on the value: it returns `(true, BigInt.ofInt z)` for a text of the grammar that
denotes `z`, and `(false, BigInt.ofInt 0)` for every other array, among them the empty array, a lone
`-`, `-0`, a leading `+`, a leading zero, white space, any other byte, and a word above 255.  Each
integer has one text in the grammar, the printer's.  The text form "an optional leading `-` and no
leading zero except in `0`" also admits the reading `["-"] ("0" / nonzero *digit)`, which accepts
`-0`; Int64Text's grammar rejects `-0`, so that reading and printing are exact inverses
(`readSpec_print` and `print_of_readSpec`).

The exports of the compiled module are `natTrim`, `natCmp`, `natAdd`, `natSub`, `natMul`,
`natDivModChecked`, `intNeg`, `intCmp`, `intAdd`, `intSub`, `intMul`, `intTDivModChecked`,
`intEDivModChecked`, `intToText`, `intOfText`, and the text exports `textNeg`, `textCmp`,
`textAdd`, `textSub`, `textMul`, `textTDiv`, `textTMod`, `textEDiv`, and `textEMod`, one for each
integer operation, with no parser of expressions.  The divisions
of Lean's convention, `natDivMod`, `intTDivMod`, and `intEDivMod`, are library functions that the
module compiles into its exports without exporting them.  The module also exports the functions of
MultiPrecision, Uscale, and Int64Text that these call, since leanexe's compiler exports every
function that it compiles; those are not part of this library's interface.

A division export returns the status 0 with the quotient and the remainder, or the status 1 with
two zeros when the divisor is 0.  A text export reads its operands with the grammar above and
returns a status with a result: 0 with the result, 1 when the first operand is not a text of the
grammar, 2 when the second is not, and 3 when the operation is a division and the divisor is 0.
With a status other than 0, the text result is empty and the word result is 0.  The first operand
is read and judged before the second.  `intOfText` keeps the flag of `readSpec`, `true` for an
accepted text, where the other exports return the status 0 for success.  A call that finds no
memory for an allocation ends at a trap with no status; the call theorems exclude the trap when
the memory has room for the export's allocation bound.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision (value Digits base)
open Library.Numerics.Decimal.Shared.StrconvGrammar (words ascii)

/-! ## Naturals -/

/-- The canonical limbs of `n`: its base-`2^32` digits, least significant first. -/
def limbsOf (n : ℕ) : Array UInt64 := ((Nat.digits base n).map UInt64.ofNat).toArray

/-- Limbs below the base with no zero limb at the top. -/
def Canonical (u : Array UInt64) : Prop := Digits u ∧ ∀ h : 0 < u.size, u[u.size - 1] ≠ 0

/-- 0, 1, or 2 when `a` is less than, equal to, or greater than `b`. -/
def cmpSpec {α : Type} [LinearOrder α] (a b : α) : UInt64 :=
  if a < b then 0 else if a = b then 1 else 2

/-- The flag `a < b` and the canonical limbs of `|a - b|`. -/
def natSubSpec (a b : ℕ) : Bool × Array UInt64 :=
  (decide (a < b), limbsOf ((a : ℤ) - b).natAbs)

/-- The canonical limbs of the quotient and the remainder, with `a / 0 = 0` and `a % 0 = a`. -/
def natDivModSpec (a b : ℕ) : Array UInt64 × Array UInt64 := (limbsOf (a / b), limbsOf (a % b))

/-! ## Integers -/

/-- The canonical integer of `z`. -/
def BigInt.ofInt (z : ℤ) : BigInt := ⟨decide (z < 0), limbsOf z.natAbs⟩

/-- The integer that a sign and a magnitude denote. -/
def BigInt.toInt (x : BigInt) : ℤ := if x.neg then -(value x.mag : ℤ) else value x.mag

/-- A canonical integer is the canonical form of the integer it denotes. -/
def BigInt.Canonical (x : BigInt) : Prop := x = .ofInt x.toInt

/-- The truncated quotient and remainder, with `x.tdiv 0 = 0` and `x.tmod 0 = x`. -/
def intTDivModSpec (a b : ℤ) : BigInt × BigInt := (.ofInt (a.tdiv b), .ofInt (a.tmod b))

/-- Lean's Euclidean quotient and remainder, with `x / 0 = 0` and `x % 0 = x`. -/
def intEDivModSpec (a b : ℤ) : BigInt × BigInt := (.ofInt (a / b), .ofInt (a % b))

/-! ## Text -/

/-- Lean's decimal text of `z`, one byte to a word. -/
def printSpec (z : ℤ) : Array UInt64 := words (ascii (toString z))

/-- The integer of a text of `Int64Text`'s grammar, without its range test. -/
def readSpec (s : Array UInt64) : Bool × BigInt :=
  match Library.Numerics.Decimal.Int64Text.denote s.toList with
  | some z => (true, .ofInt z)
  | none => (false, .ofInt 0)

/-! ## Exports -/

/-- The export of natural division: the status 1 and two zeros for a zero divisor, and otherwise
the status 0, the quotient, and the remainder. -/
def natDivModCheckedSpec (a b : ℕ) : UInt64 × Array UInt64 × Array UInt64 :=
  if b = 0 then (1, limbsOf 0, limbsOf 0) else (0, limbsOf (a / b), limbsOf (a % b))

/-- The export of truncated division, with the statuses of `natDivModCheckedSpec`. -/
def intTDivModCheckedSpec (a b : ℤ) : UInt64 × BigInt × BigInt :=
  if b = 0 then (1, .ofInt 0, .ofInt 0) else (0, .ofInt (a.tdiv b), .ofInt (a.tmod b))

/-- The export of Euclidean division, with the statuses of `natDivModCheckedSpec`. -/
def intEDivModCheckedSpec (a b : ℤ) : UInt64 × BigInt × BigInt :=
  if b = 0 then (1, .ofInt 0, .ofInt 0) else (0, .ofInt (a / b), .ofInt (a % b))

/-- A unary text export: the status 0 and the text of `f z` for a text of `z`, and the status 1
and the empty text otherwise. -/
def textUnary (f : ℤ → ℤ) (s : Array UInt64) : UInt64 × Array UInt64 :=
  match Library.Numerics.Decimal.Int64Text.denote s.toList with
  | some a => (0, printSpec (f a))
  | none => (1, #[])

/-- A binary text export: the status 1 or 2 and the empty text when the first or the second
operand is not a text of the grammar, the status 3 and the empty text when `division` holds and
the divisor is 0, and otherwise the status 0 and the text of `f a b`. -/
def textBinary (division : Bool) (f : ℤ → ℤ → ℤ) (s t : Array UInt64) :
    UInt64 × Array UInt64 :=
  match Library.Numerics.Decimal.Int64Text.denote s.toList with
  | none => (1, #[])
  | some a =>
    match Library.Numerics.Decimal.Int64Text.denote t.toList with
    | none => (2, #[])
    | some b => if division = true ∧ b = 0 then (3, #[]) else (0, printSpec (f a b))

/-- The text export of comparison: the status of `textBinary` and the code of `cmpSpec`, or 0
with a status other than 0. -/
def textCmpSpec (s t : Array UInt64) : UInt64 × UInt64 :=
  match Library.Numerics.Decimal.Int64Text.denote s.toList with
  | none => (1, 0)
  | some a =>
    match Library.Numerics.Decimal.Int64Text.denote t.toList with
    | none => (2, 0)
    | some b => (0, cmpSpec a b)

def textNegSpec : Array UInt64 → UInt64 × Array UInt64 := textUnary fun a => -a
def textAddSpec : Array UInt64 → Array UInt64 → UInt64 × Array UInt64 := textBinary false (· + ·)
def textSubSpec : Array UInt64 → Array UInt64 → UInt64 × Array UInt64 := textBinary false (· - ·)
def textMulSpec : Array UInt64 → Array UInt64 → UInt64 × Array UInt64 := textBinary false (· * ·)
def textTDivSpec : Array UInt64 → Array UInt64 → UInt64 × Array UInt64 := textBinary true Int.tdiv
def textTModSpec : Array UInt64 → Array UInt64 → UInt64 × Array UInt64 := textBinary true Int.tmod
def textEDivSpec : Array UInt64 → Array UInt64 → UInt64 × Array UInt64 := textBinary true (· / ·)
def textEModSpec : Array UInt64 → Array UInt64 → UInt64 × Array UInt64 := textBinary true (· % ·)

end Library.Numerics.Bignum
