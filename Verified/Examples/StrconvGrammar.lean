import Mathlib.Data.List.Basic

/-!
The grammar of number strings that `ParseFloat` reads, as an inductive relation with one
constructor per production.  `Derives general s n` states that the bytes `s` form a number of the
grammar selected by `general` and denote `n`.  With `general` false the grammar is the `number` of
RFC 8259, section 6:

```
number = [ minus ] int [ frac ] [ exp ]
int    = zero / ( digit1-9 *DIGIT )
frac   = decimal-point 1*DIGIT
exp    = e [ minus / plus ] 1*DIGIT
```

With `general` true it is a superset in the style of C's `strtod`, without white space, NaN
payloads, or a longest-prefix rule: an optional `+` or `-`, a decimal significand
`1*DIGIT [ "." *DIGIT ] / "." 1*DIGIT` with leading zeros allowed and an optional exponent, a
hexadecimal significand after `0x` or `0X` with a required binary exponent `p` or `P` of decimal
digits, or `inf`, `infinity`, or `nan` in any case.  The whole input must match.  A decimal
denotes `.dec neg d e`, the digits of its integer and fraction parts read as one integer `d`, with
the exponent `e` reduced by the number of fraction digits, so `1.0` denotes `.dec false 10 (-1)`;
a hexadecimal significand reduces its binary exponent by four per fraction digit.
-/

namespace Verified.Examples.StrconvGrammar

/-- What a number string denotes: `(-1)^neg · d · 10^e`, `(-1)^neg · d · 2^e`, an infinity, or
NaN. -/
inductive Num where
  | dec (neg : Bool) (d : Nat) (e : Int)
  | hex (neg : Bool) (d : Nat) (e : Int)
  | inf (neg : Bool)
  | nan
  deriving DecidableEq, Repr

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List UInt8 := s.toList.map Char.toUInt8

/-- The bytes `s` as an array of words, one byte per word. -/
def words (s : List UInt8) : Array UInt64 := (s.map UInt8.toUInt64).toArray

def isDigit (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39

def isHexDigit (b : UInt8) : Bool :=
  isDigit b || (0x41 ≤ b && b ≤ 0x46) || (0x61 ≤ b && b ≤ 0x66)

/-- The value of a hexadecimal digit; `b % 32 + 9` maps both `A` and `a` to 10. -/
def hexDigitValue (b : UInt8) : Nat := if isDigit b then b.toNat - 0x30 else b.toNat % 32 + 9

/-- The value of a string of decimal digits, 0 for the empty string. -/
def decValue (ds : List UInt8) : Nat := ds.foldl (fun v b => 10 * v + (b.toNat - 0x30)) 0

/-- The value of a string of hexadecimal digits, 0 for the empty string. -/
def hexValue (ds : List UInt8) : Nat := ds.foldl (fun v b => 16 * v + hexDigitValue b) 0

/-- An ASCII letter in lower case; every other byte unchanged. -/
def lower (b : UInt8) : UInt8 := if 0x41 ≤ b && b ≤ 0x5A then b + 0x20 else b

/-- The sign of a number and whether it is negative: nothing or `-`, and also `+` in the general
grammar. -/
inductive Sign : Bool → List UInt8 → Bool → Prop
  | none (general : Bool) : Sign general [] false
  | minus (general : Bool) : Sign general (ascii "-") true
  | plus : Sign true (ascii "+") false

/-- RFC 8259 `int = zero / ( digit1-9 *DIGIT )`. -/
inductive JsonInt : List UInt8 → Prop
  | zero : JsonInt (ascii "0")
  | nonzero (c : UInt8) (ds : List UInt8) :
      0x31 ≤ c → c ≤ 0x39 → (∀ b ∈ ds, isDigit b) → JsonInt (c :: ds)

/-- RFC 8259 `[ frac ]`, `frac = decimal-point 1*DIGIT`, with its digits. -/
inductive JsonFrac : List UInt8 → List UInt8 → Prop
  | none : JsonFrac [] []
  | some (f : List UInt8) : f ≠ [] → (∀ b ∈ f, isDigit b) → JsonFrac (ascii "." ++ f) f

/-- A significand of the general grammar, `1*D [ "." *D ] / "." 1*D` for digits `D` of the class
`digit`, with its integer digits and its fraction digits. -/
inductive Significand (digit : UInt8 → Bool) : List UInt8 → List UInt8 → List UInt8 → Prop
  | int (i : List UInt8) : i ≠ [] → (∀ b ∈ i, digit b) → Significand digit i i []
  | point (i f : List UInt8) : i ++ f ≠ [] → (∀ b ∈ i ++ f, digit b) →
      Significand digit (i ++ ascii "." ++ f) i f

/-- An exponent `m [ "+" / "-" ] 1*DIGIT` with a marker byte `m` from `markers`, and its
value. -/
inductive Exponent (markers : List UInt8) : List UInt8 → Int → Prop
  | plain (m : UInt8) (ds : List UInt8) : m ∈ markers → ds ≠ [] → (∀ b ∈ ds, isDigit b) →
      Exponent markers (m :: ds) (decValue ds)
  | plus (m : UInt8) (ds : List UInt8) : m ∈ markers → ds ≠ [] → (∀ b ∈ ds, isDigit b) →
      Exponent markers (m :: (ascii "+" ++ ds)) (decValue ds)
  | minus (m : UInt8) (ds : List UInt8) : m ∈ markers → ds ≠ [] → (∀ b ∈ ds, isDigit b) →
      Exponent markers (m :: (ascii "-" ++ ds)) (-(decValue ds : Int))

/-- An optional exponent, 0 when absent. -/
inductive OptExponent (markers : List UInt8) : List UInt8 → Int → Prop
  | none : OptExponent markers [] 0
  | some (x : List UInt8) (e : Int) : Exponent markers x e → OptExponent markers x e

/-- `Derives general s n`: the bytes `s` form a number of the grammar selected by `general` and
denote `n`.  The general grammar's decimals include every RFC 8259 number (`derives_general`). -/
inductive Derives : Bool → List UInt8 → Num → Prop
  | json (sg i fr f x : List UInt8) (neg : Bool) (e : Int) :
      Sign false sg neg → JsonInt i → JsonFrac fr f → OptExponent (ascii "eE") x e →
      Derives false (sg ++ i ++ fr ++ x) (.dec neg (decValue (i ++ f)) (e - f.length))
  | decimal (sg m i f x : List UInt8) (neg : Bool) (e : Int) :
      Sign true sg neg → Significand isDigit m i f → OptExponent (ascii "eE") x e →
      Derives true (sg ++ m ++ x) (.dec neg (decValue (i ++ f)) (e - f.length))
  | hex (sg z m i f x : List UInt8) (neg : Bool) (e : Int) :
      Sign true sg neg → z ∈ [ascii "0x", ascii "0X"] → Significand isHexDigit m i f →
      Exponent (ascii "pP") x e →
      Derives true (sg ++ z ++ m ++ x) (.hex neg (hexValue (i ++ f)) (e - 4 * f.length))
  | inf (sg w : List UInt8) (neg : Bool) :
      Sign true sg neg → w.map lower ∈ [ascii "inf", ascii "infinity"] →
      Derives true (sg ++ w) (.inf neg)
  | nan (sg w : List UInt8) (neg : Bool) :
      Sign true sg neg → w.map lower = ascii "nan" → Derives true (sg ++ w) .nan

theorem ascii_minus : ascii "-" = [0x2D] := rfl
theorem ascii_plus : ascii "+" = [0x2B] := rfl
theorem ascii_point : ascii "." = [0x2E] := rfl
theorem ascii_zero : ascii "0" = [0x30] := rfl
theorem ascii_eE : ascii "eE" = [0x65, 0x45] := rfl
theorem ascii_pP : ascii "pP" = [0x70, 0x50] := rfl
theorem ascii_0x : ascii "0x" = [0x30, 0x78] := rfl
theorem ascii_0X : ascii "0X" = [0x30, 0x58] := rfl
theorem ascii_inf : ascii "inf" = [0x69, 0x6E, 0x66] := rfl
theorem ascii_infinity : ascii "infinity" = [0x69, 0x6E, 0x66, 0x69, 0x6E, 0x69, 0x74, 0x79] := rfl
theorem ascii_nan : ascii "nan" = [0x6E, 0x61, 0x6E] := rfl

example : Derives false (ascii "-1.25e+3") (.dec true 125 1) := by
  have h := Derives.json (ascii "-") (ascii "1") (ascii ".25") (ascii "25") (ascii "e+3") true 3
    (Sign.minus false) (JsonInt.nonzero 0x31 [] (by decide) (by decide) (by simp))
    (JsonFrac.some (ascii "25") (by decide) (by decide))
    (OptExponent.some _ _ (Exponent.plus 0x65 (ascii "3") (by decide) (by decide) (by decide)))
  exact h

end Verified.Examples.StrconvGrammar
