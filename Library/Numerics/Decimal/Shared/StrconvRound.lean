import Library.Numerics.Decimal.Shared.StrconvGrammar
import Library.Numerics.Decimal.Shared.StrconvBinary32
import LeanExe.ProofKit.F64PositiveRounding

/-!
The meaning of a number for binary64 and binary32, and the definition of the shortest decimal.
`round64 n` is the binary64 word of roundTiesToEven applied to the value of `n`: the nearest-even
rounding of the magnitude, `F64PositiveRounding.roundNearestEven`, with positive infinity from
`2 ^ 1024 - 2 ^ 970` on, and the sign applied afterwards, so that a negative number that rounds to
zero gives `-0` and `-0` itself gives `-0`.  An infinity keeps its sign, and every NaN gives the
canonical NaN `0x7FF8000000000000`.  `round32` is the same for binary32 with
`StrconvBinary32.roundNearestEven` and the canonical NaN `0x7FC00000`.

`Shortest64 w neg d e` states that the decimal `(-1)^neg · d · 10^e` rounds to `w` and comes first
among all such decimals in the order of the definition that the printers prove: the fewest
significant digits, then the nearest to the value of `w`, then an even last digit.  This is the
definition of ECMA-262's Number::toString with its Note 2 and of Schubfach's Figure 1, and it
differs from Java's `Double.toString`, which requires at least two digits.  `sciLayout` and
`ecmaLayout` are the two output layouts, the second transcribing steps 5 to 12 of ECMA-262's
Number::toString (6.1.6.1.20).
-/

namespace Library.Numerics.Decimal.Shared.StrconvRound
open StrconvGrammar LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- The real value of a finite number; 0 for an infinity or NaN. -/
noncomputable def Num.toReal : Num → ℝ
  | .dec neg d e => (if neg then -1 else 1) * d * (10 : ℝ) ^ e
  | .hex neg d e => (if neg then -1 else 1) * d * (2 : ℝ) ^ e
  | _ => 0

def withSign64 (neg : Bool) (w : UInt64) : UInt64 := if neg then Wasm.IEEE64.negate w else w

def withSign32 (neg : Bool) (w : UInt32) : UInt32 := if neg then Wasm.IEEE32.negate w else w

/-- The binary64 word of roundTiesToEven applied to a number. -/
noncomputable def round64 : Num → UInt64
  | .dec neg d e => withSign64 neg (F64PositiveRounding.roundNearestEven (d * (10 : ℝ) ^ e))
  | .hex neg d e => withSign64 neg (F64PositiveRounding.roundNearestEven (d * (2 : ℝ) ^ e))
  | .inf neg => withSign64 neg 0x7FF0000000000000
  | .nan => 0x7FF8000000000000

/-- The binary32 word of roundTiesToEven applied to a number. -/
noncomputable def round32 : Num → UInt32
  | .dec neg d e => withSign32 neg (StrconvBinary32.roundNearestEven (d * (10 : ℝ) ^ e))
  | .hex neg d e => withSign32 neg (StrconvBinary32.roundNearestEven (d * (2 : ℝ) ^ e))
  | .inf neg => withSign32 neg 0x7F800000
  | .nan => 0x7FC00000

/-- A word with every NaN replaced by the canonical NaN. -/
def canon64 (w : UInt64) : UInt64 := if Wasm.IEEE64.isNaN w then 0x7FF8000000000000 else w

def canon32 (w : UInt32) : UInt32 := if Wasm.IEEE32.isNaN w then 0x7FC00000 else w

/-- `d` divided by 10 while it is a nonzero multiple of 10, at most `k` times. -/
def stripZerosFuel : Nat → Nat → Nat
  | 0, d => d
  | k + 1, d => if d ≠ 0 ∧ d % 10 = 0 then stripZerosFuel k (d / 10) else d

/-- `d` without its trailing decimal zeros; 0 for 0.  A nonzero `d` has fewer than `d` trailing
zeros, so the fuel `d` suffices. -/
def stripZeros (d : Nat) : Nat := stripZerosFuel d d

/-- The number of significant decimal digits of `d`; 0 for 0. -/
def sigDigits (d : Nat) : Nat := (Nat.digits 10 (stripZeros d)).length

/-- `(-1)^neg · d · 10^e` rounds to `w` and has the fewest significant digits among the decimals
that round to `w`, the least distance from the value of `w` among those with as many digits, and,
at an equal distance from a different decimal with as many digits, an even last digit. -/
def Shortest64 (w : UInt64) (neg : Bool) (d : Nat) (e : Int) : Prop :=
  round64 (.dec neg d e) = w ∧
  ∀ neg' d' e', round64 (.dec neg' d' e') = w →
    sigDigits d < sigDigits d' ∨
    (sigDigits d = sigDigits d' ∧
      (|Num.toReal (.dec neg d e) - CodeLib.IEEE64.value w| <
          |Num.toReal (.dec neg' d' e') - CodeLib.IEEE64.value w| ∨
       (|Num.toReal (.dec neg d e) - CodeLib.IEEE64.value w| =
          |Num.toReal (.dec neg' d' e') - CodeLib.IEEE64.value w| ∧
        (Num.toReal (.dec neg d e) = Num.toReal (.dec neg' d' e') ∨ stripZeros d % 2 = 0))))

/-- The binary32 counterpart of `Shortest64`. -/
def Shortest32 (w : UInt32) (neg : Bool) (d : Nat) (e : Int) : Prop :=
  round32 (.dec neg d e) = w ∧
  ∀ neg' d' e', round32 (.dec neg' d' e') = w →
    sigDigits d < sigDigits d' ∨
    (sigDigits d = sigDigits d' ∧
      (|Num.toReal (.dec neg d e) - CodeLib.IEEE32.value w| <
          |Num.toReal (.dec neg' d' e') - CodeLib.IEEE32.value w| ∨
       (|Num.toReal (.dec neg d e) - CodeLib.IEEE32.value w| =
          |Num.toReal (.dec neg' d' e') - CodeLib.IEEE32.value w| ∧
        (Num.toReal (.dec neg d e) = Num.toReal (.dec neg' d' e') ∨ stripZeros d % 2 = 0))))

/-- The decimal digits of `t`, most significant first; `0` for 0. -/
def digitsOf (t : Nat) : List UInt8 := (Nat.toDigits 10 t).map Char.toUInt8

/-- The scientific layout of `(-1)^neg · t · 10^k`: the digits of `t` with a point after the
first when there are several, `e`, and the exponent of the first digit, with `-` when it is
negative. -/
def sciLayout (neg : Bool) (t : Nat) (k : Int) : List UInt8 :=
  let ds := digitsOf t
  let x : Int := k + ds.length - 1
  (if neg then ascii "-" else []) ++ ds.take 1 ++
    (if ds.length = 1 then [] else ascii "." ++ ds.drop 1) ++ ascii "e" ++
    (if x < 0 then ascii "-" else []) ++ digitsOf x.natAbs

/-- The layout of ECMA-262's Number::toString for `(-1)^neg · t · 10^k` with `t` not divisible
by 10, steps 5 to 12 of 6.1.6.1.20: `n` is the position of the decimal point relative to the first
digit, plain notation for `n` from -5 to 21, and otherwise an exponent with `+` or `-`.  ECMA-262
prints negative zero as `0`; the printers print `-0` instead. -/
def ecmaLayout (neg : Bool) (t : Nat) (k : Int) : List UInt8 :=
  let ds := digitsOf t
  let len : Int := ds.length
  let n := k + len
  (if neg then ascii "-" else []) ++
    (if len ≤ n ∧ n ≤ 21 then ds ++ List.replicate (n - len).toNat 0x30
     else if 0 < n ∧ n ≤ 21 then ds.take n.toNat ++ ascii "." ++ ds.drop n.toNat
     else if -6 < n ∧ n ≤ 0 then ascii "0." ++ List.replicate (-n).toNat 0x30 ++ ds
     else ds.take 1 ++ (if ds.length = 1 then [] else ascii "." ++ ds.drop 1) ++ ascii "e" ++
       (if 0 ≤ n - 1 then ascii "+" else ascii "-") ++ digitsOf (n - 1).natAbs)

example : sciLayout false 15 2 = ascii "1.5e3" := by decide
example : sciLayout true 5 (-324) = ascii "-5e-324" := by decide
example : ecmaLayout false 15 2 = ascii "1500" := by decide
example : ecmaLayout false 15 20 = ascii "1.5e+21" := by decide
example : ecmaLayout false 1 (-6) = ascii "0.000001" := by decide
example : ecmaLayout false 1 (-7) = ascii "1e-7" := by decide
example : ecmaLayout false 125 (-2) = ascii "1.25" := by decide
example : stripZeros 1500 = 15 ∧ sigDigits 1500 = 2 ∧ sigDigits 0 = 0 := by decide

end Library.Numerics.Decimal.Shared.StrconvRound
