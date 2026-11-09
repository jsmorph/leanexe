import Library.Numerics.Decimal.Shared.StrconvGrammar

/-!
The specification of the decimal printer and reader of `Int64`.  A text is an array of words that
hold one byte each, `StrconvGrammar.words`, as the decimal parsers and printers of the library take
and return their strings.

`expectedPrint x` is the text of `toString x`, Lean's decimal form of the integer `x.toInt`: the
digits of its magnitude with no leading zero, `0` for zero, and `-` before the digits of a negative
value, so `Int64.minValue` prints as `-9223372036854775808`.

`expectedRead s` accepts the texts of the grammar

```
integer = "0" / [ "-" ] nonzero *digit
nonzero = "1" / "2" / "3" / "4" / "5" / "6" / "7" / "8" / "9"
digit   = "0" / nonzero
```

whose integer lies in [-2^63, 2^63 - 1], and returns `(true, x)` with `x` the `Int64` of that
integer.  It returns `(false, 0)` for every other array of words, among them the empty array, a
lone `-`, a sign out of place, a byte outside the grammar's alphabet anywhere, a word above 255,
which holds no byte, and a text of the grammar whose integer lies outside that range.  The grammar
settles the cases that the request leaves open as follows.

- A leading `+` is rejected.  The printer never writes one, and a second text for every
  nonnegative value would end the correspondence between values and texts.
- A leading zero is rejected, except in the text `0` itself.  `007` would be a second text of 7.
- `-0` is rejected.  `Int64` has one zero, so `-0` would be a second text of 0.  RFC 8259's
  `[ minus ] int` admits `-0`, and the library's binary64 parser reads it as negative zero, a value
  distinct from zero, which `Int64` lacks.
- The reader takes the whole array and no white space, as the library's parsers do.

The grammar is RFC 8259's `[ minus ] int` without `-0`, and each `Int64` value has exactly one text
in it, the printer's.  A pair of a flag and a value reports rejection because the verified
compiler's dialect has no `Option`: the flag is a `Bool`, which the module passes as the word 1 or
0, and the value of a rejected text is 0, as the library's parsers return `(false, 0)` for a
rejected string.
-/

namespace Library.Numerics.Decimal.Int64Text

open Library.Numerics.Decimal.Shared.StrconvGrammar

/-- The text of `x`: the bytes of Lean's `toString x`, which is `toString x.toInt`, one byte to a
word. -/
def expectedPrint (x : Int64) : Array UInt64 := words (ascii (toString x))

/-- Word `w` holds the byte of a decimal digit, `0` (48) to `9` (57). -/
def isDigitWord (w : UInt64) : Bool := 48 ≤ w && w ≤ 57

/-- The value of decimal digits, most significant first. -/
def digitsValue (ds : List UInt64) : Nat := ds.foldl (fun v d => 10 * v + (d.toNat - 48)) 0

/-- The value of `nonzero *digit`: `ds` is a digit from 1 to 9 followed by digits. -/
def magnitude (ds : List UInt64) : Option Nat :=
  match ds with
  | [] => none
  | d :: rest => if 49 ≤ d && d ≤ 57 && rest.all isDigitWord then some (digitsValue ds) else none

/-- The integer that the words `s` denote in the grammar `integer`, or `none` when `s` is not a
text of the grammar. -/
def denote (s : List UInt64) : Option Int :=
  if s = [48] then some 0
  else if s.head? = some 45 then (magnitude s.tail).map fun n => -(n : Int)
  else (magnitude s).map fun n => (n : Int)

/-- The reader's result: `(true, x)` for a text of the grammar whose integer `x.toInt` lies in the
range of `Int64`, and `(false, 0)` for every other array. -/
def expectedRead (s : Array UInt64) : Bool × Int64 :=
  match denote s.toList with
  | some n => if -2 ^ 63 ≤ n ∧ n < 2 ^ 63 then (true, Int64.ofInt n) else (false, 0)
  | none => (false, 0)

end Library.Numerics.Decimal.Int64Text
