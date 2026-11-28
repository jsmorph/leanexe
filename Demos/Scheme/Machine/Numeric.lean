module

public import Demos.Scheme.Machine.Text

@[expose] public section

/-! The numeric layer of the executable interpreter.  Every numeric procedure and the reading of
numerals pass through this module, whose words are fixnums: the word of `8 n` for an integer `n`
from `-2^60` to `2^60 - 1`.  A later layer of integers of any size replaces these functions and
allocates objects of the reserved kind `K_BIGNUM`, and no caller changes.

An operation computes over `Int64`, whose 63 bits hold every sum and difference of two fixnums,
and checks the profile's range at its result.  A sum of many arguments keeps a two-word
accumulator, so a sum in the range is exact when a partial sum is not.  A product checks each step
for overflow by division and, after an overflow, returns 0 when a later factor is 0, since the
magnitude of a product of nonzero integers never decreases. -/

namespace Demos.Scheme.Machine.Numeric

open Demos.Scheme.Machine

/-- `2^60`, the magnitude of the least fixnum. -/
def LIMIT : UInt64 := 1152921504606846976

@[inline] def inRange (n : Int64) : Bool := -1152921504606846976 ≤ n && n ≤ 1152921504606846975

/-- The fixnum of an integer in `Int64`, or the restriction's status. -/
@[inline] def ofInt (n : Int64) : UInt64 × UInt64 :=
  if inRange n then (0, mkFix n) else (S_RESTRICTION + M_RANGE, 0)

/-! ## Numerals (§6.5.4) -/

/-- The value of the numeral from `p` to `e` of the source: the status 0 and a fixnum, the
restriction's status for a numeral outside the profile, or the read error of an invalid token,
whose offset is `p`.  The prefixes, the digits, and the bytes of numerals follow the reference
reader's `readNumeral`. -/
def readNumeral (src : LeanExe.Bytes) (p e : UInt64) : UInt64 × UInt64 :=
  -- prefixes: (offset, radix or 0, exactness: 0 none, 1 #e, 2 #i, bad)
  let pre := LeanExe.repeatWhile 4 (p, (0 : UInt64), (0 : UInt64), false)
    (fun s => !s.2.2.2 && s.1 + 1 < e && src.get s.1 == 35)
    fun s =>
      let k := foldByte (src.get (s.1 + 1))
      if k == 98 || k == 111 || k == 100 || k == 120 then
        if s.2.1 != 0 then (s.1, s.2.1, s.2.2.1, true)
        else (s.1 + 2, (if k == 98 then 2 else if k == 111 then 8 else if k == 100 then 10
          else 16), s.2.2.1, false)
      else if k == 101 || k == 105 then
        if s.2.2.1 != 0 then (s.1, s.2.1, s.2.2.1, true)
        else (s.1 + 2, s.2.1, (if k == 101 then 1 else 2), false)
      else (s.1, s.2.1, s.2.2.1, true)
  let q := pre.1
  let r := if pre.2.1 == 0 then 10 else pre.2.1
  let ex := pre.2.2.1
  let invalid : UInt64 × UInt64 := (S_READ + M_TOKEN, p)
  if pre.2.2.2 || q ≥ e then invalid
  else
    let c := src.get q
    let neg := c == 45
    let s := if c == 43 || c == 45 then q + 1 else q
    let digits := s < e && LeanExe.repeatWhile src.size s
      (fun i => i < e && digitValueB (src.get i) < r) (fun i => i + 1) == e
    if digits then
      if ex == 2 then (S_RESTRICTION + M_NUMBER, 0)
      else
        let mag := LeanExe.repeatWhile src.size (s, (0 : UInt64)) (fun st => st.1 < e)
          (fun st =>
            (st.1 + 1, if st.2 > LIMIT / r then LIMIT + LIMIT
              else st.2 * r + digitValueB (src.get st.1))) |>.2
        if neg then
          if mag ≤ LIMIT then (0, mkFix (0 - mag.toInt64)) else (S_RESTRICTION + M_RANGE, 0)
        else if mag < LIMIT then (0, mkFix mag.toInt64) else (S_RESTRICTION + M_RANGE, 0)
    else if allNumeral src r q e then (S_RESTRICTION + M_NUMBER, 0)
    else invalid

end Demos.Scheme.Machine.Numeric

namespace Demos.Scheme.Machine.Numeric

open Demos.Scheme.Machine

/-! ## Operations (§6.5.5)

The arguments are the list `args` of the machine, last first, with `nargs` elements, which the
evaluator checked against the procedure's arity. -/

/-- Whether every element of a list is a number. -/
def allNumbers (heap : Array Slot) (l : UInt64) : Bool :=
  LeanExe.repeatWhile 16777216 l (fun l => isPair heap l && isFix (fa heap l)) (fun l => fb heap l)
    == NILV

/-- Whether the chained comparison holds over the arguments, `rel b a` for each argument `a` and
the argument `b` after it, read from the list whose last argument is first. -/
def chainHolds (heap : Array Slot) (l : UInt64) (op : UInt64) : Bool :=
  (LeanExe.repeatWhile 16777216 (l, true) (fun s => s.2 && isPair heap s.1 && isPair heap (fb heap s.1))
    fun s =>
      let b := fixVal (fa heap s.1)
      let a := fixVal (fa heap (fb heap s.1))
      let ok := if op == N_EQ then a == b else if op == N_LT then a < b
        else if op == N_GT then a > b else if op == N_LE then a ≤ b else a ≥ b
      (fb heap s.1, ok)).2

/-- The magnitude of an `Int64` as a word. -/
@[inline] def mag (a : Int64) : UInt64 := if a < 0 then (0 - a).toUInt64 else a.toUInt64

/-- The greatest common divisor of two words, by Euclid's algorithm. -/
def gcdWord (a b : UInt64) : UInt64 :=
  (LeanExe.repeatWhile 128 (a, b) (fun s => s.2 != 0) fun s => (s.2, s.1 % s.2)).1

/-- The sum of the arguments, exact through a two-word accumulator: `hi · 2^61 + lo` with
`0 ≤ lo < 2^61`. -/
def sum (heap : Array Slot) (l : UInt64) : UInt64 × UInt64 :=
  let st := LeanExe.repeatWhile 16777216 (l, (0 : Int64), (0 : Int64)) (fun s => isPair heap s.1)
    fun s =>
      let lo := s.2.2 + fixVal (fa heap s.1)
      if lo < 0 then (fb heap s.1, s.2.1 - 1, lo + 2305843009213693952)
      else if lo ≥ 2305843009213693952 then (fb heap s.1, s.2.1 + 1, lo - 2305843009213693952)
      else (fb heap s.1, s.2.1, lo)
  let hi := st.2.1
  let lo := st.2.2
  if hi == 0 && lo ≤ 1152921504606846975 then (0, mkFix lo)
  else if hi == -1 && lo ≥ 1152921504606846976 then (0, mkFix (lo - 2305843009213693952))
  else (S_RESTRICTION + M_RANGE, 0)

/-- The product of the arguments: 0 when one is 0, and otherwise exact or the restriction, since
the magnitude of a product of nonzero integers never decreases. -/
def product (heap : Array Slot) (l : UInt64) : UInt64 × UInt64 :=
  let zero := LeanExe.repeatWhile 16777216 l (fun l => isPair heap l && fa heap l != mkFix 0)
    (fun l => fb heap l) != NILV
  if zero then (0, mkFix 0)
  else
    let st := LeanExe.repeatWhile 16777216 (l, (1 : Int64), false)
      (fun s => !s.2.2 && isPair heap s.1)
      fun s =>
        let x := fixVal (fa heap s.1)
        let p := s.2.1
        if mag p > 9223372036854775807 / mag x then (fb heap s.1, p, true)
        else
          let q := p * x
          (fb heap s.1, q, !inRange q)
    if st.2.2 then (S_RESTRICTION + M_RANGE, 0) else (0, mkFix st.2.1)

/-- `n1 / n2` of exact integers: the quotient when it is an integer, a division by zero, or the
restriction for a quotient that is no integer. -/
def divide (a b : Int64) : UInt64 × UInt64 :=
  if b == 0 then (S_ERROR + M_DIVZERO, 0)
  else if a % b == 0 then ofInt (a / b)
  else (S_RESTRICTION + M_NOTINT, 0)

/-- The numeric procedure with code `op` on the machine's arguments: the status 0 and the result's
word, or an outcome's status. -/
def compute (heap : Array Slot) (op args nargs : UInt64) : UInt64 × UInt64 :=
  if op ≤ N_ISINTEGER then (0, boolV (isFix (fa heap args)))
  else if !allNumbers heap args then (S_ERROR + M_TYPE, 0)
  else
    let rest := if isPair heap args then fb heap args else NILV
    let a := if isPair heap args then fixVal (fa heap args) else 0
    let b := if isPair heap rest then fixVal (fa heap rest) else 0
    -- `a` is the last argument and `b` the one before it
    if op == N_ISEXACT then (0, TRUE)
    else if op == N_ISINEXACT then (0, FALSE)
    else if op ≤ N_GE then (0, boolV (chainHolds heap args op))
    else if op == N_ISZERO then (0, boolV (a == 0))
    else if op == N_ISPOSITIVE then (0, boolV (a > 0))
    else if op == N_ISNEGATIVE then (0, boolV (a < 0))
    else if op == N_ISODD then (0, boolV (a % 2 != 0))
    else if op == N_ISEVEN then (0, boolV (a % 2 == 0))
    else if op == N_MAX || op == N_MIN then
      (0, mkFix (LeanExe.repeatWhile 16777216 (fb heap args, a) (fun s => isPair heap s.1)
        (fun s =>
          let x := fixVal (fa heap s.1)
          (fb heap s.1, if op == N_MAX then (if x > s.2 then x else s.2)
            else if x < s.2 then x else s.2))).2)
    else if op == N_ADD then sum heap args
    else if op == N_MUL then product heap args
    else if op == N_SUB then if nargs == 1 then ofInt (0 - a) else ofInt (b - a)
    else if op == N_DIV then if nargs == 1 then divide 1 a else divide b a
    else if op == N_ABS then ofInt (if a < 0 then 0 - a else a)
    else if op == N_QUOTIENT then if a == 0 then (S_ERROR + M_DIVZERO, 0) else ofInt (b / a)
    else if op == N_REMAINDER then if a == 0 then (S_ERROR + M_DIVZERO, 0) else ofInt (b % a)
    else if op == N_MODULO then
      if a == 0 then (S_ERROR + M_DIVZERO, 0)
      else
        let r := b % a
        ofInt (if r != 0 && (r < 0) != (a < 0) then r + a else r)
    else if op == N_GCD then
      let g := LeanExe.repeatWhile 16777216 (args, (0 : UInt64)) (fun s => isPair heap s.1)
        (fun s => (fb heap s.1, gcdWord s.2 (mag (fixVal (fa heap s.1))))) |>.2
      if g ≤ 1152921504606846975 then (0, mkFix g.toInt64) else (S_RESTRICTION + M_RANGE, 0)
    else if op == N_LCM then
      let r := LeanExe.repeatWhile 16777216 (args, (1 : UInt64), false)
        (fun s => isPair heap s.1)
        (fun s =>
          let x := mag (fixVal (fa heap s.1))
          if x == 0 || s.2.1 == 0 then (fb heap s.1, 0, s.2.2)
          else
            let q := s.2.1 / gcdWord s.2.1 x
            if q > 1152921504606846975 / x then (fb heap s.1, s.2.1, true)
            else (fb heap s.1, q * x, s.2.2))
      if r.2.2 && r.2.1 != 0 then (S_RESTRICTION + M_RANGE, 0)
      else if r.2.1 ≤ 1152921504606846975 then (0, mkFix r.2.1.toInt64)
      else (S_RESTRICTION + M_RANGE, 0)
    else (0, mkFix a)

/-- The machine after the numeric procedure `op` on its arguments: the result in `val`, or the
outcome. -/
def apply (m : Machine) (op : UInt64) : Machine :=
  let r := compute m.heap op m.args m.nargs
  if r.1 == 0 then { m with val := r.2 } else fail m r.1 0

end Demos.Scheme.Machine.Numeric
