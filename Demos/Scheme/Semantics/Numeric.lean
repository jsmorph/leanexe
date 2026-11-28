module

@[expose] public section

/-! The numeric layer of the reference semantics.  Every numeric procedure of §6.5.5 that the
profile implements computes over Lean's `Int` here, and nothing in this module depends on a range.
A `Profile` decides which exact integers the implementation represents.  The fixnum profile
represents the signed 61-bit range, and an exact result outside it is a violation of an
implementation restriction (§6.5.3).  A profile of integers of any size changes only the
predicate. -/

namespace Demos.Scheme.Semantics.Numeric

/-- An implementation restriction on exact integers (§6.5.3): the integers it represents. -/
structure Profile where
  representable : Int → Bool

/-- The least integer of the fixnum profile, `-2^60`. -/
def fixnumMin : Int := -1152921504606846976

/-- The greatest integer of the fixnum profile, `2^60 - 1`. -/
def fixnumMax : Int := 1152921504606846975

/-- The fixnum profile: the integers from `-2^60` to `2^60 - 1`. -/
def fixnum : Profile := ⟨fun n => decide (fixnumMin ≤ n ∧ n ≤ fixnumMax)⟩

/-- The violations of an implementation restriction that the profile reports (§1.3.2, §6.5.3):
an exact integer outside the profile's range, an exact result that is no integer, and a numeral
that denotes no integer, such as an inexact, rational, or complex numeral. -/
inductive Restriction where
  | range
  | notInteger
  | number
  deriving DecidableEq, Repr

/-- The numeric procedures of the profile (§6.5.5). -/
inductive Op where
  | isNumber | isComplex | isReal | isRational | isInteger | isExact | isInexact
  | eq | lt | gt | le | ge
  | isZero | isPositive | isNegative | isOdd | isEven
  | max | min | add | mul | sub | div | abs
  | quotient | remainder | modulo | gcd | lcm
  | floor | ceiling | truncate | round
  deriving DecidableEq, Repr, Inhabited

/-- The arities that the report marks essential: `exact n`, `atLeast n`, or `between a b`. -/
inductive Arity where
  | exact (n : Nat)
  | atLeast (n : Nat)
  | between (a b : Nat)
  deriving DecidableEq, Repr

/-- Whether `n` arguments meet an arity. -/
def Arity.accepts : Arity → Nat → Bool
  | .exact k, n => n == k
  | .atLeast k, n => k ≤ n
  | .between a b, n => a ≤ n && n ≤ b

/-- The essential arity of each numeric procedure. -/
def Op.arity : Op → Arity
  | .eq | .lt | .gt | .le | .ge => .atLeast 2
  | .max | .min => .atLeast 1
  | .add | .mul | .gcd | .lcm => .atLeast 0
  | .sub | .div => .between 1 2
  | .quotient | .remainder | .modulo => .exact 2
  | _ => .exact 1

/-- Whether the procedure is a type predicate, which accepts any object. -/
def Op.isPredicate : Op → Bool
  | .isNumber | .isComplex | .isReal | .isRational | .isInteger => true
  | _ => false

/-- The mathematical result of a numeric procedure on exact integers. -/
inductive Result where
  | int (n : Int)
  | bool (b : Bool)
  | divideByZero
  | notInteger
  | arity
  deriving DecidableEq, Repr

/-- Whether every adjacent pair of the list meets `r`: the chained comparisons of §6.5.5. -/
def chain (r : Int → Int → Bool) : List Int → Bool
  | a :: b :: rest => r a b && chain r (b :: rest)
  | _ => true

/-- `n1 / n2` of exact integers (§6.5.5): the quotient when it is an integer. -/
def divide (a b : Int) : Result :=
  if b == 0 then .divideByZero
  else if Int.tmod a b == 0 then .int (Int.tdiv a b)
  else .notInteger

/-- The value of a numeric procedure on integer arguments, and `arity` for a number of arguments
outside its arity.  `quotient`
truncates, `remainder` takes the sign of the dividend, and `modulo` the sign of the divisor
(§6.5.5).  On integers, `floor`, `ceiling`, `truncate`, and `round` are the identity. -/
def eval : Op → List Int → Result
  | .isNumber, _ | .isComplex, _ | .isReal, _ | .isRational, _ | .isInteger, _ => .bool true
  | .isExact, _ => .bool true
  | .isInexact, _ => .bool false
  | .eq, xs => .bool (chain (· == ·) xs)
  | .lt, xs => .bool (chain (· < ·) xs)
  | .gt, xs => .bool (chain (· > ·) xs)
  | .le, xs => .bool (chain (· ≤ ·) xs)
  | .ge, xs => .bool (chain (· ≥ ·) xs)
  | .isZero, xs => .bool (xs.headD 0 == 0)
  | .isPositive, xs => .bool (xs.headD 0 > 0)
  | .isNegative, xs => .bool (xs.headD 0 < 0)
  | .isOdd, xs => .bool (Int.emod (xs.headD 0) 2 == 1)
  | .isEven, xs => .bool (Int.emod (xs.headD 0) 2 == 0)
  | .max, x :: xs => .int (xs.foldl Max.max x)
  | .min, x :: xs => .int (xs.foldl Min.min x)
  | .add, xs => .int (xs.foldl (· + ·) 0)
  | .mul, xs => .int (xs.foldl (· * ·) 1)
  | .sub, [a] => .int (-a)
  | .sub, [a, b] => .int (a - b)
  | .div, [a] => divide 1 a
  | .div, [a, b] => divide a b
  | .abs, xs => .int (xs.headD 0).natAbs
  | .quotient, [a, b] => if b == 0 then .divideByZero else .int (Int.tdiv a b)
  | .remainder, [a, b] => if b == 0 then .divideByZero else .int (Int.tmod a b)
  | .modulo, [a, b] => if b == 0 then .divideByZero else .int (Int.fmod a b)
  | .gcd, xs => .int (xs.foldl (fun g x => (Int.gcd g x : Int)) 0)
  | .lcm, xs => .int (xs.foldl (fun l x => (Int.lcm l x : Int)) 1)
  | .floor, xs | .ceiling, xs | .truncate, xs | .round, xs => .int (xs.headD 0)
  | _, _ => .arity

end Demos.Scheme.Semantics.Numeric
