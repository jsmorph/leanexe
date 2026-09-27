/-!
Pure binary64 operations used by the spectral estimator's executable source.

These integer definitions are adapted from Interpreter.Wasm.IEEE64 and its
three rounding helpers. Project.SpectralKL.Operations proves equality with
those definitions for every input word. LeanExe lowers the five operations to
WASM binary64 instructions; native Lean evaluates these exact definitions.
-/
namespace LeanExe.IEEE64

def roundShift (n shift : Nat) : Nat :=
  let unit := 2 ^ shift
  let quotient := n / unit
  let remainder := n % unit
  let half := unit / 2
  if remainder < half then quotient
  else if half < remainder then quotient + 1
  else if quotient % 2 == 0 then quotient else quotient + 1

def roundQuotient (numerator denominator : Nat) : Nat :=
  if denominator == 0 then 0
  else
    let quotient := numerator / denominator
    let twiceRemainder := 2 * (numerator % denominator)
    if twiceRemainder < denominator then quotient
    else if denominator < twiceRemainder then quotient + 1
    else if quotient % 2 == 0 then quotient else quotient + 1

def roundSqrtIntegral (radicand shift : Nat) : Nat :=
  let lower := Nat.sqrt radicand / 2 ^ shift
  let midpointSquared := (2 * lower + 1) ^ 2 * 2 ^ (2 * shift)
  let fourRadicand := 4 * radicand
  if fourRadicand < midpointSquared then lower
  else if midpointSquared < fourRadicand then lower + 1
  else if lower % 2 == 0 then lower else lower + 1

def canonicalNaN : UInt64 := 0x7FF8000000000000

def sign (x : UInt64) : Bool := decide (2 ^ 63 ≤ x.toNat)
def exponent (x : UInt64) : Nat := x.toNat / 2 ^ 52 % 2 ^ 11
def fraction (x : UInt64) : Nat := x.toNat % 2 ^ 52

def isNaN (x : UInt64) : Bool := exponent x == 0x7FF && fraction x != 0
def isInfinite (x : UInt64) : Bool :=
  exponent x == 0x7FF && fraction x == 0
def isFinite (x : UInt64) : Bool := exponent x != 0x7FF

def scaledMagnitude (x : UInt64) : Nat :=
  let e := exponent x
  let f := fraction x
  if e == 0 then f else (2 ^ 52 + f) * 2 ^ (e - 1)

def scaledValue (x : UInt64) : Int :=
  let magnitude : Int := scaledMagnitude x
  if sign x then -magnitude else magnitude

def signMask (negative : Bool) : UInt64 :=
  if negative then 0x8000000000000000 else 0

def infinity (negative : Bool) : UInt64 :=
  signMask negative ||| 0x7FF0000000000000

def encodeFinite
    (negative : Bool) (exponentField fractionField : Nat) : UInt64 :=
  UInt64.ofNat
    ((if negative then 2 ^ 63 else 0) + exponentField * 2 ^ 52 + fractionField)

def negate (x : UInt64) : UInt64 :=
  encodeFinite (!sign x) (exponent x) (fraction x)

def abs (x : UInt64) : UInt64 :=
  encodeFinite false (exponent x) (fraction x)

def copySign (value source : UInt64) : UInt64 :=
  encodeFinite (sign source) (exponent value) (fraction value)

def roundScaledMagnitude (negative : Bool) (n : Nat) : UInt64 :=
  if n < 2 ^ 52 then
    encodeFinite negative 0 n
  else if n < 2 ^ 53 then
    encodeFinite negative 1 (n - 2 ^ 52)
  else
    let shift := Nat.log2 n - 52
    let rounded := roundShift n shift
    let (finalShift, significand) :=
      if rounded == 2 ^ 53 then (shift + 1, 2 ^ 52)
      else (shift, rounded)
    let exponentField := finalShift + 1
    if 0x7FF ≤ exponentField then infinity negative
    else encodeFinite negative exponentField (significand - 2 ^ 52)

def roundDyadicMagnitude
    (negative : Bool) (n fractionalBits : Nat) : UInt64 :=
  if n == 0 then signMask negative
  else
    let outputShift := Nat.log2 n - (fractionalBits + 52)
    let candidate :=
      if outputShift == 0 then
        if fractionalBits == 0 then n
        else roundShift n fractionalBits
      else
        roundShift n (fractionalBits + outputShift) * 2 ^ outputShift
    roundScaledMagnitude negative candidate

def roundRationalMagnitude
    (negative : Bool) (numerator denominator : Nat) : UInt64 :=
  if numerator == 0 then signMask negative
  else if denominator == 0 then infinity negative
  else
    let integerPart := numerator / denominator
    let outputShift := Nat.log2 integerPart - 52
    let candidate :=
      if outputShift == 0 then
        roundQuotient numerator denominator
      else
        roundQuotient numerator (denominator * 2 ^ outputShift) *
          2 ^ outputShift
    roundScaledMagnitude negative candidate

def roundSqrtMagnitude (magnitude : Nat) : UInt64 :=
  if magnitude == 0 then 0
  else
    let radicand := magnitude * 2 ^ 1074
    let rootFloor := Nat.sqrt radicand
    let outputShift := Nat.log2 rootFloor - 52
    let rounded := roundSqrtIntegral radicand outputShift
    roundScaledMagnitude false (rounded * 2 ^ outputShift)

def addBits (a b : UInt64) : UInt64 :=
  if isNaN a || isNaN b then canonicalNaN
  else if isInfinite a then
    if isInfinite b && sign a != sign b then canonicalNaN else a
  else if isInfinite b then b
  else
    let sum := scaledValue a + scaledValue b
    if sum == 0 then
      if sign a && sign b then signMask true else 0
    else roundScaledMagnitude (sum < 0) sum.natAbs

def subBits (a b : UInt64) : UInt64 := addBits a (negate b)

def mulBits (a b : UInt64) : UInt64 :=
  if isNaN a || isNaN b then canonicalNaN
  else
    let negative := sign a != sign b
    let aZero := scaledMagnitude a == 0
    let bZero := scaledMagnitude b == 0
    if isInfinite a then
      if bZero then canonicalNaN else infinity negative
    else if isInfinite b then
      if aZero then canonicalNaN else infinity negative
    else if aZero || bZero then signMask negative
    else roundDyadicMagnitude negative
      (scaledMagnitude a * scaledMagnitude b) 1074

def divBits (a b : UInt64) : UInt64 :=
  if isNaN a || isNaN b then canonicalNaN
  else
    let negative := sign a != sign b
    let aZero := scaledMagnitude a == 0
    let bZero := scaledMagnitude b == 0
    if isInfinite a then
      if isInfinite b then canonicalNaN else infinity negative
    else if isInfinite b then signMask negative
    else if bZero then
      if aZero then canonicalNaN else infinity negative
    else if aZero then signMask negative
    else roundRationalMagnitude negative
      (scaledMagnitude a * 2 ^ 1074) (scaledMagnitude b)

def sqrtBits (a : UInt64) : UInt64 :=
  if isNaN a then canonicalNaN
  else
    let magnitude := scaledMagnitude a
    if magnitude == 0 then a
    else if sign a then canonicalNaN
    else if isInfinite a then a
    else roundSqrtMagnitude magnitude

end LeanExe.IEEE64
