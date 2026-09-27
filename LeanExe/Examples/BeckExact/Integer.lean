namespace LeanExe.Examples.BeckExact

namespace Digits

def radix : UInt64 := 4294967296

def lengthFrom : Nat → Array UInt64 → Nat
  | 0, _ => 0
  | count + 1, a => if a[count]! != 0 then count + 1 else lengthFrom count a

def length (a : Array UInt64) : Nat := lengthFrom a.size a

def trim (a : Array UInt64) : Array UInt64 := a.extract 0 (length a)

def get (a : Array UInt64) (index : Nat) : UInt64 :=
  if index < a.size then a[index]! else 0

def compareFrom : Nat → Array UInt64 → Array UInt64 → UInt64
  | 0, _, _ => 0
  | count + 1, a, b =>
    if a[count]! < b[count]! then 1
    else if b[count]! < a[count]! then 2
    else compareFrom count a b

def compare (a b : Array UInt64) : UInt64 :=
  let an := length a
  let bn := length b
  if an < bn then 1
  else if bn < an then 2
  else compareFrom an a b

def add (a b : Array UInt64) : Array UInt64 := Id.run do
  let mut result := #[]
  let mut carry : UInt64 := 0
  for index in [:max a.size b.size] do
    let total := get a index + get b index + carry
    result := result.push (total % radix)
    carry := total / radix
  if carry != 0 then result := result.push carry
  return trim result

def sub (a b : Array UInt64) : Array UInt64 := Id.run do
  let mut result := #[]
  let mut borrow : UInt64 := 0
  for index in [:a.size] do
    let left := a[index]!
    let right := get b index + borrow
    result := result.push ((left + radix - right) % radix)
    borrow := if left < right then 1 else 0
  return trim result

def mul (a b : Array UInt64) : Array UInt64 := Id.run do
  let mut result := Array.replicate (a.size + b.size) (0 : UInt64)
  for i in [:a.size] do
    let mut carry : UInt64 := 0
    for j in [:b.size] do
      let total := a[i]! * b[j]! + result[i + j]! + carry
      result := result.set! (i + j) (total % radix)
      carry := total / radix
    result := result.set! (i + b.size) carry
  return trim result

def shiftBit (a : Array UInt64) (bit : UInt64) : Array UInt64 := Id.run do
  let mut result := #[]
  let mut carry := bit
  for index in [:a.size] do
    let total := a[index]! * 2 + carry
    result := result.push (total % radix)
    carry := total / radix
  if carry != 0 then result := result.push carry
  return trim result

def divRem (a b : Array UInt64) : Option (Array UInt64 × Array UInt64) := Id.run do
  if length b == 0 then return none
  let mut quotient := Array.replicate a.size (0 : UInt64)
  let mut remainder := #[]
  for offset in [:32 * a.size] do
    let index := 32 * a.size - 1 - offset
    let bit := (a[index / 32]! >>> (index % 32).toUInt64) &&& 1
    remainder := shiftBit remainder bit
    if compare remainder b != 1 then
      remainder := sub remainder b
      quotient := quotient.set! (index / 32)
        (quotient[index / 32]! + (1 <<< (index % 32).toUInt64))
  return some (trim quotient, remainder)

end Digits

structure Integer where
  negative : Bool
  digits : Array UInt64
  deriving Inhabited, Repr

namespace Integer

def make (negative : Bool) (digits : Array UInt64) : Integer :=
  let ds := Digits.trim digits
  ⟨negative && ds.size != 0, ds⟩

def zero : Integer := ⟨false, #[]⟩

def ofWord (word : UInt64) : Integer := make false #[word % Digits.radix, word / Digits.radix]

def isZero (a : Integer) : Bool := Digits.length a.digits == 0

def neg (a : Integer) : Integer := make (!a.negative) a.digits

def abs (a : Integer) : Integer := ⟨false, a.digits⟩

def equal (a b : Integer) : Bool :=
  a.negative == b.negative && Digits.compare a.digits b.digits == 0

def less (a b : Integer) : Bool :=
  if a.negative != b.negative then a.negative
  else if a.negative then Digits.compare a.digits b.digits == 2
  else Digits.compare a.digits b.digits == 1

def add (a b : Integer) : Integer :=
  if a.negative == b.negative then make a.negative (Digits.add a.digits b.digits)
  else if Digits.compare a.digits b.digits == 1 then make b.negative (Digits.sub b.digits a.digits)
  else make a.negative (Digits.sub a.digits b.digits)

def sub (a b : Integer) : Integer := add a (neg b)

def mul (a b : Integer) : Integer := make (a.negative != b.negative) (Digits.mul a.digits b.digits)

def divideExact (a b : Integer) : Option Integer :=
  match Digits.divRem a.digits b.digits with
  | none => none
  | some (quotient, remainder) =>
    if Digits.length remainder != 0 then none
    else some (make (a.negative != b.negative) quotient)

end Integer

end LeanExe.Examples.BeckExact
