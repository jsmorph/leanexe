import Verified.Reflect.Command

namespace Verified.Examples.Frontend

@[inline] def offset (x k : UInt64) : UInt64 := x + k

abbrev shifted (x : UInt64) : UInt64 := offset x 3

def inlineScalar (x : UInt64) : UInt64 := shifted (offset x 5)

@[inline] def replace (xs : Array UInt64) (i v : UInt64) : Array UInt64 :=
  xs.setIfInBounds i.toNat v

def inlineArray (xs : Array UInt64) (i v : UInt64) : Array UInt64 :=
  replace (xs.push 7) i v

def inlineLoop (n : UInt64) : UInt64 :=
  LeanExe.loop n 0 fun i total => offset total (shifted i)

def setDirect (xs : Array UInt64) (i v : UInt64) : Array UInt64 :=
  xs.setIfInBounds i.toNat v

def insertDirect (xs : Array UInt64) (i v : UInt64) : Array UInt64 :=
  xs.insertIdxIfInBounds i.toNat v

def eraseDirect (xs : Array UInt64) (i : UInt64) : Array UInt64 :=
  xs.eraseIdxIfInBounds i.toNat

@[inline] def listed (x : UInt64) : UInt64 := x * 7

def listedCall (x : UInt64) : UInt64 := listed x + 1

def emptyWords : Array UInt64 := #[]

def emptyFloats : Array Float := #[]

structure Entry where
  key : UInt64
  price : Float
  active : Bool

instance : LeanExe.Pipeline.Flat Entry (UInt64 × Float × Bool) :=
  ⟨fun e => (e.key, e.price, e.active)⟩

def entries (n : UInt64) : UInt64 × Array Entry :=
  if n == 0 then (1, #[])
  else (0, LeanExe.build n fun i => ⟨i, i.toFloat, i % 2 == 0⟩)

def boolEq (a b : Bool) : Bool := a == b

def boolNe (a b : Bool) : Bool := a != b

def boolDecide (a b : Bool) : Bool := decide (a = b)

def boolIf (a b : Bool) : UInt64 := if a = b then 7 else 9

def boolIfNe (a b : Bool) : UInt64 := if a ≠ b then 7 else 9

def boolOwn (xs : Array UInt64) (flag : Bool) : Bool :=
  let ys := xs.push 7
  flag && 0 < ys.size.toUInt64

def boolCalls (xs : Array UInt64) (a b : Bool) : Bool := boolOwn xs a == boolOwn xs b

def boolRecord (a b : Bool) : Entry :=
  if a = b then ⟨7, 1.5, true⟩ else ⟨9, -2.5, false⟩

def boolRecords (a b : Bool) : Array Entry :=
  if a ≠ b then LeanExe.build 1 fun _ => ⟨7, 1.5, true⟩ else #[]

verified_compile compiled := [inlineScalar, inlineArray, inlineLoop, setDirect, insertDirect,
  eraseDirect, listed, listedCall, emptyWords, emptyFloats, entries, boolEq, boolNe, boolDecide,
  boolIf, boolIfNe, boolOwn, boolCalls, boolRecord, boolRecords]

#print axioms compiled.inlineScalar.denote_eq
#print axioms compiled.inlineArray.implements
#print axioms compiled.inlineLoop.trapFree
#print axioms compiled.insertDirect.implements
#print axioms compiled.eraseDirect.implements
#print axioms compiled.entries.implements
#print axioms compiled.boolCalls.implements
#print axioms compiled.bytes

end Verified.Examples.Frontend
