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

verified_compile compiled := [inlineScalar, inlineArray, inlineLoop, setDirect, insertDirect,
  eraseDirect, listed, listedCall]

#print axioms compiled.inlineScalar.denote_eq
#print axioms compiled.inlineArray.implements
#print axioms compiled.inlineLoop.trapFree
#print axioms compiled.insertDirect.implements
#print axioms compiled.eraseDirect.implements
#print axioms compiled.bytes

end Verified.Examples.Frontend
