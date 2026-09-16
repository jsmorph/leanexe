import Project.ProofKit.F64Outward

namespace Project.ProofKit.F64Interval
open Project.ProofKit.F64Order (finiteBits positiveBits)

structure Bounds where
  status : UInt64
  lower : UInt64
  upper : UInt64
  deriving DecidableEq, Inhabited, Repr

def rejected : Bounds := ⟨1, 0, 0⟩

def pack (lower upper : F64Outward.Checked) : Bounds :=
  if lower.status == 0 && upper.status == 0 then ⟨0, lower.value, upper.value⟩
  else rejected

def point (word : UInt64) : Bounds :=
  if finiteBits word then ⟨0, word, word⟩ else rejected

def add (a b : Bounds) : Bounds :=
  if a.status == 0 && b.status == 0 then
    pack (F64Outward.add false a.lower b.lower) (F64Outward.add true a.upper b.upper)
  else rejected

def sub (a b : Bounds) : Bounds :=
  if a.status == 0 && b.status == 0 then
    pack (F64Outward.sub false a.lower b.upper) (F64Outward.sub true a.upper b.lower)
  else rejected

def scale (a : Bounds) (word : UInt64) : Bounds :=
  if a.status == 0 then
    if word < 0x8000000000000000 then
      pack (F64Outward.mul false a.lower word) (F64Outward.mul true a.upper word)
    else
      pack (F64Outward.mul false a.upper word) (F64Outward.mul true a.lower word)
  else rejected

def divPositive (a : Bounds) (word : UInt64) : Bounds :=
  if a.status == 0 && positiveBits word then
    pack (F64Outward.div false a.lower word) (F64Outward.div true a.upper word)
  else rejected

end Project.ProofKit.F64Interval
