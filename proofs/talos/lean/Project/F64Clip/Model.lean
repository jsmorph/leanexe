import Project.ProofKit.F64Absolute

namespace Project.F64Clip
open Project.ProofKit.F64Order

def validBound (bound : UInt64) : Bool :=
  finiteBits bound &&
    (decide (bound < 0x8000000000000000) || absBits bound == 0) &&
    decide (absBits bound ≤ 0x4024000000000000)

def clip (bound x : UInt64) : UInt64 :=
  if absBits x ≤ absBits bound then x
  else if x < 0x8000000000000000 then absBits bound else negativeAbsBits bound

def accepted (count : Nat) (bound : UInt64) (weights : Array UInt64) : Bool :=
  decide (weights.size = count) && validBound bound && weights.all (fun x => finiteBits x)

def prepare (count : Nat) (bound : UInt64) (weights : Array UInt64) : Array UInt64 :=
  if accepted count bound weights then weights.map (fun x => clip bound x) else #[]

end Project.F64Clip
