namespace LeanExe.KernelCheck

def maxLevel (u v : UInt64) : UInt64 := if u < v then v else u

/-- The concrete impredicative universe operation used by Pi formation. -/
def imaxLevel (u v : UInt64) : UInt64 := if v == 0 then 0 else maxLevel u v

/-- Operation 0 is max, 1 is imax. Results: 0 accepted, 1 incorrect,
3 unsupported operation. All UInt64 inputs are valid concrete levels. -/
def checkLevelOp (op u v expected : UInt64) : UInt64 :=
  if op == 0 then
    if expected == maxLevel u v then 0 else 1
  else if op == 1 then
    if expected == imaxLevel u v then 0 else 1
  else 3

end LeanExe.KernelCheck
