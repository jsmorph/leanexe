import Verified.Reflect.Command

/-! The eleventh program of the verified compiler: arrays that grow with `xs.push v` and
`xs ++ ys`.  An owned array that dies at the operation grows in its own block while the block has
room, and otherwise moves to a block of twice its capacity, so that a loop of pushes copies its
elements a number of times logarithmic in the final length.  Any other array is copied once into a
block with room for the result. -/

namespace Verified.Examples.Grow

def pushParam (xs : Array UInt64) (v : UInt64) : Array UInt64 := xs.push v

def pushBuilt (n v : UInt64) : Array UInt64 := (LeanExe.build n fun i => i).push v

def pushTwo (n a b : UInt64) : Array UInt64 := ((LeanExe.build n fun i => i).push a).push b

def pushSize (n : UInt64) : Array UInt64 :=
  let xs := LeanExe.build n fun i => i
  xs.push xs.size.toUInt64

def pushKeep (n v : UInt64) : Array UInt64 × Array UInt64 :=
  let ys := LeanExe.build n fun i => i
  (ys.push v, ys)

def evens (n : UInt64) : Array UInt64 :=
  LeanExe.loop n (LeanExe.build 0 fun _ => 0) fun i acc => acc.push (2 * i)

def appendParams (xs ys : Array UInt64) : Array UInt64 := xs ++ ys

def appendBuilt (n : UInt64) (ys : Array UInt64) : Array UInt64 :=
  (LeanExe.build n fun i => i) ++ ys

def appendRoom (n : UInt64) (ys : Array UInt64) : Array UInt64 :=
  ((LeanExe.build n fun i => i).push 7) ++ ys

def appendSelf (xs : Array UInt64) : Array UInt64 := xs ++ xs

def appendSelfOwned (n : UInt64) : Array UInt64 :=
  let xs := LeanExe.build n fun i => i + 1
  xs ++ xs

def appendOwnedRight (xs : Array UInt64) (n : UInt64) : Array UInt64 :=
  xs ++ LeanExe.build n fun i => i

def repeated (xs : Array UInt64) (n : UInt64) : Array UInt64 :=
  LeanExe.loop n (LeanExe.build 0 fun _ => 0) fun _ acc => acc ++ xs

verified_compile compiled := [pushParam, pushBuilt, pushTwo, pushSize, pushKeep, evens,
  appendParams, appendBuilt, appendRoom, appendSelf, appendSelfOwned, appendOwnedRight, repeated]

end Verified.Examples.Grow
