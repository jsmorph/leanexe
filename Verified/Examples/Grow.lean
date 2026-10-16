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

/-- The first push of `pushTwo` is charged a block of twice the bytes of its new length and twice
its 8 added bytes, and the second, which grows the paid result of the first, a header and four times
its 8 added bytes. -/
theorem pushTwo_bound (n a b : UInt64) :
    compiled.pushTwo.bound (n, a, b) =
      blockCost n.toNat + growCost ((LeanExe.build n fun i => i).size + 1) 1 + (48 + 32) := by
  rw [compiled.pushTwo.bound_eq, paidGrowCost_eq]

/-- `evens` pushes `n` words onto a paid loop state, at a header and four times the 8 added bytes
each, after the built array's block and its credit. -/
theorem evens_bound (n : UInt64) : compiled.evens.bound n = 72 + 80 * n.toNat := by
  rw [compiled.evens.bound_eq, loopCost_const]
  simp only [LeanExe.build, Array.size_ofFn, blockCost_eq, creditCost, paidGrowCost_eq,
    UInt64.toNat_zero]
  omega

/-- `repeated` appends `xs` to a paid loop state `n` times, at a header and four times the added
bytes each, after the built array's block and its credit. -/
theorem repeated_bound (xs : Array UInt64) (n : UInt64) :
    compiled.repeated.bound (xs, n) = 72 + n.toNat * (32 * xs.size + 48) := by
  rw [compiled.repeated.bound_eq, loopCost_const]
  simp only [LeanExe.build, Array.size_ofFn, blockCost_eq, creditCost, paidGrowCost_eq,
    UInt64.toNat_zero]

end Verified.Examples.Grow
