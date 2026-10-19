import Verified.Reflect.Command
import Verified.Examples.TailReflection

namespace Verified.Examples.Tail

open TailReflection

def rotate (n : UInt64) (left right : Array UInt64) : Array UInt64 :=
  if n = 0 then left else rotate (n - 1) right left
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

def replace (n : UInt64) (xs : Array UInt64) : Array UInt64 :=
  if n = 0 then xs else replace (n - 1) #[]
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

def guardedCount (n : UInt64) : UInt64 :=
  if n = 0 then 0 else guardedCount (n - 1) + 1
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

def guardLoop (n acc : UInt64) : UInt64 :=
  if n = 0 then acc else guardLoop (n - 1) (acc + guardedCount 2)
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

def callsTail (n acc : UInt64) : UInt64 := tailCount n acc + tailCount (n + 1) acc

def sharedSeed (n : UInt64) (xs : Array UInt64) : Array UInt64 := tailGrow xs n xs

verified_compile compiled := [tailCount, tailGrow, tailEntries, tailScalarPair, rotate, replace,
  guardedCount, guardLoop, callsTail, sharedSeed]

theorem count_bound (n acc : UInt64) : compiled.tailCount.bound (n, acc) = 0 := by
  rw [compiled.tailCount.bound_eq]

theorem count_no_depth : compiled.tailCount.func.depth = false := rfl

theorem guard_loop_depth : compiled.guardLoop.func.depth = true := rfl

#print axioms compiled.bytes
#print axioms count_bound
#print axioms compiled.tailGrow.bound_eq
#print axioms compiled.guardLoop.fits_eq

end Verified.Examples.Tail
