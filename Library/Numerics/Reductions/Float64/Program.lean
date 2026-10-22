import LeanExe.Dialect.Loop

namespace Library.Numerics.Reductions.Float64

def total (xs : Array Float) : Float :=
  LeanExe.loop xs.size.toUInt64 0.0 fun i acc => acc + xs[i.toNat]!

/-- The largest element, or negative infinity for an empty array. -/
def largest (xs : Array Float) : Float :=
  LeanExe.loop xs.size.toUInt64 (-(1.0 / 0.0)) fun i acc => max acc xs[i.toNat]!

/-- The sum of the elements of `xs` whose flag in `bs` is true, a missing flag false. -/
def select (bs : Array Bool) (xs : Array Float) : Float :=
  LeanExe.loop xs.size.toUInt64 0.0 fun i acc => if bs[i.toNat]! then acc + xs[i.toNat]! else acc

/-- The sum of the elements of `xs` from `lo` up to `hi`, by halves. -/
def sumRange (xs : Array Float) (lo hi : UInt64) : Float :=
  if hi - lo ≤ 1 then (if hi - lo = 1 then xs[lo.toNat]! else 0.0)
  else
    let mid := lo + (hi - lo) / 2
    sumRange xs lo mid + sumRange xs mid hi
termination_by (hi - lo).toNat
decreasing_by
  all_goals
    rename_i h
    have := UInt64.toNat_lt lo
    have := UInt64.toNat_lt hi
    simp only [UInt64.le_iff_toNat_le, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_div,
      UInt64.reduceToNat] at h ⊢
    omega

end Library.Numerics.Reductions.Float64
