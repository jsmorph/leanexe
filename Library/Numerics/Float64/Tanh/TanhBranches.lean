import Library.Numerics.Float64.Tanh.Expm1Branches

/-!
The branches of fdlibm's `tanh` in `Tanh.tanh`.  Outside the non-finite and tiny inputs the code
computes `z` from `abs(x)` alone, in `core`, and returns `z` or `-z` by the sign of `x`.
-/

namespace Library.Numerics.Float64.Tanh.TanhBranches
open CodeLib.IEEE64 LeanExe.ProofKit Expm1Branches

/-- `z` of fdlibm's `tanh` for a finite input outside the tiny range. -/
def core (x : Float) : Float :=
  if highWord x.toBits < 1077280768 then
    if highWord x.toBits ≥ 1072693248 then
      1.0 - 2.0 / (Tanh.expm1 (2.0 * x.abs) + 2.0)
    else (-Tanh.expm1 (-2.0 * x.abs)) / (Tanh.expm1 (-2.0 * x.abs) + 2.0)
  else 1.0 - Float.ofBits 0x01A56E1FC2F8F359

theorem select_nonfinite (x : Float) (h1 : highWord x.toBits ≥ 2146435072) :
    Tanh.tanh x = if sgn x.toBits = true then 1.0 / x - 1.0 else 1.0 / x + 1.0 := by
  have h1' : x.toBits >>> 32 &&& 2147483647 ≥ 2146435072 := h1
  unfold Tanh.tanh
  simp only []
  rw [ite_eq_left h1']
  rfl

theorem select_tiny (x : Float) (h1 : ¬ highWord x.toBits ≥ 2146435072)
    (h2 : highWord x.toBits < 1043333120) (h3 : Float.ofBits 9094988921128908188 + x > 1.0) :
    Tanh.tanh x = x := by
  have h1' : ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) := h1
  have h2' : x.toBits >>> 32 &&& 2147483647 < 1043333120 := h2
  unfold Tanh.tanh
  simp only []
  rw [ite_eq_right h1']
  simp [h2', h3]

theorem select_main (x : Float) (h1 : ¬ highWord x.toBits ≥ 2146435072)
    (h2 : ¬ (highWord x.toBits < 1043333120 ∧ Float.ofBits 9094988921128908188 + x > 1.0)) :
    Tanh.tanh x = if sgn x.toBits = true then -core x else core x := by
  have h1' : ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) := h1
  unfold Tanh.tanh core
  simp only []
  rw [ite_eq_right h1', ite_eq_right]
  · rfl
  · simpa [highWord] using h2

#print axioms select_nonfinite
#print axioms select_tiny
#print axioms select_main

end Library.Numerics.Float64.Tanh.TanhBranches
