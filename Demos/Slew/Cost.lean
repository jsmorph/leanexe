import Demos.Slew.NanFree
import Library.Numerics.Float64.Tanh.Expm1ReduceWords

/-! The cost of an edge of the slew planner's graph.  For an input that passes `validInput`, the
duration of the rotation between two nodes in whole milliseconds, plus the settling time in
whole milliseconds, is at most `2 ^ 34` (`edge_cost_le`), so a sum over a path of at most 1,026
edges stays far below the sentinel `infinity = 2 ^ 62`.  The rate limit of at least `1e-5` rad/s
and the acceleration limit of at least `1e-7` rad/s² bound the duration of a rotation by at most
4.1 rad by about `1.04e10` ms, and the settling time of at most 3,600 s gives `3.6e6` ms.
`ceilMs_le` bounds the rounded-up milliseconds by the computed value plus one, from the
truncation of `Float.toUInt64` (`toUInt64_le`). -/

namespace Demos.Slew.Cost

open Demos.Slew.Spec Demos.Slew.Rounding Demos.Slew.Error Demos.Slew.Axis Demos.Slew.Cone
open Demos.Slew.Decide Demos.Slew.Check Demos.Slew.Valid Demos.Slew.Angle Demos.Slew.Relative
open Demos.Slew.Arc Demos.Slew.NanFree
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- `Float.toUInt64` truncates a finite value below `2 ^ 62` to at most the value, and a value
that is not positive to 0. -/
theorem toUInt64_le {x : Float} (hf : Rounding.Fin x) (hx : val x < 2 ^ 62) :
    (x.toUInt64.toNat : ℝ) ≤ max (val x) 0 := by
  rw [F64Convert.toUInt64_eq]
  cases hs : Wasm.IEEE64.sign x.toBits
  · exact (Library.Numerics.Float64.Tanh.Expm1ReduceWords.truncSat_spec x.toBits hf hs hx).1.trans
      (le_max_left _ _)
  · have hfin : Wasm.IEEE64.isFinite x.toBits = true := hf
    have htr : Wasm.IEEE64.truncatedInt x.toBits =
        some (-((Wasm.IEEE64.scaledMagnitude x.toBits / 2 ^ 1074 : ℕ) : ℤ)) := by
      unfold Wasm.IEEE64.truncatedInt
      rw [ite_eq_left hfin]
      simp only [hs, ite_true]
    have hz : Wasm.IEEE64.truncSatI64U x.toBits = 0 := by
      unfold Wasm.IEEE64.truncSatI64U
      rw [not_nan_of_finite hf]
      simp only [Bool.false_eq_true, ite_false, htr]
      rw [ite_eq_left (neg_nonpos.mpr (by positivity))]
    rw [hz]
    simp

/-- `ceilMs t` is at most one more than the computed `t * 1000`. -/
theorem ceilMs_le {t : Float} {M : ℝ} (hf : Rounding.Fin (t * 1000.0))
    (hy : val (t * 1000.0) ≤ M) (hM0 : 0 ≤ M) (hM : M < 2 ^ 61) :
    ((ceilMs t).toNat : ℝ) ≤ M + 1 := by
  have hn := toUInt64_le hf (by linarith)
  have hn' : ((t * 1000.0).toUInt64.toNat : ℝ) ≤ M := hn.trans (max_le hy hM0)
  have hlt : (t * 1000.0).toUInt64.toNat < 2 ^ 61 := by exact_mod_cast hn'.trans_lt hM
  unfold ceilMs
  dsimp only
  split
  · have e : ((t * 1000.0).toUInt64 + 1).toNat = (t * 1000.0).toUInt64.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
    rw [e]
    push_cast
    linarith
  · linarith

theorem thousand_bnd : Bnd (1000.0 : Float) 1000 0 1000 := by
  have h := Bnd.of_val one_thousand_val.1 (M := 1000) (by rw [one_thousand_val.2]; norm_num)
  rwa [one_thousand_val.2] at h

/-- The duration of a rotation by at most 4.1 rad within the limits of `validInput` is at most
`1.05e10 + 1` ms. -/
theorem ticks_le {theta wmax amax : Float} (ht : Rounding.Fin theta) (ht0 : 0 ≤ val theta)
    (ht1 : val theta ≤ 4.1) (hw : Rounding.Fin wmax) (hw0 : 0.9999e-5 ≤ val wmax)
    (hw1 : val wmax ≤ 1) (ha : Rounding.Fin amax) (ha0 : 0.9999e-7 ≤ val amax)
    (ha1 : val amax ≤ 1) : ((slewTicks theta wmax amax).toNat : ℝ) ≤ 1.05e10 + 1 := by
  have Bt := Bnd.of_val ht (M := 4.1) (by rw [abs_of_nonneg ht0]; exact ht1)
  have Bw := Bnd.of_val hw (M := 1) (by rw [abs_of_nonneg (by linarith)]; exact hw1)
  have Ba := Bnd.of_val ha (M := 1) (by rw [abs_of_nonneg (by linarith)]; exact ha1)
  have hwa : 0.9999e-5 ≤ |val wmax| := by rw [abs_of_nonneg (by linarith)]; exact hw0
  have haa : 0.9999e-7 ≤ |val amax| := by rw [abs_of_nonneg (by linarith)]; exact ha0
  have t1 := Bnd.div 1e-9 Bt Bw hwa (by norm_num) (by norm_num) (by norm_num)
  have t2 := Bnd.div 1e-8 Bw Ba haa (by norm_num) (by norm_num) (by norm_num)
  have s := Bnd.add 1e-7 t1 t2 (by norm_num) (by norm_num)
  have q := Bnd.div 1e-8 Bt Ba haa (by norm_num) (by norm_num) (by norm_num)
  have q0 := div_nonneg' ht ha q.1.1 ht0 (by linarith)
  obtain ⟨fr, r0, r1⟩ := sqrt_facts q.1.1 q0
  have hq1 : val (theta / amax) ≤ 4.2e7 := by
    have := q.upper; have := q.2
    have h2 : (4.1 : ℝ) / 0.9999e-7 ≤ 4.11e7 := by norm_num
    have := abs_le.mp q.2
    linarith
  have hr1 : val (Float.sqrt (theta / amax)) ≤ 7000 := by
    have : √(val (theta / amax)) ≤ 6481 := by
      rw [show (6481 : ℝ) = √(6481 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  have Br := Bnd.of_val fr (M := 7000) (by rw [abs_of_nonneg r0]; exact hr1)
  have t3 := Bnd.mul (14001 / 2 ^ 53) Bnd.two Br (by norm_num) (by norm_num)
  unfold slewTicks
  split
  · have hB := Bnd.mul 1e-3 s thousand_bnd (by norm_num) (by norm_num)
    have h1 := hB.upper
    have h2 := (abs_le.mp hB.2).2
    have h3 : (4.1 / 0.9999e-5 + 1 / 0.9999e-7) * 1000 + 1e-3 ≤ (1.05e10 : ℝ) := by norm_num
    exact ceilMs_le hB.1.1 (by linarith) (by norm_num) (by norm_num)
  · have hB := Bnd.mul 1e-3 t3 thousand_bnd (by norm_num) (by norm_num)
    have h1 := hB.upper
    have h2 := (abs_le.mp hB.2).2
    have h3 : 2 * 7000 * 1000 + 1e-3 ≤ (1.05e10 : ℝ) := by norm_num
    exact ceilMs_le hB.1.1 (by linarith) (by norm_num) (by norm_num)

/-- The settling time of at most 3,600 s is at most 3,600,002 ms. -/
theorem settle_le {x : Float} (hf : Rounding.Fin x) (h0 : 0 ≤ val x) (h1 : val x ≤ 3600) :
    ((ceilMs x).toNat : ℝ) ≤ 3600002 := by
  have B6 := Bnd.of_val hf (M := 3600) (by rw [abs_of_nonneg h0]; exact h1)
  have hB := Bnd.mul 1e-6 B6 thousand_bnd (by norm_num) (by norm_num)
  have h2 := hB.upper
  have h3 := (abs_le.mp hB.2).2
  have := ceilMs_le hB.1.1 (M := 3600001) (by linarith) (by norm_num) (by norm_num)
  linarith

/-- **The cost of an edge.**  For an input that passes `validInput` and two nodes, the duration
of the rotation between them plus the settling time, in whole milliseconds, is at most
`2 ^ 34`. -/
theorem edge_cost_le {xs : Array Float} (h : validInput xs = true) {a b : UInt64}
    (ha : a.toNat < (dims xs).nw.toNat + 2) (hb : b.toNat < (dims xs).nw.toNat + 2) :
    (slewTicks (angleOf (relative (nodeAt xs (dims xs) a) (nodeAt xs (dims xs) b))) (rd xs 4)
      (rd xs 5) + ceilMs (rd xs 6)).toNat ≤ 2 ^ 34 := by
  obtain ⟨hnodes, _, _⟩ := valid_good h
  have hv := facts_of h
  have t := dims_facts hv
  obtain ⟨r4a, r4b, r5a, r5b, l6a, l6b⟩ := limits_of h
  have f4 : Rounding.Fin (rd xs 4) := fin_at hv (by simp only [UInt64.reduceToNat]; omega)
  have f5 : Rounding.Fin (rd xs 5) := fin_at hv (by simp only [UInt64.reduceToNat]; omega)
  have f6 : Rounding.Fin (rd xs 6) := fin_at hv (by simp only [UInt64.reduceToNat]; omega)
  have hw0 : 0.9999e-5 ≤ val (rd xs 4) := rateMin_val.2.trans (le_val_of_le r4a)
  have hw1 : val (rd xs 4) ≤ 1 := by have := le_val_of_le r4b; rwa [one_val.2] at this
  have ha0 : 0.9999e-7 ≤ val (rd xs 5) := accelMin_val.2.trans (le_val_of_le r5a)
  have ha1 : val (rd xs 5) ≤ 1 := by have := le_val_of_le r5b; rwa [one_val.2] at this
  have h6a : 0 ≤ val (rd xs 6) := by have := le_val_of_le l6a; rwa [zero_val.2] at this
  have h6b : val (rd xs 6) ≤ 3600 := by
    have := le_val_of_le l6b; rwa [three_thousand_six_hundred_val] at this
  set rel := relative (nodeAt xs (dims xs) a) (nodeAt xs (dims xs) b) with hrel
  have hr : GoodRel rel := relative_good (hnodes a ha) (hnodes b hb)
  obtain ⟨fθ, hθ⟩ := angle_out hr
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hθ0, _, _⟩ := ((plan_finite h).2.2.2 a b ha hb).2
  have hθ1 : val (angleOf rel) ≤ 4.1 := by
    have h1 := (abs_le.mp hθ).2
    have h2 : angleR rel ≤ Real.pi := angle_le_pi _ _
    have h3 := Real.pi_lt_four
    linarith
  have hT := ticks_le fθ hθ0 hθ1 f4 hw0 hw1 f5 ha0 ha1
  have hS := settle_le f6 h6a h6b
  have hT' : (slewTicks (angleOf rel) (rd xs 4) (rd xs 5)).toNat ≤ 10500000001 := by
    have := hT.trans (show (1.05e10 : ℝ) + 1 ≤ 10500000001 by norm_num)
    exact_mod_cast this
  have hS' : (ceilMs (rd xs 6)).toNat ≤ 3600002 := by exact_mod_cast hS
  rw [UInt64.toNat_add]
  omega

end Demos.Slew.Cost
