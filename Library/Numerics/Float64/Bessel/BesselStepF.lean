import Library.Numerics.Float64.Bessel.BesselForward
import Library.Numerics.Float64.Bessel.BesselPQEval
import Library.Numerics.Float64.Log.LogCoreBits
import LeanExe.ProofKit.F64Convert
import LeanExe.Dialect.Loop
import LeanExe.Dialect.RepeatWhile

/-!
The floating-point facts that the loops of `jn` and `yn` share.  A word whose value is below
`2^1024` in magnitude is finite (`finite_of_abs_lt`), since the exponent 2047 of infinities and NaNs
gives a value of at least `2^1024`.  `toFloat` of a word below `2^53` is exact (`toFloat_exact`).
One step `b ⊗ (t ⊘ x) ⊖ a` or `(t ⊘ x) ⊗ b ⊖ a` of the recurrence, with `t = T` exact, `x = w ≥ 2`,
and `|a|, |b| ≤ 1`, lies within `u (3.01 (T/w) |b| + |a|) + 2^-1070` of `(T/w) b - a` (`step_bt`,
`step_tb`).  `go_iterate` evaluates `LeanExe.repeatWhile` as the `N`-th iterate of its step when
the condition holds for the first `N` states and fails at the `N`-th.
-/

namespace Library.Numerics.Float64.Bessel.BesselStepF
open Real CodeLib.IEEE64 LeanExe.ProofKit F64Approx BesselPQEval

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

set_option exponentiation.threshold 4096 in
/-- A word of magnitude below `2^1024` is finite. -/
theorem finite_of_abs_lt (w : UInt64) (h : |value w| < 2 ^ 1024) : Finite w := by
  by_contra hnf
  have he : Wasm.IEEE64.exponent w = 2047 := by
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hnf
    simpa using hnf
  have hm : 2 ^ 2098 ≤ Wasm.IEEE64.scaledMagnitude w := by
    have hs : Wasm.IEEE64.scaledMagnitude w = (2 ^ 52 + Wasm.IEEE64.fraction w) * 2 ^ 2046 := by
      simp [Wasm.IEEE64.scaledMagnitude, he]
    rw [hs]
    calc (2 : ℕ) ^ 2098 = 2 ^ 52 * 2 ^ 2046 := by norm_num
      _ ≤ (2 ^ 52 + Wasm.IEEE64.fraction w) * 2 ^ 2046 :=
        Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hv : |value w| = (Wasm.IEEE64.scaledMagnitude w : ℝ) / 2 ^ 1074 := by
    rw [value, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), ← Int.cast_abs,
      Int.abs_eq_natAbs, natAbs_scaledValue, Int.cast_natCast]
  have hm' : (2 : ℝ) ^ 2098 ≤ (Wasm.IEEE64.scaledMagnitude w : ℝ) := by exact_mod_cast hm
  rw [hv, div_lt_iff₀ (by positivity)] at h
  have e : (2 : ℝ) ^ 1024 * 2 ^ 1074 = 2 ^ 2098 := by norm_num
  linarith

/-- `toFloat` of a word up to `2^53` is exact. -/
theorem toFloat_exact (n : UInt64) (hn : n.toNat ≤ 2 ^ 53) : FApprox n.toFloat (n.toNat : ℝ) 0 := by
  obtain ⟨hf, hv⟩ := Library.Numerics.Float64.Log.LogCoreBits.convert_exact n hn
  unfold FApprox Approx
  rw [F64Convert.toBits_toFloat, hv, sub_self, abs_zero]
  exact ⟨hf, le_rfl⟩

/-- The rounding of one step, from the three operations' errors. -/
theorem step_arith {V A L r : ℝ} (hV0 : 0 ≤ V) (hV : V ≤ 1) (hL0 : 0 ≤ L)
    (hr : r ≤ V * L + A) :
    (V * (L / 2 ^ 53 + 1 / 2 ^ 1075) + V * (L + (L / 2 ^ 53 + 1 / 2 ^ 1075)) / 2 ^ 53 +
        1 / 2 ^ 1075) +
      (r + (V * (L / 2 ^ 53 + 1 / 2 ^ 1075) + V * (L + (L / 2 ^ 53 + 1 / 2 ^ 1075)) / 2 ^ 53 +
        1 / 2 ^ 1075)) / 2 ^ 53 ≤
      1 / 2 ^ 53 * (301 / 100 * L * V + A) + 1 / 2 ^ 1070 := by
  have hVL : 0 ≤ V * L := mul_nonneg hV0 hL0
  linarith

/-- Magnitudes in one step. -/
theorem step_mags {L V : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ 2 ^ 40) (hV0 : 0 ≤ V) (hV : V ≤ 1) :
    L / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 ∧ V * (L / 2 ^ 53 + 1 / 2 ^ 1075) ≤ 1 ∧
      V * (L + (L / 2 ^ 53 + 1 / 2 ^ 1075)) ≤ 2 ^ 41 ∧ V * L ≤ 2 ^ 40 := by
  have h1 : L / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 := by
    have : L / 2 ^ 53 ≤ 2 ^ 40 / 2 ^ 53 := div_le_div_of_nonneg_right hL (by positivity)
    have : (2 : ℝ) ^ 40 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 := by norm_num
    linarith
  have h0 : 0 ≤ L / 2 ^ 53 + 1 / 2 ^ 1075 := by positivity
  refine ⟨h1, ?_, ?_, ?_⟩
  · calc V * (L / 2 ^ 53 + 1 / 2 ^ 1075) ≤ 1 * 1 := mul_le_mul hV h1 h0 (by norm_num)
      _ = 1 := by norm_num
  · have h2 : L + (L / 2 ^ 53 + 1 / 2 ^ 1075) ≤ 2 ^ 41 := by
      have : (2 : ℝ) ^ 40 + 1 ≤ 2 ^ 41 := by norm_num
      linarith
    calc V * (L + (L / 2 ^ 53 + 1 / 2 ^ 1075)) ≤ 1 * 2 ^ 41 :=
          mul_le_mul hV h2 (by positivity) (by norm_num)
      _ = 2 ^ 41 := by norm_num
  · calc V * L ≤ 1 * 2 ^ 40 := mul_le_mul hV hL hL0 (by norm_num)
      _ = 2 ^ 40 := by norm_num

/-- One step `b ⊗ (t ⊘ x) ⊖ a` of the forward recurrence of `jn`. -/
theorem step_bt {a b t x : Float} {T w : ℝ} (ha : Finite a.toBits) (hb : Finite b.toBits)
    (ht : FApprox t T 0) (hx : FApprox x w 0) (hT : 0 ≤ T) (hw : 2 ≤ w) (hTw : T / w ≤ 2 ^ 40)
    (hA : |value a.toBits| ≤ 1) (hB : |value b.toBits| ≤ 1) :
    Finite (b * (t / x) - a).toBits ∧
      |value (b * (t / x) - a).toBits - (T / w * value b.toBits - value a.toBits)| ≤
        𝐮 * (301 / 100 * (T / w) * |value b.toBits| + |value a.toBits|) + 1 / 2 ^ 1070 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hw0 : 0 < w := by linarith
  have hL0 : 0 ≤ T / w := div_nonneg hT hw0.le
  have hV0 := abs_nonneg (value b.toBits)
  obtain ⟨m1, m2, m3, m4⟩ := step_mags hL0 hTw hV0 hB
  have hq := fapprox_div ht hx T w (by rw [abs_of_nonneg hT]) (le_abs_self w) (by linarith) (T / w)
    (by rw [add_zero, sub_zero]) (by linarith [show (2 : ℝ) ^ 40 < 2 ^ 1022 by norm_num])
  have hq' : FApprox (t / x) (T / w) (T / w / 2 ^ 53 + 1 / 2 ^ 1075) := fmono hq (by simp)
  have hp := fapprox_mul (fapprox_exact b hb) hq' |value b.toBits| (T / w) le_rfl
    (by rw [abs_of_nonneg hL0])
    ((|value b.toBits| + 0) * (T / w + (T / w / 2 ^ 53 + 1 / 2 ^ 1075))) le_rfl (by
      linarith [show (2 : ℝ) ^ 41 < 2 ^ 1022 by norm_num])
  have hab : |value b.toBits * (T / w) - value a.toBits| ≤
      |value b.toBits| * (T / w) + |value a.toBits| := by
    have := abs_sub (value b.toBits * (T / w)) (value a.toBits)
    rwa [abs_mul, abs_of_nonneg hL0] at this
  have hr := fapprox_sub hp (fapprox_exact a ha)
    (|value b.toBits * (T / w) - value a.toBits| + (0 * (T / w) + |value b.toBits| *
      (T / w / 2 ^ 53 + 1 / 2 ^ 1075) + 0 * (T / w / 2 ^ 53 + 1 / 2 ^ 1075) +
      (|value b.toBits| + 0) * (T / w + (T / w / 2 ^ 53 + 1 / 2 ^ 1075)) / 2 ^ 53 +
      1 / 2 ^ 1075 + 0)) le_rfl (by
        have : (2 : ℝ) ^ 40 + 1 + 1 + 2 ^ 41 / 2 ^ 53 + 1 / 2 ^ 1075 < 2 ^ 1023 := by norm_num
        linarith)
  refine ⟨hr.1, ?_⟩
  rw [show T / w * value b.toBits - value a.toBits = value b.toBits * (T / w) - value a.toBits by
    ring]
  refine le_trans hr.2 ?_
  have := step_arith hV0 hB hL0 hab
  rw [hu]
  linarith

/-- One step `(t ⊘ x) ⊗ b ⊖ a` of the forward recurrence of `yn`. -/
theorem step_tb {a b t x : Float} {T w : ℝ} (ha : Finite a.toBits) (hb : Finite b.toBits)
    (ht : FApprox t T 0) (hx : FApprox x w 0) (hT : 0 ≤ T) (hw : 2 ≤ w) (hTw : T / w ≤ 2 ^ 40)
    (hA : |value a.toBits| ≤ 1) (hB : |value b.toBits| ≤ 1) :
    Finite ((t / x) * b - a).toBits ∧
      |value ((t / x) * b - a).toBits - (T / w * value b.toBits - value a.toBits)| ≤
        𝐮 * (301 / 100 * (T / w) * |value b.toBits| + |value a.toBits|) + 1 / 2 ^ 1070 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hw0 : 0 < w := by linarith
  have hL0 : 0 ≤ T / w := div_nonneg hT hw0.le
  have hV0 := abs_nonneg (value b.toBits)
  obtain ⟨m1, m2, m3, m4⟩ := step_mags hL0 hTw hV0 hB
  have hq := fapprox_div ht hx T w (by rw [abs_of_nonneg hT]) (le_abs_self w) (by linarith) (T / w)
    (by rw [add_zero, sub_zero]) (by linarith [show (2 : ℝ) ^ 40 < 2 ^ 1022 by norm_num])
  have hq' : FApprox (t / x) (T / w) (T / w / 2 ^ 53 + 1 / 2 ^ 1075) := fmono hq (by simp)
  have hp := fapprox_mul hq' (fapprox_exact b hb) (T / w) |value b.toBits|
    (by rw [abs_of_nonneg hL0]) le_rfl
    ((T / w + (T / w / 2 ^ 53 + 1 / 2 ^ 1075)) * (|value b.toBits| + 0)) le_rfl (by
      linarith [show (2 : ℝ) ^ 41 < 2 ^ 1022 by norm_num])
  have hab : |T / w * value b.toBits - value a.toBits| ≤
      |value b.toBits| * (T / w) + |value a.toBits| := by
    have := abs_sub (T / w * value b.toBits) (value a.toBits)
    rw [abs_mul, abs_of_nonneg hL0] at this
    linarith
  have hr := fapprox_sub hp (fapprox_exact a ha)
    (|T / w * value b.toBits - value a.toBits| + ((T / w / 2 ^ 53 + 1 / 2 ^ 1075) *
      |value b.toBits| + T / w * 0 + (T / w / 2 ^ 53 + 1 / 2 ^ 1075) * 0 +
      (T / w + (T / w / 2 ^ 53 + 1 / 2 ^ 1075)) * (|value b.toBits| + 0) / 2 ^ 53 +
      1 / 2 ^ 1075 + 0)) le_rfl (by
        have : (2 : ℝ) ^ 40 + 1 + 1 + 2 ^ 41 / 2 ^ 53 + 1 / 2 ^ 1075 < 2 ^ 1023 := by norm_num
        linarith)
  refine ⟨hr.1, le_trans hr.2 ?_⟩
  have := step_arith hV0 hB hL0 hab
  rw [hu]
  linarith

/-- `repeatWhile` runs its step `N` times when the condition holds `N` times and then fails. -/
theorem go_iterate {α : Type} (cond : α → Bool) (step : α → α) :
    ∀ (N fuel : ℕ) (s : α), N ≤ fuel → (∀ j < N, cond (step^[j] s) = true) →
      cond (step^[N] s) = false → LeanExe.repeatWhile.go cond step fuel s = step^[N] s
  | 0, fuel, s, _, _, hstop => by
    rw [Function.iterate_zero_apply] at hstop
    cases fuel with
    | zero => rfl
    | succ k =>
      show (if cond s = true then LeanExe.repeatWhile.go cond step k (step s) else s) = s
      simp [hstop]
  | N + 1, fuel, s, hN, hc, hstop => by
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have h0 : cond s = true := hc 0 (by omega)
    have ih := go_iterate cond step N k (step s) (by omega)
      (fun j hj => by rw [← Function.iterate_succ_apply]; exact hc (j + 1) (by omega))
      (by rw [← Function.iterate_succ_apply]; exact hstop)
    show (if cond s = true then LeanExe.repeatWhile.go cond step k (step s) else s) =
      step^[N + 1] s
    rw [if_pos h0, ih, Function.iterate_succ_apply]

#print axioms finite_of_abs_lt
#print axioms toFloat_exact
#print axioms step_bt
#print axioms step_tb
#print axioms go_iterate

end Library.Numerics.Float64.Bessel.BesselStepF
