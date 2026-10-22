import Library.Numerics.Float64.Bessel.BesselPQEval

/-!
`Bessel.pAsym` and the `Q` term of the code on one of fdlibm's ranges, from the checks of
`BesselRatioEval` and `BesselPQEval`.  `ratio_at` evaluates `R(ẑ)/S(ẑ)` at `ẑ = 1/(x x)` for `x` in
`[lo, hi]`, given the kernel checks on pieces of `ẑ` and of the real `z = 1/x²`.  `p_of_ratio` adds
the rounding of `1 + r/s`, at most `u` below 2.  `q0_of_ratio` and `q1_of_ratio` follow the code's
`(r/s - 1/8)/x` and `(3/8 + r/s)/x`: the sum is within `u/8` or `u/4` of exact, as the result lies
below `1/4` or `1/2`, and the division by the exact `x` adds a relative `u`.
-/

namespace Library.Numerics.Float64.Bessel.BesselPQRange
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound F64Approx F64HalfUlp F64Horner BesselRatioEval
  BesselPQEval BesselCS BesselRatio

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

theorem forall₂_words (ws : List UInt64) (h : ∀ w ∈ ws, Finite w) :
    List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) ws
      (ws.map ratOfWord) := by
  induction ws with
  | nil => exact List.Forall₂.nil
  | cons w rest ih =>
    exact List.Forall₂.cons ⟨h w (by simp), (ratOfWord_cast w).symm⟩
      (ih fun w hw => h w (by simp [hw]))

theorem fshift {f : Float} {v v' e d : ℝ} (h : FApprox f v e) (hv : |v - v'| ≤ d) :
    FApprox f v' (e + d) := by
  refine ⟨h.1, ?_⟩
  have := abs_sub_le (value f.toBits) v v'
  linarith [h.2]

/-- `R(ẑ)/S(ẑ)` at `ẑ = 1/(x x)`, and `|R/S| ≤ ρ` at `z = 1/x²`. -/
theorem ratio_at (rw sw : List UInt64) (hrf : ∀ w ∈ rw, Finite w) (hsf : ∀ w ∈ sw, Finite w)
    (hrne : rw ≠ []) (x : Float) (hxf : Finite x.toBits) (lo hi : ℝ)
    (hlo : lo ≤ value x.toBits) (hhi : value x.toBits ≤ hi) (h2 : 2 ≤ lo) (hb : hi ≤ 2 ^ 130)
    (δ E ρ a b : ℚ) (rest : List ℚ)
    (hck : piecesOk (rw.map ratOfWord) (1 :: sw.map ratOfWord) δ E a (b :: rest) = true)
    (hbd : boundsOk (rw.map ratOfWord) (1 :: sw.map ratOfWord) ρ a (b :: rest) = true)
    (hδ : (2 + 1 / 2 ^ 40) * 𝐮 / lo ^ 2 ≤ δ) (ha : (a : ℝ) ≤ 1 / hi ^ 2 - δ)
    (hl : 1 / lo ^ 2 + δ ≤ (lastD a (b :: rest) : ℝ)) :
    FApprox (hornerF (rw.map Float.ofBits) (1.0 / (x * x)) /
        hornerF (1.0 :: sw.map Float.ofBits) (1.0 / (x * x)))
      (eval (rw.map ratOfWord) (1 / value x.toBits ^ 2) /
        eval (1 :: sw.map ratOfWord) (1 / value x.toBits ^ 2)) E ∧
    0 < eval (1 :: sw.map ratOfWord) (1 / value x.toBits ^ 2) ∧
    |eval (rw.map ratOfWord) (1 / value x.toBits ^ 2)| ≤
      ρ * eval (1 :: sw.map ratOfWord) (1 / value x.toBits ^ 2) := by
  set v := value x.toBits with hv
  have hlo0 : 0 < lo := by linarith
  have hv0 : 0 < v := by linarith
  have hz := recip_sq x hxf (h2.trans hlo) (hhi.trans hb)
  have hsq1 : lo ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hlo0.le hlo 2
  have hsq2 : v ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ hv0.le hhi 2
  have hinv1 : 1 / v ^ 2 ≤ 1 / lo ^ 2 := one_div_le_one_div_of_le (by positivity) hsq1
  have hinv2 : 1 / hi ^ 2 ≤ 1 / v ^ 2 := one_div_le_one_div_of_le (by positivity) hsq2
  have hd : |value (1.0 / (x * x)).toBits - 1 / v ^ 2| ≤ (δ : ℝ) := by
    refine hz.2.trans (le_trans ?_ hδ)
    exact div_le_div_of_nonneg_left (by norm_num [unitRoundoff64]) (by positivity) hsq1
  have hd' := abs_le.mp hd
  have hδ0 : (0 : ℝ) ≤ δ := (abs_nonneg _).trans hd
  have hrn : ∀ w ∈ rw, Wasm.IEEE64.isNaN w = false := fun w hw => not_nan_of_finite (hrf w hw)
  have hsn : ∀ w ∈ sw, Wasm.IEEE64.isNaN w = false := fun w hw => not_nan_of_finite (hsf w hw)
  have hone : CodeLib.IEEE64.Finite (0x3FF0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide
  have hws : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ))
      (0x3FF0000000000000 :: sw) (1 :: sw.map ratOfWord) :=
    List.Forall₂.cons ⟨hone, by rw [value_one, Rat.cast_one]⟩ (forall₂_words sw hsf)
  have hsfm : (1.0 :: sw.map Float.ofBits).map Float.toBits = 0x3FF0000000000000 :: sw := by
    rw [List.map_cons, one_bits, map_bits sw hsn]
  have hR : rw.map ratOfWord ≠ [] := by simpa using hrne
  refine ⟨ratio_float _ _ rw (0x3FF0000000000000 :: sw) _ _ (map_bits rw hrn) hsfm
    (forall₂_words rw hrf) hws hR (by simp) _ hz.1 (1 / v ^ 2) δ E a b rest hck hd
    (by linarith) (by linarith), ?_⟩
  exact bounds_sound _ _ ρ (1 / v ^ 2) a (b :: rest) (by simp) hbd (by linarith) (by linarith)

/-- `1 + r/s` with `|R/S| ≤ ρ`. -/
theorem p_of_ratio {r : Float} {ρv E ρ : ℝ} (hr : FApprox r ρv E) (hρ : |ρv| ≤ ρ)
    (hsmall : ρ + E < 1) : FApprox (1.0 + r) (1 + ρv) (E + 𝐮) := by
  have h := fapprox_add_half fapprox_one hr 1022 (by norm_num) (by
    have : |1 + ρv| ≤ 1 + ρ := by
      have := abs_add_le 1 ρv
      rw [abs_one] at this
      linarith
    have h2 : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
    rw [h2]
    linarith)
  refine fmono h (le_of_eq ?_)
  norm_num [unitRoundoff64]

theorem bits_eighth : (0.125 : Float).toBits = 0x3FC0000000000000 := rfl
theorem bits_three_eighths : (0.375 : Float).toBits = 0x3FD8000000000000 := rfl

theorem fapprox_eighth : FApprox 0.125 (1 / 8) 0 := by
  unfold FApprox Approx
  rw [bits_eighth, ← ratOfWord_cast]
  have : ratOfWord 0x3FC0000000000000 = 1 / 8 := by decide +kernel
  rw [this]
  exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by norm_num⟩

theorem fapprox_three_eighths : FApprox 0.375 (3 / 8) 0 := by
  unfold FApprox Approx
  rw [bits_three_eighths, ← ratOfWord_cast]
  have : ratOfWord 0x3FD8000000000000 = 3 / 8 := by decide +kernel
  rw [this]
  exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by norm_num⟩

/-- `(r/s - 1/8)/x` of `j0` and `y0`, for `0 ≤ R/S ≤ ρ ≤ 1/16`. -/
theorem q0_of_ratio {r x : Float} {ρv E ρ lo : ℝ} (hr : FApprox r ρv E) (hxf : Finite x.toBits)
    (h0 : 0 ≤ ρv) (h1 : ρv ≤ ρ) (hρ : ρ ≤ 1 / 16) (hE : E ≤ 1 / 64) (hlo : 2 ≤ lo)
    (hx : lo ≤ value x.toBits) :
    FApprox ((r - 0.125) / x) ((ρv - 1 / 8) / value x.toBits)
      ((E + 𝐮 / 8) / lo + (1 / 8 + (E + 𝐮 / 8)) / lo / 2 ^ 53 + 1 / 2 ^ 1075) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hb : |ρv - 1 / 8| ≤ 1 / 8 := by rw [abs_le]; constructor <;> linarith
  have ht := fapprox_sub_half hr fapprox_eighth 1019 (by norm_num) (by
    have h2 : (2 : ℝ) ^ (53 + 1019) / 2 ^ 1074 = 1 / 4 := by norm_num
    rw [h2]
    linarith)
  have ht' : FApprox (r - 0.125) (ρv - 1 / 8) (E + 𝐮 / 8) :=
    fmono ht (le_of_eq (by rw [hu]; norm_num))
  have hlo0 : 0 < lo := by linarith
  have hd := fapprox_div ht' (fapprox_exact x hxf) (1 / 8) lo hb
    (by rw [abs_of_pos (by linarith)]; exact hx) (by linarith) _ le_rfl (by
      rw [sub_zero, div_lt_iff₀ hlo0]
      have : E + 𝐮 / 8 ≤ 1 := by rw [hu]; linarith
      nlinarith [show (1 : ℝ) < 2 ^ 1022 by norm_num])
  refine fmono hd (le_of_eq ?_)
  ring

/-- `(3/8 + r/s)/x` of `j1` and `y1`, for `-ρ ≤ R/S ≤ 0` and `ρ ≤ 1/16`. -/
theorem q1_of_ratio {r x : Float} {ρv E ρ lo : ℝ} (hr : FApprox r ρv E) (hxf : Finite x.toBits)
    (h0 : ρv ≤ 0) (h1 : -ρ ≤ ρv) (hρ : ρ ≤ 1 / 16) (hE : E ≤ 1 / 64) (hlo : 2 ≤ lo)
    (hx : lo ≤ value x.toBits) :
    FApprox ((0.375 + r) / x) ((3 / 8 + ρv) / value x.toBits)
      ((E + 𝐮 / 4) / lo + (3 / 8 + (E + 𝐮 / 4)) / lo / 2 ^ 53 + 1 / 2 ^ 1075) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hb : |3 / 8 + ρv| ≤ 3 / 8 := by rw [abs_le]; constructor <;> linarith
  have ht := fapprox_add_half fapprox_three_eighths hr 1020 (by norm_num) (by
    have h2 : (2 : ℝ) ^ (53 + 1020) / 2 ^ 1074 = 1 / 2 := by norm_num
    rw [h2]
    linarith)
  have ht' : FApprox (0.375 + r) (3 / 8 + ρv) (E + 𝐮 / 4) :=
    fmono ht (le_of_eq (by rw [hu]; norm_num))
  have hlo0 : 0 < lo := by linarith
  have hd := fapprox_div ht' (fapprox_exact x hxf) (3 / 8) lo hb
    (by rw [abs_of_pos (by linarith)]; exact hx) (by linarith) _ le_rfl (by
      rw [sub_zero, div_lt_iff₀ hlo0]
      have : E + 𝐮 / 4 ≤ 1 := by rw [hu]; linarith
      nlinarith [show (1 : ℝ) < 2 ^ 1022 by norm_num])
  refine fmono hd (le_of_eq ?_)
  ring

theorem eval_one_cons (S : List ℚ) (z : ℝ) : eval (1 :: S) z = 1 + z * eval S z := by
  rw [eval_cons, Rat.cast_one]

#print axioms forall₂_words
#print axioms fshift
#print axioms ratio_at
#print axioms p_of_ratio
#print axioms q0_of_ratio
#print axioms q1_of_ratio

end Library.Numerics.Float64.Bessel.BesselPQRange
