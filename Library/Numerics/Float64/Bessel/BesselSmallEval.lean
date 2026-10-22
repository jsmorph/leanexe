import Library.Numerics.Float64.Bessel.BesselPQRange
import Library.Numerics.Float64.Bessel.BesselSmallApprox
import LeanExe.ProofKit.F64NearestDiv
import LeanExe.ProofKit.F64Exact
import LeanExe.ProofKit.PolyCalculus

/-!
Tools for the paths below 2, where the code evaluates fdlibm's polynomials at the computed
`ẑ = x x` and the error bounds come from one interval each.  `sq_near` bounds `ẑ`, `horner_at`
bounds a Horner evaluation at `ẑ` against the polynomial at the real `z` from `F64Horner`'s
`hornerErr` and the Lipschitz bound `magBound (p')` on the interval, and `half_exact` shows that
`x / 2.0` is exact for a positive normal `x` with exponent field at least 2, by
`F64NearestDiv.div_nearest` and the double `x / 2` itself.
-/

namespace Library.Numerics.Float64.Bessel.BesselSmallEval
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyCalculus F64Approx F64HalfUlp F64Horner
  BesselPQEval BesselPQRange BesselCS

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- `x x` with `|x| ≤ M`. -/
theorem sq_near (x : Float) (hxf : Finite x.toBits) (M : ℝ) (hM : |value x.toBits| ≤ M)
    (hMb : M * M < 2 ^ 1022) :
    FApprox (x * x) (value x.toBits ^ 2) (M * M / 2 ^ 53 + 1 / 2 ^ 1075) := by
  have hx := fapprox_exact x hxf
  have h := fapprox_mul hx hx M M hM hM (M * M) (by simp) hMb
  exact fmono (fcongr h (by ring)) (le_of_eq (by ring))

/-- A Horner evaluation at a computed argument, against the polynomial at the real argument. -/
theorem horner_at (fl : List Float) (wl : List UInt64) (cs : List ℚ)
    (hfl : fl.map Float.toBits = wl)
    (hrel : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) wl cs)
    (hne : cs ≠ []) (lo hi : ℚ) (hok : hornerOK cs lo hi = true) (zf : Float)
    (hzf : Finite zf.toBits) (z δ : ℝ) (h1 : (lo : ℝ) ≤ value zf.toBits)
    (h2 : value zf.toBits ≤ hi) (h3 : (lo : ℝ) ≤ z) (h4 : z ≤ hi)
    (hδ : |value zf.toBits - z| ≤ δ) :
    FApprox (hornerF fl zf) (eval cs z)
      (hornerErr cs lo hi + magBound (derivP cs) lo hi * δ) := by
  unfold FApprox
  rw [hornerF_bits, hfl]
  have ha := hornerW_approx cs wl hrel hne lo hi zf.toBits hzf h1 h2 hok
  have hder : ∀ t ∈ Set.Icc (lo : ℝ) hi,
      HasDerivWithinAt (eval cs) (eval (derivP cs) t) (Set.Icc (lo : ℝ) hi) t :=
    fun t _ => (hasDerivAt_eval cs t).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc (lo : ℝ) hi, ‖eval (derivP cs) t‖ ≤ magBound (derivP cs) lo hi := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact magBound_sound _ lo hi t ht.1 ht.2
  have hl := (convex_Icc (lo : ℝ) hi).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    ⟨h3, h4⟩ ⟨h1, h2⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hl
  have hM0 : (0 : ℝ) ≤ magBound (derivP cs) lo hi := (abs_nonneg _).trans (hbound z ⟨h3, h4⟩)
  have hL := mul_le_mul_of_nonneg_left hδ hM0
  refine ⟨ha.1, ?_⟩
  have := abs_sub_le (value (hornerW wl zf.toBits)) (eval cs (value zf.toBits)) (eval cs z)
  linarith [ha.2]

theorem words_rel (ws : List UInt64) (hw : ∀ w ∈ ws, Finite w) :
    (ws.map Float.ofBits).map Float.toBits = ws ∧
      List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) ws
        (ws.map ratOfWord) :=
  ⟨map_bits ws fun w h => not_nan_of_finite (hw w h), forall₂_words ws hw⟩

theorem words_rel_one (ws : List UInt64) (hw : ∀ w ∈ ws, Finite w) :
    (1.0 :: ws.map Float.ofBits).map Float.toBits = 0x3FF0000000000000 :: ws ∧
      List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ))
        (0x3FF0000000000000 :: ws) (1 :: ws.map ratOfWord) := by
  refine ⟨by rw [List.map_cons, one_bits, map_bits ws fun w h => not_nan_of_finite (hw w h)], ?_⟩
  exact List.Forall₂.cons ⟨by unfold CodeLib.IEEE64.Finite; decide, by rw [value_one, Rat.cast_one]⟩
    (forall₂_words ws hw)

/-- `x / 2.0` is exact for a positive normal `x` whose exponent field is at least 2. -/
theorem half_exact (x : Float) (hxf : Finite x.toBits) (hs : Wasm.IEEE64.sign x.toBits = false)
    (he : 2 ≤ Wasm.IEEE64.exponent x.toBits) (hx : value x.toBits < 2 ^ 1000) :
    Finite (x / 2.0).toBits ∧ value (x / 2.0).toBits = value x.toBits / 2 := by
  have h2 : (2.0 : Float).toBits = 0x4000000000000000 := rfl
  have h2f : Finite (0x4000000000000000 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
  have h2v : value (0x4000000000000000 : UInt64) = 2 := by
    rw [← ratOfWord_cast]
    have : ratOfWord 0x4000000000000000 = 2 := by decide +kernel
    rw [this]; norm_num
  set e := Wasm.IEEE64.exponent x.toBits
  set f := Wasm.IEEE64.fraction x.toBits
  have hf : f < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hfin : e < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : e < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hv := F64Magnitude.normal_value x.toBits hs (by omega)
  set w := Wasm.IEEE64.encodeFinite false (e - 1) f
  have hwe := F64Source.exponent_encodeFinite false (e - 1) f (by omega) hf
  have hwf := F64Source.fraction_encodeFinite false (e - 1) f (by omega) hf
  have hws := F64Source.sign_encodeFinite false (e - 1) f (by omega) hf
  have hwv := F64Magnitude.normal_value w hws (by rw [hwe]; omega)
  rw [hwe, hwf] at hwv
  have hval : value w = value x.toBits / 2 := by
    rw [hwv, hv]
    have : (2 : ℝ) ^ (e - 1) = 2 * 2 ^ (e - 1 - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this]
    ring
  have hvpos : 0 < value x.toBits := by
    rw [hv]; positivity
  have hn := F64NearestDiv.div_nearest x.toBits 0x4000000000000000 hxf h2f hs (by decide)
    (by
      rw [h2v]
      have : (1 : ℝ) / 2 ^ 1022 ≤ value x.toBits / 2 := by
        rw [hv]
        have h1 : (2 : ℝ) ^ 52 * 2 ^ 1 ≤ ((2 : ℝ) ^ 52 + f) * 2 ^ (e - 1) := by
          apply mul_le_mul (by linarith [show (0 : ℝ) ≤ f by positivity]) _ (by positivity)
            (by positivity)
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        rw [div_div, le_div_iff₀ (by positivity)]
        have : (1 : ℝ) / 2 ^ 1022 * (2 ^ 1074 * 2) = 2 ^ 53 := by norm_num
        nlinarith
      exact this)
    (by rw [h2v]; linarith)
  rw [h2v] at hn
  obtain ⟨hnf, -⟩ := F64NearestNonnegative.nearest_finite _ _ hn
  have hwlt : w.toNat < F64NearestNonnegative.limit := by
    have hw : w.toNat = (e - 1) * 2 ^ 52 + f := by
      simp only [w, Wasm.IEEE64.encodeFinite, Bool.false_eq_true, ite_false, zero_add]
      rw [UInt64.toNat_ofNat_of_lt']
      calc (e - 1) * 2 ^ 52 + f < 2047 * 2 ^ 52 := by
            have : (e - 1) * 2 ^ 52 ≤ 2045 * 2 ^ 52 := Nat.mul_le_mul_right _ (by omega)
            omega
        _ < 2 ^ 64 := by norm_num
    rw [hw, F64NearestNonnegative.limit]
    have : (e - 1) * 2 ^ 52 ≤ 2045 * 2 ^ 52 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hc := hn.2 w hwlt
  rw [hval, sub_self, abs_zero] at hc
  have h0 := abs_nonpos_iff.mp hc
  rw [F64Bits.toBits_div, h2]
  exact ⟨hnf, sub_eq_zero.mp h0⟩

#print axioms sq_near
#print axioms horner_at
#print axioms half_exact

end Library.Numerics.Float64.Bessel.BesselSmallEval
