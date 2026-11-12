import Library.Numerics.Fourier.Compiled
import Library.Numerics.Float64.Trig.TrigSinCos
import Library.Numerics.Reductions.Binary64
import LeanExe.ProofKit.F64Compose

/-!
The accuracy of `twiddle n m`, the pair `(cos θ, sin θ)` of `Trig` at the rounded angle
`θ = 6.283185307179586 ⊗ (m ⊘ n)`.  `within_abs` turns one step of the nearest-even reference of a
number `y` with `|y| ≤ 1` into an absolute error of at most `5 · 2 ^ -53`: two and a half spacings
of `y`'s binade by `F64Compose.error_of_within`, and a few subnormal steps below `2 ^ -1021`.
`angle_error` bounds the error of the rounded angle by `19 · 2 ^ -53 + 2 ^ -1072` for
`0 ≤ m < n ≤ 2 ^ 53`, from the two roundings and `|6.283185307179586 - 2 π| < 2 ^ -51`.  Since
`cos` and `sin` are 1-Lipschitz, each component of the twiddle lies within `2 ^ -48` of
`cos (2 π m / n)` and `sin (2 π m / n)`.
-/

namespace Library.Numerics.Fourier

open CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.F64Approx
open Library.Numerics.Reductions.Binary64

set_option exponentiation.threshold 4096

/-! ### One step as an absolute error -/

theorem value_negate (w : UInt64) : value (Wasm.IEEE64.negate w) = -value w := by
  have he : Wasm.IEEE64.exponent w < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
  have hf : Wasm.IEEE64.fraction w < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  have hm : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.negate w) = Wasm.IEEE64.scaledMagnitude w := by
    unfold Wasm.IEEE64.negate
    rw [scaledMagnitude_encodeFinite _ _ _ he hf]
    simp [Wasm.IEEE64.scaledMagnitude]
  have hs : Wasm.IEEE64.sign (Wasm.IEEE64.negate w) = !Wasm.IEEE64.sign w := by
    unfold Wasm.IEEE64.negate
    exact sign_encodeFinite _ _ _ he hf
  have hsv : Wasm.IEEE64.scaledValue (Wasm.IEEE64.negate w) = -Wasm.IEEE64.scaledValue w := by
    show (if Wasm.IEEE64.sign (Wasm.IEEE64.negate w) then
        -(Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.negate w) : Int) else
        (Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.negate w) : Int)) =
      -(if Wasm.IEEE64.sign w then -(Wasm.IEEE64.scaledMagnitude w : Int) else
        (Wasm.IEEE64.scaledMagnitude w : Int))
    rw [hm, hs]
    cases Wasm.IEEE64.sign w <;> simp
  rw [value, value, hsv]
  push_cast
  ring

/-- One step of the reference of a number in `[0, 2 ^ -1021)` lies within `2 ^ -1019` of it. -/
theorem within_tiny (y : ℝ) (w : UInt64) (h : F64SignedRounding.WithinSteps 1 y w)
    (hy0 : 0 ≤ y) (hy : y < 2 ^ 53 / 2 ^ 1074) : |value w - y| ≤ 2 ^ 54 / 2 ^ 1074 := by
  have hlim : F64NearestNonnegative.limit = 2047 * 2 ^ 52 := rfl
  have hyt : y < F64PositiveRounding.overflowThreshold := by
    have : (2 : ℝ) ^ 53 / 2 ^ 1074 < F64PositiveRounding.overflowThreshold := by
      rw [show F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - 2 ^ 970 from rfl]
      norm_num
    linarith
  set r := F64PositiveRounding.roundNearestEven y with hr
  have hrn : F64NearestNonnegative.Nearest y r := by
    rw [hr, F64PositiveRounding.reference_finite y hyt]
    exact (F64NearestEven.roundNearestEven_spec y).1
  have hb2 := F64PositiveSpacing.boundary_value 2 (by norm_num) (by norm_num)
  have hb3 := F64PositiveSpacing.boundary_value 3 (by norm_num) (by norm_num)
  have hofNat : ∀ k : ℕ, k < 2 ^ 63 → (UInt64.ofNat k).toNat = k := fun k hk =>
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hint := F64PositiveOrder.nearest_interval y r 0 (UInt64.ofNat (2 * 2 ^ 52)) hrn
    (by rw [hlim]; decide) (by rw [hofNat _ (by norm_num), hlim]; norm_num)
    (by rw [value_zero]; exact hy0) (by rw [hb2]; norm_num at hy ⊢; linarith)
  rw [hofNat _ (by norm_num)] at hint
  have hpr : F64SignedRounding.position (F64SignedRounding.roundNearestEven y) = r.toNat := by
    have href : F64SignedRounding.roundNearestEven y = r := by
      simp only [F64SignedRounding.roundNearestEven, hy0, ite_true, hr]
    rw [href, F64SignedRounding.position_of_lt r (by omega)]
  have hpos := h.2
  rw [hpr] at hpos
  have hpos' := abs_le.mp hpos
  by_cases hs : Wasm.IEEE64.sign w = true
  · -- a negative zero or the negative least subnormal
    have hge : 2 ^ 63 ≤ w.toNat := by simpa [Wasm.IEEE64.sign] using hs
    have hp : F64SignedRounding.position w = -((w.toNat - 2 ^ 63 : ℕ) : ℤ) := by
      simp only [F64SignedRounding.position, hs, ite_true]
    rw [hp] at hpos'
    have hw1 : w.toNat - 2 ^ 63 ≤ 1 := by omega
    have hmag : Wasm.IEEE64.scaledMagnitude w ≤ 1 := by
      have hwl := w.toNat_lt
      have he : Wasm.IEEE64.exponent w = 0 := by
        show w.toNat / 2 ^ 52 % 2 ^ 11 = 0
        omega
      have hf : Wasm.IEEE64.fraction w ≤ 1 := by
        show w.toNat % 2 ^ 52 ≤ 1
        omega
      unfold Wasm.IEEE64.scaledMagnitude
      simp only [he, beq_self_eq_true, ↓reduceIte]
      exact hf
    have hav := F64RoundNearest.abs_value w
    have hv : |value w| ≤ 1 / 2 ^ 1074 := by
      rw [hav]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmag) (by positivity)
    have hv' := abs_le.mp hv
    have hc : (1 : ℝ) / 2 ^ 1074 + 2 ^ 53 / 2 ^ 1074 ≤ 2 ^ 54 / 2 ^ 1074 := by norm_num
    rw [abs_le]
    constructor <;> linarith
  · have hs' : Wasm.IEEE64.sign w = false := by simpa using hs
    have hlt : w.toNat < 2 ^ 63 := by
      have : ¬ 2 ^ 63 ≤ w.toNat := by simpa [Wasm.IEEE64.sign] using hs'
      omega
    rw [F64SignedRounding.position_of_lt w hlt] at hpos'
    have hw3 : w.toNat ≤ 3 * 2 ^ 52 := by omega
    have hv : value w ≤ 2 ^ 54 / 2 ^ 1074 := by
      calc value w ≤ value (UInt64.ofNat (3 * 2 ^ 52)) :=
            (F64PositiveOrder.value_le_iff hlt (by rw [hofNat _ (by norm_num)]; norm_num)).mpr
              (by rw [hofNat _ (by norm_num)]; omega)
        _ = 2 ^ 54 / 2 ^ 1074 := by rw [hb3]
    have hv0 : 0 ≤ value w := by
      have h0 := (F64PositiveOrder.value_le_iff (left := 0) (by decide) hlt).mpr (by simp)
      rwa [value_zero] at h0
    rw [abs_le]
    constructor <;> linarith

/-- A word within one step of the nearest-even reference of `y`, with `|y| ≤ 1`, lies within
`5 · 2 ^ -53` of `y`. -/
theorem within_abs_nonneg (y : ℝ) (w : UInt64) (h : F64SignedRounding.WithinSteps 1 y w)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : |value w - y| ≤ 5 / 2 ^ 53 := by
  by_cases ht : y < 2 ^ 53 / 2 ^ 1074
  · exact (within_tiny y w h hy0 ht).trans (by norm_num)
  · push Not at ht
    set t := y * 2 ^ 1074 with htdef
    have ht53 : (2 : ℝ) ^ 53 ≤ t := by
      rw [htdef]; rwa [div_le_iff₀ (by positivity)] at ht
    have ht1 : t ≤ 2 ^ 1074 := by
      rw [htdef]; nlinarith [show (0 : ℝ) < 2 ^ 1074 by positivity]
    set N := ⌊t⌋₊ with hN
    have hN53 : 2 ^ 53 ≤ N := Nat.le_floor (by exact_mod_cast ht53)
    have hN1 : N ≤ 2 ^ 1074 := by
      have h1 := Nat.floor_le (show 0 ≤ t by linarith)
      have h2 : (N : ℝ) ≤ 2 ^ 1074 := by rw [hN]; linarith
      exact_mod_cast h2
    have hN0 : N ≠ 0 := by positivity
    set k := Nat.log 2 N with hk
    have hk1 : 2 ^ k ≤ N := Nat.pow_log_le_self 2 hN0
    have hk2 : N < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
    have hk53 : 53 ≤ k := Nat.le_log_of_pow_le (by norm_num) hN53
    have hk1074 : k ≤ 1074 := (Nat.pow_le_pow_iff_right (by norm_num)).mp (hk1.trans hN1)
    have htk1 : (2 : ℝ) ^ k ≤ t := by
      have : ((2 ^ k : ℕ) : ℝ) ≤ N := by exact_mod_cast hk1
      have := Nat.floor_le (show 0 ≤ t by linarith)
      push_cast at *
      linarith
    have htk2 : t < 2 ^ (k + 1) := by
      have h1 := Nat.lt_floor_add_one t
      have h2 : ((N + 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hk2
      push_cast at h2
      linarith
    set n := k - 51 with hn
    have hnk : n + 51 = k := by omega
    have he := (F64Compose.error_of_within y w h n (by omega) (by omega)
      (by rw [hnk, div_le_iff₀ (by positivity)]; exact htk1)
      (by rw [hnk, mul_div_assoc', lt_div_iff₀ (by positivity), ← pow_succ']; exact htk2)).1
    refine he.trans ?_
    have : (2 : ℝ) ^ (n - 1) ≤ 2 ^ 1022 := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : 5 / 2 * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074) ≤ 5 / 2 * (2 ^ 1022 / 2 ^ 1074) := by
      gcongr
    have h3 : 5 / 2 * ((2 : ℝ) ^ 1022 / 2 ^ 1074) = 5 / 2 ^ 53 := by norm_num
    linarith

/-- `within_abs_nonneg` for every `|y| ≤ 1`. -/
theorem within_abs (y : ℝ) (w : UInt64) (h : F64SignedRounding.WithinSteps 1 y w)
    (hy : |y| ≤ 1) : |value w - y| ≤ 5 / 2 ^ 53 := by
  rcases le_or_gt 0 y with hy0 | hy0
  · exact within_abs_nonneg y w h hy0 (le_of_abs_le hy)
  · have h' := (F64SignedRounding.within_negate 1 y w).mpr h
    have := within_abs_nonneg (-y) _ h' (by linarith) (by
      have := abs_le.mp hy; linarith)
    rw [value_negate, show -value w - -y = -(value w - y) by ring, abs_neg] at this
    exact this

/-- A word within one step of a number of magnitude at most 1 is finite. -/
theorem finite_of_within (y : ℝ) (w : UInt64) (h : F64SignedRounding.WithinSteps 1 y w)
    (hy : |y| ≤ 1) : Finite w := by
  have he := within_abs y w h hy
  have hn := h.1
  by_contra hnf
  have hw := w.toNat_lt
  have hex0 : Wasm.IEEE64.exponent w = 2047 := by
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hnf
    simpa using hnf
  have hex : w.toNat / 2 ^ 52 % 2 ^ 11 = 2047 := hex0
  have hf : w.toNat % 2 ^ 52 = 0 := by omega
  have hm : Wasm.IEEE64.scaledMagnitude w = 2 ^ 2098 := by
    unfold Wasm.IEEE64.scaledMagnitude
    rw [hex0, show Wasm.IEEE64.fraction w = 0 from hf]
    norm_num
  have ha := F64RoundNearest.abs_value w
  rw [hm] at ha
  have h3 := abs_sub_abs_le_abs_sub (value w) y
  have : ((2 ^ 2098 : ℕ) : ℝ) / 2 ^ 1074 = 2 ^ 1024 := by norm_num
  rw [this] at ha
  have : (5 : ℝ) / 2 ^ 53 + 1 < 2 ^ 1024 := by norm_num
  linarith

/-! ### The rounded angle -/

theorem twoPi_bits : (6.283185307179586 : Float).toBits = 0x401921FB54442D18 := by
  decide +kernel

theorem twoPi_value : value (6.283185307179586 : Float).toBits = 7074237752028440 / 2 ^ 50 := by
  rw [twoPi_bits]
  have : Wasm.IEEE64.scaledValue 0x401921FB54442D18 = 7074237752028440 * 2 ^ 1024 := by
    decide +kernel
  rw [value, this]
  push_cast
  norm_num

theorem twoPi_close : |(7074237752028440 / 2 ^ 50 : ℝ) - 2 * Real.pi| ≤ 1 / 2 ^ 51 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  rw [abs_le]
  constructor <;> norm_num <;> linarith

/-- The rounded angle `6.283185307179586 ⊗ (m ⊘ n)` lies within `19 · 2 ^ -53 + 2 ^ -1072` of
`2 π m / n` for `m < n ≤ 2 ^ 53`. -/
theorem angle_error (n m : UInt64) (hn0 : 0 < n.toNat) (hmn : m.toNat < n.toNat)
    (hn : n.toNat ≤ 2 ^ 53) :
    FApprox (6.283185307179586 * (m.toFloat / n.toFloat)) (2 * Real.pi * m.toNat / n.toNat)
      (19 / 2 ^ 53 + 1 / 2 ^ 1072) := by
  have hm := toFloat_exact m (by omega)
  have hnf := toFloat_exact n hn
  have hnr : (0 : ℝ) < n.toNat := by exact_mod_cast hn0
  have hmr : (0 : ℝ) ≤ m.toNat := by positivity
  have hmn' : (m.toNat : ℝ) ≤ n.toNat := by exact_mod_cast hmn.le
  have hq := fapprox_div hm hnf (m.toNat : ℝ) (n.toNat : ℝ) (by rw [abs_of_nonneg hmr])
    (by rw [abs_of_pos hnr]) hnr 1 (by rw [sub_zero, add_zero, div_le_one hnr]; exact hmn')
    (by norm_num)
  have hq' : FApprox (m.toFloat / n.toFloat) ((m.toNat : ℝ) / n.toNat)
      (1 / 2 ^ 53 + 1 / 2 ^ 1075) := hq.mono (le_of_eq (by simp))
  have hc : FApprox (6.283185307179586 : Float) (7074237752028440 / 2 ^ 50) 0 := by
    have := approx_self _ (show CodeLib.IEEE64.Finite (6.283185307179586 : Float).toBits by
      rw [twoPi_bits]; unfold CodeLib.IEEE64.Finite; decide)
    rw [twoPi_value] at this
    exact this
  have hρ : |(m.toNat : ℝ) / n.toNat| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_one hnr]; exact hmn'
  have hp := fapprox_mul hc hq' 7 1 (by norm_num) hρ 8 (by norm_num) (by norm_num)
  have hp' : FApprox (6.283185307179586 * (m.toFloat / n.toFloat))
      (7074237752028440 / 2 ^ 50 * ((m.toNat : ℝ) / n.toNat)) (15 / 2 ^ 53 + 8 / 2 ^ 1075) :=
    hp.mono (le_of_eq (by ring))
  refine ⟨hp'.1, ?_⟩
  have hd : |(7074237752028440 / 2 ^ 50 : ℝ) * ((m.toNat : ℝ) / n.toNat) -
      2 * Real.pi * m.toNat / n.toNat| ≤ 1 / 2 ^ 51 := by
    rw [show (7074237752028440 / 2 ^ 50 : ℝ) * ((m.toNat : ℝ) / n.toNat) -
        2 * Real.pi * m.toNat / n.toNat =
        ((7074237752028440 / 2 ^ 50 : ℝ) - 2 * Real.pi) * ((m.toNat : ℝ) / n.toNat) by ring,
      abs_mul]
    calc |(7074237752028440 / 2 ^ 50 : ℝ) - 2 * Real.pi| * |(m.toNat : ℝ) / n.toNat|
        ≤ 1 / 2 ^ 51 * 1 := mul_le_mul twoPi_close hρ (abs_nonneg _) (by norm_num)
      _ = 1 / 2 ^ 51 := by ring
  calc |value (6.283185307179586 * (m.toFloat / n.toFloat)).toBits -
        2 * Real.pi * m.toNat / n.toNat|
      ≤ |value (6.283185307179586 * (m.toFloat / n.toFloat)).toBits -
          7074237752028440 / 2 ^ 50 * ((m.toNat : ℝ) / n.toNat)| +
        |(7074237752028440 / 2 ^ 50 : ℝ) * ((m.toNat : ℝ) / n.toNat) -
          2 * Real.pi * m.toNat / n.toNat| := abs_sub_le _ _ _
    _ ≤ (15 / 2 ^ 53 + 8 / 2 ^ 1075) + 1 / 2 ^ 51 := add_le_add hp'.2 hd
    _ ≤ 19 / 2 ^ 53 + 1 / 2 ^ 1072 := by norm_num

/-! ### The twiddle -/

theorem twiddle_eq (n m : UInt64) :
    twiddle n m = (Library.Numerics.Float64.Trig.cos (6.283185307179586 * (m.toFloat / n.toFloat)),
      Library.Numerics.Float64.Trig.sin (6.283185307179586 * (m.toFloat / n.toFloat))) := rfl

/-- `twiddle n m` for `0 ≤ m < n ≤ 2 ^ 53`: two finite floats within `2 ^ -48` of
`cos (2 π m / n)` and `sin (2 π m / n)`. -/
theorem twiddle_spec (n m : UInt64) (hn0 : 0 < n.toNat) (hmn : m.toNat < n.toNat)
    (hn : n.toNat ≤ 2 ^ 53) :
    Finite (twiddle n m).1.toBits ∧ Finite (twiddle n m).2.toBits ∧
      |value (twiddle n m).1.toBits - Real.cos (2 * Real.pi * m.toNat / n.toNat)| ≤ 1 / 2 ^ 48 ∧
      |value (twiddle n m).2.toBits - Real.sin (2 * Real.pi * m.toNat / n.toNat)| ≤ 1 / 2 ^ 48 := by
  have ha := angle_error n m hn0 hmn hn
  set θ := 6.283185307179586 * (m.toFloat / n.toFloat)
  have hc := Library.Numerics.Float64.Trig.TrigSinCos.cos_within θ ha.1
  have hs := Library.Numerics.Float64.Trig.TrigSinCos.sin_within θ ha.1
  have hc1 := within_abs _ _ hc (Real.abs_cos_le_one _)
  have hs1 := within_abs _ _ hs (Real.abs_sin_le_one _)
  have hcl := Real.abs_cos_sub_cos_le (value θ.toBits) (2 * Real.pi * m.toNat / n.toNat)
  have hsl := Real.abs_sin_sub_sin_le (value θ.toBits) (2 * Real.pi * m.toNat / n.toNat)
  have hθ := ha.2
  have hb : (5 : ℝ) / 2 ^ 53 + (19 / 2 ^ 53 + 1 / 2 ^ 1072) ≤ 1 / 2 ^ 48 := by norm_num
  rw [twiddle_eq]
  refine ⟨finite_of_within _ _ hc (Real.abs_cos_le_one _),
    finite_of_within _ _ hs (Real.abs_sin_le_one _), ?_, ?_⟩
  · calc _ ≤ |value (Library.Numerics.Float64.Trig.cos θ).toBits - Real.cos (value θ.toBits)| +
          |Real.cos (value θ.toBits) - Real.cos (2 * Real.pi * m.toNat / n.toNat)| :=
          abs_sub_le _ _ _
      _ ≤ 1 / 2 ^ 48 := by linarith
  · calc _ ≤ |value (Library.Numerics.Float64.Trig.sin θ).toBits - Real.sin (value θ.toBits)| +
          |Real.sin (value θ.toBits) - Real.sin (2 * Real.pi * m.toNat / n.toNat)| :=
          abs_sub_le _ _ _
      _ ≤ 1 / 2 ^ 48 := by linarith

end Library.Numerics.Fourier
