import Library.Numerics.Float64.Sinh.SinhMidCases
import Library.Numerics.Float64.Sinh.SinhSmallCases
import Library.Numerics.Float64.Sinh.SinhLdexp
import Library.Numerics.Float64.Sinh.SinhOverflow
import Library.Numerics.Float64.Tanh.TanhTheorem

/-!
The ranges of `Sinh.sinh` outside `[2 ^ -28, 22)`.  Below `2 ^ -28` the code returns `x`, within
`4/3 abs(x) ^ 3` of `sinh x` (`sinh_cubic`, `tiny_sinh`).  From 22 to `709.7822265625` it returns
`± 0.5 exp abs(x)`, the half of `exp` from `CoshLarge`, within one step (`sinh_large`).  Up to
`710.47607421875` it returns `± 1 · ldexpExp abs(x)`, where the product with `±1` is exact
(`sinh_ldexp`), and above it returns `x · 1.0e+307`, the infinity of the sign of `x`, beyond the
overflow threshold of `sinh` (`sinh_overflow`).  Each range states the results for `h = 0.5`
and for `h = -0.5`.
-/

namespace Library.Numerics.Float64.Sinh.SinhRanges
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative SinhWords

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

/-- `abs(sinh a - a) ≤ 4/3 a ^ 3` for `0 ≤ a ≤ 2 ^ -28`. -/
theorem sinh_cubic (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1 / 2 ^ 28) :
    |a - Real.sinh a| ≤ 4 / 3 * a ^ 3 := by
  have h1 := Real.exp_bound (x := a) (by rw [abs_of_nonneg ha]; linarith) (n := 3) (by norm_num)
  have h2 := Real.exp_bound (x := -a) (by rw [abs_neg, abs_of_nonneg ha]; linarith) (n := 3)
    (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2
  norm_num at h1 h2
  rw [abs_of_nonneg ha] at h1
  rw [abs_of_nonneg ha] at h2
  obtain ⟨h11, h12⟩ := abs_le.mp h1
  obtain ⟨h21, h22⟩ := abs_le.mp h2
  rw [Real.sinh_eq, abs_le]
  have : 0 ≤ a ^ 3 := by positivity
  constructor <;> nlinarith

/-- Below `2 ^ -28`: the word `x` itself. -/
theorem tiny_sinh (w : UInt64) (hwf : Finite w) (hx : |value w| < 1 / 2 ^ 28) :
    F64SignedRounding.WithinSteps 1 (Real.sinh (value w)) w := by
  rcases lt_trichotomy (value w) 0 with hneg | hz | hpos
  · obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value w hwf
    have hns : Wasm.IEEE64.sign (Wasm.IEEE64.negate w) = false :=
      Library.Numerics.Float64.Tanh.TanhSmall.sign_of_pos _ (by rw [hnv]; linarith)
    have hc := Library.Numerics.Float64.Tanh.Expm1PathsEdge.nearest_self _ (F64Magnitude.lt_limit_of_finite _ hnf hns)
    rw [abs_of_neg hneg] at hx
    have h := Library.Numerics.Float64.Tanh.TanhTheorem.tiny_core _ _ hc (Real.sinh (-value w)) (by rw [hnv]; linarith)
      (by rw [hnv]; exact hx) (by rw [hnv]; exact sinh_cubic _ (by linarith) hx.le)
    rw [Real.sinh_neg] at h
    have h' := (F64SignedRounding.within_negate 1 _ _).mpr h
    rwa [neg_neg, F64RelativeStep.negate_negate] at h'
  · have hm : Wasm.IEEE64.scaledMagnitude w = 0 := by
      have h := Library.Numerics.Float64.Tanh.Expm1PathsEdge.abs_value w
      rw [hz, abs_zero] at h
      have : (Wasm.IEEE64.scaledMagnitude w : ℝ) = 0 := by
        have h74 : (0 : ℝ) < 2 ^ 1074 := by positivity
        field_simp at h
        linarith
      exact_mod_cast this
    rw [hz, Real.sinh_zero, F64Convert.zero_encoding _ hm]
    cases Wasm.IEEE64.sign w
    · exact Library.Numerics.Float64.Tanh.Expm1PathsEdge.zero_within _ (Or.inl (by decide +kernel))
    · exact Library.Numerics.Float64.Tanh.Expm1PathsEdge.zero_within _ (Or.inr (by decide +kernel))
  · have hs := Library.Numerics.Float64.Tanh.TanhSmall.sign_of_pos w hpos
    have hc := Library.Numerics.Float64.Tanh.Expm1PathsEdge.nearest_self _ (F64Magnitude.lt_limit_of_finite _ hwf hs)
    rw [abs_of_pos hpos] at hx
    exact Library.Numerics.Float64.Tanh.TanhTheorem.tiny_core _ _ hc _ hpos.le hx (sinh_cubic _ hpos.le hx.le)

theorem sinh_half (A : ℝ) :
    |Real.sinh A - Real.exp A / 2| ≤ Real.exp (-A) / 2 := by
  rw [Real.sinh_eq, show (Real.exp A - Real.exp (-A)) / 2 - Real.exp A / 2 =
    -(Real.exp (-A) / 2) by ring, abs_neg, abs_of_pos (by positivity)]

/-- From 22 to `709.7827`: `± 0.5 exp abs(x)`. -/
theorem sinh_large (x : Float) (hxf : Finite x.toBits) (hlo : 22 ≤ |value x.toBits|)
    (hhi : |value x.toBits| ≤ 7097827 / 10 ^ 4) :
    F64SignedRounding.WithinSteps 1 (Real.sinh |value x.toBits|)
      (0.5 * Exp.exp x.abs).toBits ∧
    F64SignedRounding.WithinSteps 1 (-Real.sinh |value x.toBits|)
      (-0.5 * Exp.exp x.abs).toBits := by
  have hu : u = 1 / 2 ^ 53 := rfl
  obtain ⟨V, hn, hV⟩ := CoshLarge.half_exp_near x hxf hlo hhi
  obtain ⟨haf, hav⟩ := abs_float x hxf
  obtain ⟨hTf, hTe⟩ := Library.Numerics.Float64.Exp.ExpTightFloat.exp_relative x.abs haf (by rw [hav]; linarith)
    (by rw [hav]; exact hhi)
  rw [hav] at hTe
  have hE1 : 1 ≤ Real.exp |value x.toBits| := Real.one_le_exp (by linarith)
  have hTlo : 1 / 2 ^ 1021 ≤ value (Exp.exp x.abs).toBits := by
    obtain ⟨h1, -⟩ := abs_le.mp hTe
    rw [hu] at h1
    have : (1 : ℝ) / 2 ^ 1021 ≤ 1 / 2 := by norm_num
    nlinarith
  rw [F64Bits.toBits_mul, F64Bits.toBits_mul, half_bits, SinhSign.neg_half_bits,
    SinhSign.mul_negHalf _ hTf hTlo, F64SignedRounding.within_negate, and_self]
  exact CoshLarge.large_within _ _ V _ hlo hhi (sinh_half _) hn hV

theorem one_mul_inf : Wasm.IEEE64.mul 0x3FF0000000000000 0x7FF0000000000000 =
    0x7FF0000000000000 := by decide +kernel

theorem negOne_mul_inf : Wasm.IEEE64.mul 0xBFF0000000000000 0x7FF0000000000000 =
    Wasm.IEEE64.negate 0x7FF0000000000000 := by decide +kernel

theorem half_two_bits : (0.5 * 2.0 : Float).toBits = 0x3FF0000000000000 := by
  rw [F64Bits.toBits_mul, half_bits, Library.Numerics.Float64.Tanh.TanhTheorem.two_bits]; decide +kernel

theorem neg_half_two_bits : (-0.5 * 2.0 : Float).toBits = 0xBFF0000000000000 := by
  rw [F64Bits.toBits_mul, SinhSign.neg_half_bits, Library.Numerics.Float64.Tanh.TanhTheorem.two_bits]; decide +kernel

/-- From `709.7822265625` to `710.47607421875`: `± 1 · ldexpExp abs(x)`. -/
theorem sinh_ldexp (x : Float) (hxf : Finite x.toBits)
    (hlo : 7097822265625 / 10 ^ 10 ≤ |value x.toBits|)
    (hhi : |value x.toBits| ≤ 71047607421875 / 10 ^ 11) :
    F64SignedRounding.WithinSteps 1 (Real.sinh |value x.toBits|)
      (0.5 * 2.0 * Sinh.ldexpExp Exp.expTable x.abs (0 - 1)).toBits ∧
    F64SignedRounding.WithinSteps 1 (-Real.sinh |value x.toBits|)
      (-0.5 * 2.0 * Sinh.ldexpExp Exp.expTable x.abs (0 - 1)).toBits := by
  obtain ⟨hw, hshape⟩ := SinhLdexp.ldexp_within x hxf hlo hhi _ (sinh_half _)
  rw [F64Bits.toBits_mul, F64Bits.toBits_mul (-0.5 * 2.0), half_two_bits, neg_half_two_bits]
  generalize (Sinh.ldexpExp Exp.expTable x.abs (0 - 1)).toBits = c at hw hshape ⊢
  rcases hshape with h | ⟨hcf, hcv⟩
  · subst h
    rw [one_mul_inf, negOne_mul_inf, F64SignedRounding.within_negate, and_self]
    exact hw
  · rw [SinhSign.mul_one_left c hcf hcv, SinhSign.mul_negOne c hcf hcv,
      F64SignedRounding.within_negate, and_self]
    exact hw

/-- From `710.47607421875` on: `x · 1.0e+307`, the infinity of the sign of `x`. -/
theorem sinh_overflow (x : Float) (hxf : Finite x.toBits)
    (hlo : 71047607421875 / 10 ^ 11 ≤ |value x.toBits|) :
    F64SignedRounding.WithinSteps 1 (Real.sinh (value x.toBits))
      (x * Float.ofBits 0x7FAC7B1F3CAC7433).toBits := by
  have hb : (Float.ofBits 0x7FAC7B1F3CAC7433).toBits = 0x7FAC7B1F3CAC7433 := by
    rw [F64Bits.toBits_ofBits]; decide +kernel
  rw [F64Bits.toBits_mul, hb, SinhOverflow.mul_shuge _ hxf (by linarith)]
  -- `sinh abs(x)` lies above the overflow threshold.
  have hth : F64PositiveRounding.overflowThreshold ≤ Real.sinh |value x.toBits| := by
    have hl := Library.Numerics.Float64.Exp.ExpTight.log_two_bounds.2
    have e := Library.Numerics.Float64.Exp.ExpTightFloat.exp_two_pow 1025
    push_cast at e
    have h1 : Real.exp (1025 * Real.log 2) ≤ Real.exp |value x.toBits| :=
      Real.exp_le_exp.mpr (by linarith)
    rw [e] at h1
    have h2 := sinh_half |value x.toBits|
    have h3 : Real.exp (-|value x.toBits|) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := abs_nonneg (value x.toBits); linarith)
    have h4 := (abs_le.mp h2).1
    have hthr : F64PositiveRounding.overflowThreshold = 2 ^ 1024 - 2 ^ 970 := rfl
    rw [hthr]
    have : (2 : ℝ) ^ 1024 - 2 ^ 970 + 1 ≤ 2 ^ 1025 / 2 := by norm_num
    linarith
  have hpos : 0 ≤ Real.sinh |value x.toBits| := le_trans (by
    unfold F64PositiveRounding.overflowThreshold; norm_num) hth
  have hr := F64PositiveRounding.reference_overflow _ hth
  have hinf : F64SignedRounding.WithinSteps 1 (Real.sinh |value x.toBits|) 0x7FF0000000000000 :=
    F64SignedRounding.within_of_nonneg 1 _ hpos _ (by decide)
      (by rw [hr]; unfold F64PositiveRounding.positiveInfinity; omega)
      (by rw [hr]; unfold F64PositiveRounding.positiveInfinity; omega)
  have hX0 : 0 < |value x.toBits| := lt_of_lt_of_le (by norm_num) hlo
  cases hs : Wasm.IEEE64.sign x.toBits
  · have hpos' := Library.Numerics.Float64.Tanh.Expm1Theorem.pos_of_sgn x.toBits (by rw [Library.Numerics.Float64.Tanh.Expm1Branches.sgn_iff]; exact hs) hX0
    rw [abs_of_pos hpos'] at hinf
    exact hinf
  · have hneg := Library.Numerics.Float64.Tanh.Expm1Theorem.neg_of_sgn x.toBits (by rw [Library.Numerics.Float64.Tanh.Expm1Branches.sgn_iff]; exact hs) hX0
    rw [abs_of_neg hneg, Real.sinh_neg] at hinf
    have h := (F64SignedRounding.within_negate 1 _ _).mpr hinf
    rw [neg_neg] at h
    rw [show Wasm.IEEE64.infinity true = Wasm.IEEE64.negate 0x7FF0000000000000 by decide +kernel]
    exact h

#print axioms sinh_cubic
#print axioms tiny_sinh
#print axioms sinh_large
#print axioms sinh_ldexp
#print axioms sinh_overflow

end Library.Numerics.Float64.Sinh.SinhRanges
