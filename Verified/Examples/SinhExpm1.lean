import Verified.Examples.Expm1NearPos
import Verified.Examples.Expm1Theorem
import Verified.Examples.Expm1Near
import Verified.Examples.ExpTightFloat

/-!
`Tanh.expm1` on the positive arguments of `sinh` from `θ1 ≈ 0.3466` to 22, with the error of the
exact value before the last rounding.  On the path `k = 1`, up to `θ2 ≈ 1.0397`, the result is a
nearest word to a real `S` within `0.4802 u + 3 η + 2 · 2 ^ -55` of `exp x - 1`, and within
`0.4802 u + 3 η + 2 · 2 ^ -56` when `exp x - 1 ≤ 1.49` (`near_one_pos`).  From `θ2` to 22 the result
lies within `u S` of a positive `S` within `1.9604 u`, or within `0.85 u (exp x - 1)`, of
`exp x - 1` (`near_k_pos`).  Below `0.443` the path `k = 1` takes the form for `x < -1/4`, whose
bound is `0.4802 u`.
-/

namespace Verified.Examples.SinhExpm1
open CodeLib.IEEE64 LeanExe.ProofKit Expm1Branches Expm1ReduceConst Expm1PathsReduced
  Expm1Theorem F64NearestNonnegative

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

theorem sgn_false (x : Float) (hpos : 0 < value x.toBits) : sgn x.toBits = false := by
  cases hs : sgn x.toBits
  · rfl
  · exact absurd (neg_of_sgn x.toBits hs (by rw [abs_of_pos hpos]; exact hpos)) (by linarith)

theorem near_one_pos (x : Float) (hxf : Finite x.toBits)
    (hlo : value (UInt64.ofNat (1071001155 * 2 ^ 32)) ≤ value x.toBits)
    (hhi : value x.toBits < value (UInt64.ofNat (1072734898 * 2 ^ 32))) :
    ∃ S : ℝ, Nearest S (Tanh.expm1 x).toBits ∧
      |S - (Real.exp (value x.toBits) - 1)| ≤ 4802 / 10000 * u + 3 * η + 2 * (1 / 2 ^ 55) ∧
      (Real.exp (value x.toBits) - 1 ≤ 149 / 100 →
        |S - (Real.exp (value x.toBits) - 1)| ≤ 4802 / 10000 * u + 3 * η + 2 * (1 / 2 ^ 56)) ∧
      (value x.toBits < 4430 / 10000 →
        |S - (Real.exp (value x.toBits) - 1)| ≤ 4802 / 10000 * u) := by
  obtain ⟨hθ1, -, -, hθ2, -⟩ := Expm1Near.threshold_bounds
  set θ1 := value (UInt64.ofNat (1071001155 * 2 ^ 32))
  set θ2 := value (UInt64.ofNat (1072734898 * 2 ^ 32))
  have hpos : 0 < value x.toBits := by linarith
  have habs : |value x.toBits| = value x.toBits := abs_of_pos hpos
  have hs := sgn_false x hpos
  have h1 := high_finite x.toBits hxf
  have hn4 := Expm1Near.high_of_ge x.toBits 1071001155 (by norm_num) (by rw [habs]; exact hlo)
  have hn5 := Expm1Near.high_of_lt x.toBits 1072734898 (by norm_num) (by rw [habs]; exact hhi)
  have h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735) := by
    intro h
    have := UInt64.le_iff_toNat_le.mp h.1
    change 1082535490 ≤ _ at this
    omega
  have h3 : ¬ (highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0) := by
    intro h
    rw [hs] at h
    exact absurd h.2.1 (by decide)
  have h4 : highWord x.toBits > 1071001154 := UInt64.lt_iff_toNat_lt.mpr (by
    change 1071001154 < _; omega)
  have h5 : highWord x.toBits < 1072734898 := UInt64.lt_iff_toNat_lt.mpr hn5
  rw [select_reduced_one x h1 h2 h3 h4 h5, hs]
  simp only [Bool.false_eq_true, ite_false]
  rw [Expm1Words.kernel_bits]
  simp only [F64Bits.toBits_sub, Expm1Words.float_ofBits, ln2Hi_bits, ln2Lo_bits]
  obtain ⟨hyf, hcf, hy, hc, hr⟩ := Expm1ReduceOne.reduce_one_pos x.toBits hxf (by linarith)
    (by linarith)
  have he : 2 * Real.exp (value x.toBits - Real.log 2) - 1 = Real.exp (value x.toBits) - 1 := by
    have := exp_shift_pos (value x.toBits) 1
    push_cast at this
    rw [pow_one, one_mul] at this
    rw [this]
  rw [← he]
  have hη : (0 : ℝ) ≤ η := by norm_num [multiplicationUnderflowEpsilon]
  by_cases hq : value (Wasm.IEEE64.sub (Wasm.IEEE64.sub x.toBits ln2Hi) ln2Lo) < -1 / 4
  · obtain ⟨S, hn, hb⟩ := Expm1NearPos.one_low_near _ _ hyf hcf hy hc _ hr hq
    refine ⟨S, hn, ?_, fun _ => ?_, fun _ => hb⟩
    · have : (0 : ℝ) ≤ 2 * (1 / 2 ^ 55) := by positivity
      linarith
    · have : (0 : ℝ) ≤ 2 * (1 / 2 ^ 56) := by positivity
      linarith
  · obtain ⟨S, hn, hb, hb'⟩ := Expm1NearPos.one_high_near _ _ hyf hcf hy hc _ hr hq
    refine ⟨S, hn, hb, hb', fun hx => ?_⟩
    exfalso
    have hl := ExpTight.log_two_bounds.1
    have hrb := abs_le.mp hr
    have hcb := abs_le.mp hc
    have hu : u = 1 / 2 ^ 53 := rfl
    have h3 : 36 / 100 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    have h4 : (1 : ℝ) / 2 ^ 70 ≤ 1 / 10 ^ 10 := by norm_num
    have hq' := not_lt.mp hq
    linarith

theorem near_k_pos (x : Float) (hxf : Finite x.toBits)
    (hlo : value (UInt64.ofNat (1072734898 * 2 ^ 32)) ≤ value x.toBits)
    (hhi : value x.toBits ≤ 22) :
    ∃ S : ℝ, Finite (Tanh.expm1 x).toBits ∧ 0 < S ∧
      |value (Tanh.expm1 x).toBits - S| ≤ u * S ∧
      (|S - (Real.exp (value x.toBits) - 1)| ≤ 4 * (4901 / 10000 * u) ∨
        |S - (Real.exp (value x.toBits) - 1)| ≤ 85 / 100 * u * (Real.exp (value x.toBits) - 1)) := by
  obtain ⟨-, -, hθ2, -, -⟩ := Expm1Near.threshold_bounds
  set θ2 := value (UInt64.ofNat (1072734898 * 2 ^ 32))
  have hu : u = 1 / 2 ^ 53 := rfl
  have hpos : 0 < value x.toBits := by linarith
  have habs : |value x.toBits| = value x.toBits := abs_of_pos hpos
  have hs := sgn_false x hpos
  have h1 := high_finite x.toBits hxf
  have hn5 := Expm1Near.high_of_ge x.toBits 1072734898 (by norm_num) (by rw [habs]; exact hlo)
  have h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735) := by
    intro h
    have hge := high_ge_real x.toBits 1082535490 (by norm_num) 709 709 (by norm_num)
      (by decide +kernel) (UInt64.le_iff_toNat_le.mp h.1)
    rw [habs] at hge
    linarith
  have h3 : ¬ (highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0) := by
    intro h
    rw [hs] at h
    exact absurd h.2.1 (by decide)
  have h4 : highWord x.toBits > 1071001154 := UInt64.lt_iff_toNat_lt.mpr (by
    change 1071001154 < _; omega)
  have h5 : ¬ highWord x.toBits < 1072734898 := by
    intro h
    have := UInt64.lt_iff_toNat_lt.mp h
    change _ < 1072734898 at this
    omega
  rw [select_reduced_pos x h1 h2 h3 h4 h5 hs, Expm1Words.kernel_bits]
  simp only [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_add,
    F64Convert.toUInt64_eq, F64Convert.toBits_toFloat, Expm1Words.float_ofBits, ln2Hi_bits,
    ln2Lo_bits, invln2_bits, half_bits, hs]
  obtain ⟨hm1, hm2, hyf, hcf, hy, hc, hr⟩ :=
    Expm1ReduceK.reduce_k_pos x.toBits hxf (by linarith) (by linarith)
  set m := Wasm.IEEE64.truncSatI64U
    (Wasm.IEEE64.add (Wasm.IEEE64.mul invln2 x.toBits) Expm1Words.half)
  obtain ⟨hL1, hL2⟩ := Expm1ReduceK.log_two_bounds
  have hyc : |value x.toBits - (m.toNat : ℝ) * Real.log 2| ≤ 3467 / 10000 := by
    have hyb := abs_le.mp hy
    have hcb := abs_le.mp hc
    have hrb := abs_le.mp hr
    have hsm : 36 / 100 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    have h70 : (1 : ℝ) / 2 ^ 70 ≤ 1 / 10 ^ 10 := by norm_num
    push_cast at hrb
    rw [abs_le]; constructor <;> linarith
  have hyb := abs_le.mp hyc
  have hm32 : m.toNat ≤ 32 := by
    have : (m.toNat : ℝ) < 33 := by nlinarith
    have : m.toNat < 33 := by exact_mod_cast this
    omega
  have he := exp_shift_pos (value x.toBits) m.toNat
  rw [← he]
  have hη : (0 : ℝ) ≤ η := by norm_num [multiplicationUnderflowEpsilon]
  have hE : 0 < (2 : ℝ) ^ m.toNat * Real.exp (value x.toBits - (m.toNat : ℤ) * Real.log 2) - 1 := by
    rw [he]; linarith [Real.add_one_le_exp (value x.toBits)]
  have hEhi : (2 : ℝ) ^ m.toNat * Real.exp (value x.toBits - (m.toNat : ℤ) * Real.log 2) - 1 ≤
      2 ^ 32 := by
    rw [he]
    have := ExpTightFloat.exp_le_two_pow (value x.toBits) 32 (by push_cast; linarith)
    linarith
  -- From a nearest word to the `∃ S` form.
  have hfrom : ∀ (w : UInt64) (S : ℝ), Nearest S w →
      |S - ((2 : ℝ) ^ m.toNat * Real.exp (value x.toBits - (m.toNat : ℤ) * Real.log 2) - 1)| ≤
        4 * (4901 / 10000 * u) →
      ∃ S : ℝ, Finite w ∧ 0 < S ∧ |value w - S| ≤ u * S ∧
        (|S - ((2 : ℝ) ^ m.toNat * Real.exp (value x.toBits - (m.toNat : ℤ) * Real.log 2) - 1)| ≤
          4 * (4901 / 10000 * u) ∨
        |S - ((2 : ℝ) ^ m.toNat * Real.exp (value x.toBits - (m.toNat : ℤ) * Real.log 2) - 1)| ≤
          85 / 100 * u *
            ((2 : ℝ) ^ m.toNat * Real.exp (value x.toBits - (m.toNat : ℤ) * Real.log 2) - 1)) := by
    intro w S hn hb
    have hτ1 : (1 : ℝ) / 2 ≤
        (2 : ℝ) ^ m.toNat * Real.exp (value x.toBits - (m.toNat : ℤ) * Real.log 2) - 1 := by
      rw [he]
      have := Real.add_one_le_exp (value x.toBits)
      linarith
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    have hu4 : 4 * (4901 / 10000 * u) ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    refine ⟨S, (nearest_finite S w hn).1, by linarith, ?_, Or.inl hb⟩
    have h1 : (1 : ℝ) / 2 ^ 1022 ≤ 1 / 4 := by norm_num
    have h2 : (2 : ℝ) ^ 32 + 1 ≤ 2 ^ 1022 := by norm_num
    exact F64NearestHalf.nearest_relative S w hn (by linarith) (by linarith)
  rcases Nat.lt_or_ge m.toNat 3 with h3' | h3'
  · rcases Nat.lt_or_ge m.toNat 2 with h2' | h2'
    · have hm : m.toNat = 1 := by omega
      have hm' := word_one m hm
      have hq : ¬ value (Wasm.IEEE64.sub (Wasm.IEEE64.sub x.toBits
          (Wasm.IEEE64.mul (Wasm.IEEE64.convertI64U m) ln2Hi))
          (Wasm.IEEE64.mul (Wasm.IEEE64.convertI64U m) ln2Lo)) < -1 / 4 := by
        have hyb' := abs_le.mp hy
        have hrb := abs_le.mp hr
        have hcb := abs_le.mp hc
        have hsm : 36 / 100 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
        have h70 : (1 : ℝ) / 2 ^ 70 ≤ 1 / 10 ^ 10 := by norm_num
        rw [hm] at hrb
        push_cast at hrb
        linarith
      have hr1 := hr
      rw [hm] at hr1
      push_cast at hr1
      obtain ⟨S, hn, hb, -⟩ := Expm1NearPos.one_high_near _ _ hyf hcf hy hc _ (by
        simpa only [Int.cast_one, one_mul] using hr1) hq
      have hT : (2 : ℝ) ^ m.toNat * Real.exp (value x.toBits - (m.toNat : ℤ) * Real.log 2) - 1 =
          2 * Real.exp (value x.toBits - Real.log 2) - 1 := by
        rw [hm]; push_cast; ring_nf
      have hk : ∀ yy cc : UInt64, Expm1Words.kernel yy cc false m = Expm1Words.kernel yy cc false 1 :=
        fun yy cc => by rw [hm']
      rw [hk]
      apply hfrom _ S hn
      rw [hT]
      have : 3 * η + 2 * (1 / 2 ^ 55) ≤ 1 / 2 ^ 53 := by norm_num [multiplicationUnderflowEpsilon]
      have hu' : 4802 / 10000 * u + 1 / 2 ^ 53 ≤ 4 * (4901 / 10000 * u) := by rw [hu]; norm_num
      linarith
    · have hm : m.toNat = 2 := by omega
      obtain ⟨S, hn, hb⟩ := Expm1NearPos.two_near _ _ m hyf hcf hy hc _ hr hm
      apply hfrom _ S hn
      have h4 : (2 : ℝ) ^ m.toNat = 4 := by rw [hm]; norm_num
      rw [h4]
      exact hb
  rcases Nat.lt_or_ge m.toNat 20 with h20 | h20
  · obtain ⟨S, h1, h2, h3, h4⟩ := Expm1NearForms.mid_low_near _ _ m hyf hcf hy hc _ hr h3' h20
    exact ⟨S, h1, h2, h3, Or.inr h4⟩
  · obtain ⟨S, h1, h2, h3, h4⟩ :=
      Expm1NearForms.mid_high_near _ _ m hyf hcf hy hc _ hr h20 (by omega)
    exact ⟨S, h1, h2, h3, Or.inr h4⟩

#print axioms near_one_pos
#print axioms near_k_pos

end Verified.Examples.SinhExpm1
