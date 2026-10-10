import Verified.Examples.AtanTheoremTail
import LeanExe.ProofKit.F64Exact
import LeanExe.ProofKit.F64HighWord

/-!
The reduced arguments of `Atan.atan` for `|x| ≥ 0.4375`, as approximations of their exact values.
With `a = |x|`: `(2a - 1)/(2 + a)` for `a < 0.6875`, `(a - 1)/(a + 1)` for `a < 1.1875`,
`(a - 1.5)/(1 + 1.5 a)` for `a < 2.4375`, and `-1/a` beyond.  `2a`, `2a - 1`, `a - 1`, and
`a - 1.5` are exact (doubling and Sterbenz's lemma), and the other operations round once each.
`arctan a` is `arctan c + arctan t` for the exact reduced argument `t` and `c = 1/2, 1, 3/2`, and
`π/2 + arctan (-1/a)` in the last interval.
-/

namespace Verified.Examples.AtanTheoremReduce
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound

set_option exponentiation.threshold 4096

theorem float_eq_ofBits (x : Float) : x = Float.ofBits x.toBits := (F64Bits.ofBits_toBits x).symm

theorem value_word (w : UInt64) (q : ℚ) (h : ratOfWord w = q) : value w = (q : ℝ) := by
  rw [← ratOfWord_cast, h]

theorem abs_facts (x : Float) (hx : Finite x.toBits) :
    Finite x.abs.toBits ∧ value x.abs.toBits = |value x.toBits| := by
  rw [F64Bits.toBits_abs]
  refine ⟨?_, F64HighWord.value_abs _⟩
  have he := (F64Sign.fields_abs x.toBits).1
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, he] at hx ⊢
  exact hx

theorem normal_exponent (w : UInt64) (h : 1 / 2 ^ 1000 ≤ |value w|) :
    1 ≤ Wasm.IEEE64.exponent w := by
  by_contra hn
  have := F64Magnitude.magnitude_lt w 1 (-1022) le_rfl (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (-1022 : ℤ) < 1 / 2 ^ 1000 := by norm_num
  exact absurd h (not_le.mpr (this.trans h2))

theorem input_approx (x : Float) (hx : Finite x.toBits) (M : ℝ) (hM : |value x.toBits| ≤ M) :
    FSApprox x (value x.toBits) 1 M 0 :=
  ⟨one_pos, le_rfl, by rw [mul_one]; exact hM, by rw [zero_mul]; exact approx_self _ hx⟩

theorem const_approx (x : Float) (w : UInt64) (hxw : x.toBits = w) (hf : Wasm.IEEE64.isFinite w = true)
    (q : ℚ) (hq : ratOfWord w = q) (M : ℝ) (hM : |(q : ℝ)| ≤ M) : FSApprox x (q : ℝ) 1 M 0 := by
  have h := fsapprox_const w hf M (by rw [value_word w q hq]; exact hM)
  rw [float_eq_ofBits x, hxw]
  exact h.congr (value_word w q hq)

/-- An exact difference of positive floats within a factor of two. -/
theorem sub_exact_float (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hpa : 0 < value a.toBits) (hpb : 0 < value b.toBits) (h1 : value b.toBits ≤ 2 * value a.toBits)
    (h2 : value a.toBits ≤ 2 * value b.toBits) (hla : value a.toBits < 2 ^ 900)
    (hlb : value b.toBits < 2 ^ 900) (M : ℝ) (hM : |value a.toBits - value b.toBits| ≤ M) :
    FSApprox (a - b) (value a.toBits - value b.toBits) 1 M 0 := by
  have h := F64Exact.sub_exact a.toBits b.toBits ha hb hpa hpb h1 h2 hla hlb
  refine ⟨one_pos, le_rfl, by rw [mul_one]; exact hM, ?_⟩
  unfold Approx
  rw [F64Bits.toBits_sub, zero_mul]
  exact ⟨h.1, by rw [h.2, sub_self, abs_zero]⟩

/-- `2.0 * a` for a normal `a`. -/
theorem double_float (a : Float) (ha : Finite a.toBits) (h1 : 1 / 2 ^ 1000 ≤ |value a.toBits|)
    (h2 : |value a.toBits| < 2 ^ 900) :
    Finite (2.0 * a).toBits ∧ value (2.0 * a).toBits = 2 * value a.toBits := by
  rw [F64Bits.toBits_mul, show (2.0 : Float).toBits = 0x4000000000000000 from rfl]
  exact F64Exact.mul_two_exact a.toBits ha (normal_exponent _ h1)
    (F64Exact.exponent_le_of_value _ h2)

noncomputable def red0Err (A1 A2 Mn : ℝ) : ℝ :=
  (0 + Mn * (0 + 0 + (2 + A2 + (0 + 0)) / 2 ^ 53) / (2 + A1)) /
      (2 + A1 - (0 + 0 + (2 + A2 + (0 + 0)) / 2 ^ 53)) +
    (Mn + 0) / (2 + A1 - (0 + 0 + (2 + A2 + (0 + 0)) / 2 ^ 53)) / 2 ^ 53 + 1 / 2 ^ 1075

theorem reduce0 (x : Float) (hx : Finite x.toBits) (A1 A2 Mn : ℝ) (hA1 : 7 / 16 ≤ A1)
    (h1 : A1 ≤ |value x.toBits|) (h2 : |value x.toBits| ≤ A2) (hA2 : A2 ≤ 11 / 16)
    (hMn : |2 * |value x.toBits| - 1| ≤ Mn) (hMn1 : Mn ≤ 1) :
    FSApprox ((2.0 * x.abs - 1.0) / (2.0 + x.abs))
      ((2 * |value x.toBits| - 1) / (2 + |value x.toBits|)) 1 (Mn / (2 + A1))
      (red0Err A1 A2 Mn) := by
  obtain ⟨haf, hav⟩ := abs_facts x hx
  have hva : 0 < value x.abs.toBits := by rw [hav]; linarith
  have hd2 := double_float x.abs haf (by rw [hav, abs_abs]; linarith)
    (by rw [hav, abs_abs]; linarith)
  have h2pos : 0 < value (2.0 * x.abs).toBits := by rw [hd2.2]; linarith
  have hone : value (1.0 : Float).toBits = 1 := by
    rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl,
      value_word 0x3FF0000000000000 1 (by decide +kernel)]
    norm_num
  have hn := sub_exact_float (2.0 * x.abs) 1.0 hd2.1
    (by unfold CodeLib.IEEE64.Finite; decide +kernel) h2pos
    (by rw [hone]; norm_num) (by rw [hone, hd2.2, hav]; linarith)
    (by rw [hd2.2, hav, hone]; linarith)
    (by rw [hd2.2, hav]; norm_num; linarith) (by rw [hone]; norm_num) Mn
    (by rw [hone, hd2.2, hav]; exact hMn)
  rw [hone, hd2.2, hav] at hn
  have hc2 := const_approx 2.0 0x4000000000000000 rfl (by decide +kernel) 2 (by decide +kernel) 2
    (by norm_num)
  have ha := input_approx x.abs haf A2 (by rw [hav, abs_abs]; exact h2)
  rw [hav] at ha
  have hd := fsapprox_add' hc2 ha (by norm_num; linarith)
  push_cast at hd
  have hA20 : 0 ≤ A2 := by linarith
  have hmb : 2 + A1 ≤ abs (2 + |value x.toBits|) := by
    rw [abs_of_pos (by positivity)]
    linarith
  have ht := fsapprox_div hn hd (2 + A1) hmb (by norm_num; nlinarith) (1 / 2 ^ 1075)
    (by norm_num) (by
      rw [div_lt_iff₀ (by norm_num; nlinarith)]
      nlinarith)
  exact ht.mono (le_refl _) (le_of_eq (by unfold red0Err; ring))

theorem one_value : value (1.0 : Float).toBits = 1 := by
  rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl,
    value_word 0x3FF0000000000000 1 (by decide +kernel)]
  norm_num

theorem one_finite : Finite (1.0 : Float).toBits := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

noncomputable def red1Err (A1 A2 Mn : ℝ) : ℝ :=
  let ed := (A2 + 1) / 2 ^ 53
  (Mn * ed / (A1 + 1)) / (A1 + 1 - ed) + Mn / (A1 + 1 - ed) / 2 ^ 53 + 1 / 2 ^ 1075

theorem reduce1 (x : Float) (hx : Finite x.toBits) (A1 A2 Mn : ℝ) (hA1 : 11 / 16 ≤ A1)
    (h1 : A1 ≤ |value x.toBits|) (h2 : |value x.toBits| ≤ A2) (hA2 : A2 ≤ 19 / 16)
    (hMn : |(|value x.toBits| - 1)| ≤ Mn) (hMn1 : Mn ≤ 1) :
    FSApprox ((x.abs - 1.0) / (x.abs + 1.0))
      ((|value x.toBits| - 1) / (|value x.toBits| + 1)) 1 (Mn / (A1 + 1)) (red1Err A1 A2 Mn) := by
  obtain ⟨haf, hav⟩ := abs_facts x hx
  have hva : 0 < value x.abs.toBits := by rw [hav]; linarith
  have hn := sub_exact_float x.abs 1.0 haf one_finite hva (by rw [one_value]; norm_num)
    (by rw [one_value, hav]; linarith) (by rw [hav, one_value]; linarith)
    (by rw [hav]; norm_num; linarith) (by rw [one_value]; norm_num) Mn
    (by rw [one_value, hav]; exact hMn)
  rw [one_value, hav] at hn
  have hc1 := const_approx 1.0 0x3FF0000000000000 rfl (by decide +kernel) 1 (by decide +kernel) 1
    (by norm_num)
  have ha := input_approx x.abs haf A2 (by rw [hav, abs_abs]; exact h2)
  rw [hav] at ha
  have hd := fsapprox_add' ha hc1 (by norm_num; linarith)
  push_cast at hd
  have hmb : A1 + 1 ≤ abs (|value x.toBits| + 1) := by
    rw [abs_of_pos (by positivity)]
    linarith
  have ht := fsapprox_div hn hd (A1 + 1) hmb (by norm_num; nlinarith) (1 / 2 ^ 1075)
    (by norm_num) (by
      rw [div_lt_iff₀ (by norm_num; nlinarith)]
      nlinarith)
  exact ht.mono (le_refl _) (le_of_eq (by simp only [red1Err]; ring))

noncomputable def red2Err (A1 A2 Mn : ℝ) : ℝ :=
  let em := 3 / 2 * A2 / 2 ^ 53 + 1 / 2 ^ 1075
  let ed := em + (1 + 3 / 2 * A2 + em) / 2 ^ 53
  (Mn * ed / (1 + 3 / 2 * A1)) / (1 + 3 / 2 * A1 - ed) + Mn / (1 + 3 / 2 * A1 - ed) / 2 ^ 53 +
    1 / 2 ^ 1075

theorem reduce2 (x : Float) (hx : Finite x.toBits) (A1 A2 Mn : ℝ) (hA1 : 19 / 16 ≤ A1)
    (h1 : A1 ≤ |value x.toBits|) (h2 : |value x.toBits| ≤ A2) (hA2 : A2 ≤ 39 / 16)
    (hMn : |(|value x.toBits| - 3 / 2)| ≤ Mn) (hMn1 : Mn ≤ 2) :
    FSApprox ((x.abs - 1.5) / (1.0 + 1.5 * x.abs))
      ((|value x.toBits| - 3 / 2) / (1 + 3 / 2 * |value x.toBits|)) 1 (Mn / (1 + 3 / 2 * A1))
      (red2Err A1 A2 Mn) := by
  obtain ⟨haf, hav⟩ := abs_facts x hx
  have hva : 0 < value x.abs.toBits := by rw [hav]; linarith
  have h15 : value (1.5 : Float).toBits = 3 / 2 := by
    rw [show (1.5 : Float).toBits = 0x3FF8000000000000 from rfl,
      value_word 0x3FF8000000000000 (3 / 2) (by decide +kernel)]
    norm_num
  have h15f : Finite (1.5 : Float).toBits := by
    unfold CodeLib.IEEE64.Finite
    decide +kernel
  have hn := sub_exact_float x.abs 1.5 haf h15f hva (by rw [h15]; norm_num)
    (by rw [h15, hav]; linarith) (by rw [hav, h15]; linarith)
    (by rw [hav]; norm_num; linarith) (by rw [h15]; norm_num) Mn
    (by rw [h15, hav]; exact hMn)
  rw [h15, hav] at hn
  have hc15 := const_approx 1.5 0x3FF8000000000000 rfl (by decide +kernel) (3 / 2)
    (by decide +kernel) (3 / 2) (by norm_num)
  have hc1 := const_approx 1.0 0x3FF0000000000000 rfl (by decide +kernel) 1 (by decide +kernel) 1
    (by norm_num)
  have ha := input_approx x.abs haf A2 (by rw [hav, abs_abs]; exact h2)
  rw [hav] at ha
  have hm := fsapprox_mul hc15 ha (1 / 2 ^ 1075) (by norm_num) (by norm_num; nlinarith)
  have hm1 := hm.rescale 1 1 one_pos le_rfl (by norm_num)
  have hd := fsapprox_add' hc1 hm1 (by norm_num; nlinarith)
  push_cast at hd
  have hmb : 1 + 3 / 2 * A1 ≤ abs (1 + 3 / 2 * |value x.toBits|) := by
    rw [abs_of_pos (by positivity)]
    linarith
  have ht := fsapprox_div hn hd (1 + 3 / 2 * A1) hmb (by norm_num; nlinarith) (1 / 2 ^ 1075)
    (by norm_num) (by
      rw [div_lt_iff₀ (by norm_num; nlinarith)]
      nlinarith)
  exact ht.mono (le_refl _) (le_of_eq (by simp only [red2Err]; ring))

theorem neg_one_bits : (-1.0 : Float).toBits = 0xBFF0000000000000 := by
  rw [F64Bits.toBits_neg, show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
  decide +kernel

noncomputable def red3Err (A1 : ℝ) : ℝ := 1 / A1 / 2 ^ 53 + 1 / 2 ^ 1075

theorem reduce3 (x : Float) (hx : Finite x.toBits) (A1 A2 : ℝ) (hA1 : 39 / 16 ≤ A1)
    (h1 : A1 ≤ |value x.toBits|) (h2 : |value x.toBits| ≤ A2) (hA2 : A2 ≤ 2 ^ 900) :
    FSApprox (-1.0 / x.abs) (-1 / |value x.toBits|) 1 (1 / A1) (red3Err A1) := by
  obtain ⟨haf, hav⟩ := abs_facts x hx
  have hcm := const_approx (-1.0) 0xBFF0000000000000 neg_one_bits (by decide +kernel) (-1)
    (by decide +kernel) 1 (by norm_num)
  have ha := input_approx x.abs haf A2 (by rw [hav, abs_abs]; exact h2)
  rw [hav] at ha
  push_cast at hcm
  have hmb : A1 ≤ abs (|value x.toBits|) := by rw [abs_abs]; exact h1
  have ht := fsapprox_div hcm ha A1 hmb (by linarith) (1 / 2 ^ 1075) (by norm_num) (by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith)
  exact ht.mono (le_refl _) (le_of_eq (by
    simp only [red3Err, mul_zero, zero_div, zero_add, sub_zero, add_zero]))

theorem arctan_red0 (a : ℝ) (ha : 0 < a) :
    Real.arctan a = Real.arctan (1 / 2) + Real.arctan ((2 * a - 1) / (2 + a)) := by
  have h : 1 / 2 * ((2 * a - 1) / (2 + a)) < 1 := by
    rw [mul_div_assoc', div_lt_one (by positivity)]
    nlinarith
  rw [Real.arctan_add h]
  congr 1
  field_simp
  ring

theorem arctan_red1 (a : ℝ) (ha : 0 < a) :
    Real.arctan a = Real.arctan 1 + Real.arctan ((a - 1) / (a + 1)) := by
  have h : 1 * ((a - 1) / (a + 1)) < 1 := by
    rw [one_mul, div_lt_one (by positivity)]
    linarith
  rw [Real.arctan_add h]
  congr 1
  field_simp
  ring

theorem arctan_red2 (a : ℝ) (ha : 0 < a) :
    Real.arctan a = Real.arctan (3 / 2) + Real.arctan ((a - 3 / 2) / (1 + 3 / 2 * a)) := by
  have h : 3 / 2 * ((a - 3 / 2) / (1 + 3 / 2 * a)) < 1 := by
    rw [mul_div_assoc', div_lt_one (by positivity)]
    nlinarith
  rw [Real.arctan_add h]
  congr 1
  field_simp
  ring

theorem arctan_red3 (a : ℝ) (ha : 0 < a) :
    Real.arctan a = Real.pi / 2 + Real.arctan (-1 / a) := by
  rw [neg_div, Real.arctan_neg, ← inv_eq_one_div, Real.arctan_inv_of_pos ha]
  ring

#print axioms reduce0
#print axioms reduce1
#print axioms reduce2
#print axioms reduce3
#print axioms arctan_red0
#print axioms arctan_red1
#print axioms arctan_red2
#print axioms arctan_red3

end Verified.Examples.AtanTheoremReduce
