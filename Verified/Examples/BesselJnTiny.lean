import Verified.Examples.BesselStepF
import Verified.Examples.BesselSmallSigns

/-!
`jn` below `2^-30`, where the code returns `0` for `n > 33` and otherwise `(x/2)^n/n!` from a loop
of `n - 1` products.  The loop keeps its factorial between 1 and `2^(6 i)` and its power below
`2^-30` (`tiny_loop`), so the result is finite and at most 2 in magnitude (`tiny_value`).  Since
`J_(n-1)(x) ≤ (5/3)(x/2)` and `M_n ≥ 2/(π x J_(n-1))` (`BesselSmallSigns.modn_ge`), `M_n ≥ 2^59`
there (`tiny_modulus`), so an error of at most 3 lies below `u M_n`.
-/

namespace Verified.Examples.BesselJnTiny
open Real CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselOrderN BesselRecur
  BesselStepF BesselSmallSigns

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- The states of `LeanExe.loop`. -/
def lseq {α : Type} (f : UInt64 → α → α) (init : α) : ℕ → α
  | 0 => init
  | i + 1 => f (UInt64.ofNat i) (lseq f init i)

theorem loop_lseq {α : Type} (f : UInt64 → α → α) (init : α) (n : UInt64) :
    LeanExe.loop n init f = lseq f init n.toNat := by
  unfold LeanExe.loop
  induction n.toNat with
  | zero => rfl
  | succ k ih => rw [Nat.fold_succ, ih]; rfl

/-- The product of two finite floats of bounded magnitude. -/
theorem mul_mag {a b : Float} (ha : Finite a.toBits) (hb : Finite b.toBits) {A B : ℝ}
    (hA : |value a.toBits| ≤ A) (hB : |value b.toBits| ≤ B) (hAB : A * B ≤ 2 ^ 1000) :
    Finite (a * b).toBits ∧
      |value (a * b).toBits - value a.toBits * value b.toBits| ≤ A * B / 2 ^ 53 + 1 / 2 ^ 1075 := by
  have h := fapprox_mul (fapprox_exact a ha) (fapprox_exact b hb) A B hA hB (A * B)
    (by simp) (by linarith [show (2 : ℝ) ^ 1000 < 2 ^ 1022 by norm_num])
  refine ⟨h.1, le_trans h.2 (le_of_eq ?_)⟩
  ring

/-- The quotient of two finite floats, the divisor at least `m > 0` in magnitude. -/
theorem div_mag {a b : Float} (ha : Finite a.toBits) (hb : Finite b.toBits) {A m : ℝ}
    (hA : |value a.toBits| ≤ A) (hm : 0 < m) (hb' : m ≤ |value b.toBits|) (hAm : A / m ≤ 2 ^ 1000) :
    Finite (a / b).toBits ∧
      |value (a / b).toBits - value a.toBits / value b.toBits| ≤ A / m / 2 ^ 53 + 1 / 2 ^ 1075 := by
  have h := fapprox_div (fapprox_exact a ha) (fapprox_exact b hb) A m hA hb' hm (A / m)
    (by simp) (by linarith [show (2 : ℝ) ^ 1000 < 2 ^ 1022 by norm_num])
  refine ⟨h.1, le_trans h.2 (le_of_eq ?_)⟩
  simp

/-- The body of the loop below `2^-30`. -/
def tbody (temp : Float) (k : UInt64) (s : Float × Float) : Float × Float :=
  (s.1 * (k + 2).toFloat, s.2 * temp)

theorem word_add_two (i : ℕ) (hi : i < 2 ^ 40) : (UInt64.ofNat i + 2).toNat = i + 2 := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']
  simp only [UInt64.reduceToNat, Nat.reducePow]
  omega

/-- The loop below `2^-30`: the factorial stays in `[1, 2^(6 i)]` and the power below `2^-30`. -/
theorem tiny_loop (temp : Float) (htf : Finite temp.toBits) (ht : |value temp.toBits| ≤ 1 / 2 ^ 30) :
    ∀ i, i ≤ 33 → Finite (lseq (tbody temp) ((1.0 : Float), temp) i).1.toBits ∧
      1 ≤ value (lseq (tbody temp) ((1.0 : Float), temp) i).1.toBits ∧
      value (lseq (tbody temp) ((1.0 : Float), temp) i).1.toBits ≤ 2 ^ (6 * i) ∧
      Finite (lseq (tbody temp) ((1.0 : Float), temp) i).2.toBits ∧
      |value (lseq (tbody temp) ((1.0 : Float), temp) i).2.toBits| ≤ 1 / 2 ^ 30 := by
  intro i
  induction i with
  | zero =>
    intro _
    have h1 := fapprox_one
    refine ⟨h1.1, ?_, ?_, htf, ht⟩
    · have := abs_le.mp h1.2; show 1 ≤ value (1.0 : Float).toBits; linarith
    · have := abs_le.mp h1.2; show value (1.0 : Float).toBits ≤ 2 ^ (6 * 0); norm_num; linarith
  | succ j ih =>
    intro hj
    obtain ⟨fa, a1, a2, fb, b1⟩ := ih (by omega)
    have e : lseq (tbody temp) ((1.0 : Float), temp) (j + 1) =
        ((lseq (tbody temp) ((1.0 : Float), temp) j).1 * (UInt64.ofNat j + 2).toFloat,
          (lseq (tbody temp) ((1.0 : Float), temp) j).2 * temp) := rfl
    rw [e]
    dsimp only
    have hw := word_add_two j (by omega)
    have hkf := toFloat_exact (UInt64.ofNat j + 2) (by rw [hw]; omega)
    rw [hw] at hkf
    have hkv : value (UInt64.ofNat j + 2).toFloat.toBits = (j : ℝ) + 2 := by
      have := abs_nonpos_iff.mp hkf.2
      push_cast at this
      linarith
    have hj32 : (j : ℝ) ≤ 32 := by exact_mod_cast (show j ≤ 32 by omega)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hk0 : |value (UInt64.ofNat j + 2).toFloat.toBits| ≤ 34 := by
      rw [hkv, abs_of_nonneg (by linarith)]
      linarith
    set A := value (lseq (tbody temp) ((1.0 : Float), temp) j).1.toBits with hAdef
    have hA0 : 0 ≤ A := by linarith
    have hA : |A| ≤ A := le_of_eq (abs_of_nonneg hA0)
    have hp6 : (2 : ℝ) ^ (6 * j) ≤ 2 ^ 192 := pow_le_pow_right₀ (by norm_num) (by omega)
    obtain ⟨fm, em⟩ := mul_mag fa hkf.1 hA hk0 (by nlinarith)
    obtain ⟨fp, ep⟩ := mul_mag fb htf b1 ht (by norm_num)
    rw [hkv] at em
    have em' := abs_le.mp em
    have hpow : (1 : ℝ) ≤ 2 ^ (6 * j) := one_le_pow₀ (by norm_num)
    refine ⟨fm, ?_, ?_, fp, ?_⟩
    · nlinarith [mul_nonneg hA0 hj0]
    · have h6 : (2 : ℝ) ^ (6 * (j + 1)) = 2 ^ (6 * j) * 64 := by rw [mul_add, pow_add]; norm_num
      rw [h6]
      have h7 := mul_le_mul_of_nonneg_right a2 (show 0 ≤ (j : ℝ) + 2 + 34 / 2 ^ 53 by positivity)
      have h8 : (2 : ℝ) ^ (6 * j) * ((j : ℝ) + 2 + 34 / 2 ^ 53) ≤ 2 ^ (6 * j) * 63 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : (34 : ℝ) / 2 ^ 53 ≤ 1 := by norm_num
        linarith
      nlinarith
    · have h1 : |value (lseq (tbody temp) ((1.0 : Float), temp) j).2.toBits * value temp.toBits| ≤
          1 / 2 ^ 30 * (1 / 2 ^ 30) := by
        rw [abs_mul]; exact mul_le_mul b1 ht (abs_nonneg _) (by norm_num)
      have h2 := abs_sub_abs_le_abs_sub (value ((lseq (tbody temp) ((1.0 : Float), temp) j).2 *
        temp).toBits) (value (lseq (tbody temp) ((1.0 : Float), temp) j).2.toBits * value temp.toBits)
      have : (1 : ℝ) / 2 ^ 30 * (1 / 2 ^ 30) + 1 / 2 ^ 30 * (1 / 2 ^ 30) / 2 ^ 53 + 1 / 2 ^ 1075 ≤
          1 / 2 ^ 30 := by norm_num
      linarith

/-- The result below `2^-30` is finite and at most 2 in magnitude. -/
theorem tiny_value (xa : Float) (n : UInt64) (hxf : Finite xa.toBits)
    (hx : |value xa.toBits| < 1 / 2 ^ 30) (hn2 : 2 ≤ n.toNat) :
    Finite (if n > 33 then (0.0 : Float) else
        (LeanExe.loop (n - 1) ((1.0 : Float), xa * 0.5) (tbody (xa * 0.5))).2 /
          (LeanExe.loop (n - 1) ((1.0 : Float), xa * 0.5) (tbody (xa * 0.5))).1).toBits ∧
      |value (if n > 33 then (0.0 : Float) else
        (LeanExe.loop (n - 1) ((1.0 : Float), xa * 0.5) (tbody (xa * 0.5))).2 /
          (LeanExe.loop (n - 1) ((1.0 : Float), xa * 0.5) (tbody (xa * 0.5))).1).toBits| ≤ 2 := by
  split_ifs with h33
  · have h0 : (0.0 : Float).toBits = 0 := rfl
    rw [h0]
    refine ⟨by unfold CodeLib.IEEE64.Finite; decide, ?_⟩
    have : value (0 : UInt64) = 0 := by
      rw [← ratOfWord_cast]
      have : ratOfWord 0 = 0 := by decide +kernel
      rw [this]
      norm_num
    rw [this]; norm_num
  · have h05 : FApprox (0.5 : Float) (1 / 2) 0 := by
      unfold FApprox Approx
      have hb : (0.5 : Float).toBits = 0x3FE0000000000000 := rfl
      rw [hb, ← ratOfWord_cast]
      have : ratOfWord 0x3FE0000000000000 = 1 / 2 := by decide +kernel
      rw [this]
      exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by norm_num⟩
    have hx1 : |value xa.toBits| ≤ 1 := le_trans hx.le (by norm_num)
    obtain ⟨ft, et⟩ := mul_mag hxf h05.1 hx1 (show |value (0.5 : Float).toBits| ≤ 1 by
      have := abs_le.mp h05.2; rw [abs_le]; constructor <;> linarith) (by norm_num)
    have ht : |value (xa * 0.5).toBits| ≤ 1 / 2 ^ 30 := by
      have h5 : value (0.5 : Float).toBits = 1 / 2 := by
        have := abs_le.mp h05.2; linarith [this.1, this.2]
      rw [h5] at et
      have := abs_le.mp et
      rw [abs_le]
      have := abs_lt.mp hx
      constructor <;> nlinarith
    have hn : (n - 1).toNat ≤ 33 := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt] at h33
      rw [UInt64.toNat_sub]
      have := n.toNat_lt
      simp only [UInt64.reduceToNat, Nat.reducePow] at h33 this ⊢
      omega
    rw [loop_lseq]
    obtain ⟨fa, a1, -, fb, b1⟩ := tiny_loop (xa * 0.5) ft ht (n - 1).toNat hn
    have hapos : (1 : ℝ) ≤ |value (lseq (tbody (xa * 0.5)) ((1.0 : Float), xa * 0.5) (n - 1).toNat).1.toBits| := by
      rw [abs_of_nonneg (by linarith)]; exact a1
    obtain ⟨fd, ed⟩ := div_mag fb fa b1 one_pos hapos (by norm_num)
    refine ⟨fd, ?_⟩
    have hq : |value (lseq (tbody (xa * 0.5)) ((1.0 : Float), xa * 0.5) (n - 1).toNat).2.toBits /
        value (lseq (tbody (xa * 0.5)) ((1.0 : Float), xa * 0.5) (n - 1).toNat).1.toBits| ≤
          1 / 2 ^ 30 := by
      rw [abs_div, div_le_iff₀ (by linarith)]
      nlinarith
    have hd := abs_sub_abs_le_abs_sub (value ((lseq (tbody (xa * 0.5)) ((1.0 : Float), xa * 0.5)
      (n - 1).toNat).2 / (lseq (tbody (xa * 0.5)) ((1.0 : Float), xa * 0.5) (n - 1).toNat).1).toBits)
      (value (lseq (tbody (xa * 0.5)) ((1.0 : Float), xa * 0.5) (n - 1).toNat).2.toBits /
        value (lseq (tbody (xa * 0.5)) ((1.0 : Float), xa * 0.5) (n - 1).toNat).1.toBits)
    have : (1 : ℝ) / 2 ^ 30 / 1 / 2 ^ 53 + 1 / 2 ^ 1075 + 1 / 2 ^ 30 ≤ 2 := by norm_num
    linarith

/-- `M_n ≥ 2^59` below `2^-30` for `n ≥ 2`. -/
theorem tiny_modulus (x : ℝ) (h0 : 0 < x) (h1 : x < 1 / 2 ^ 30) (n : ℕ) (hn : 2 ≤ n) :
    2 ^ 59 ≤ modn x n := by
  have hx2 : x ≤ 2 := le_trans h1.le (by norm_num)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hm := modn_ge x h0 hx2 k (by omega)
  have hJ := Jn_le k (by omega) x h0.le hx2
  have hJp := Jn_pos k x h0 hx2
  have hp : (x / 2) ^ k ≤ x / 2 := by
    have h2 : x / 2 ≤ 1 := by linarith
    calc (x / 2) ^ k = (x / 2) ^ (k - 1) * (x / 2) := by
          rw [← pow_succ, show k - 1 + 1 = k by omega]
      _ ≤ 1 * (x / 2) := mul_le_mul_of_nonneg_right (pow_le_one₀ (by positivity) h2) (by positivity)
      _ = x / 2 := one_mul _
  have hf : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hJ2 : Jn k x ≤ 5 / 6 * x := by
    have : (x / 2) ^ k / (k.factorial : ℝ) ≤ x / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hpi : π ≤ 4 := pi_le_four
  have hden : π * x * Jn k x ≤ 4 * x * (5 / 6 * x) := by
    have := mul_le_mul_of_nonneg_left hJ2 (show 0 ≤ π * x by positivity)
    have h4 : π * x * (5 / 6 * x) ≤ 4 * x * (5 / 6 * x) := by
      have h5 := mul_le_mul_of_nonneg_right hpi (show (0 : ℝ) ≤ x * (5 / 6 * x) by positivity)
      calc π * x * (5 / 6 * x) = π * (x * (5 / 6 * x)) := by ring
        _ ≤ 4 * (x * (5 / 6 * x)) := h5
        _ = 4 * x * (5 / 6 * x) := by ring
    linarith
  have hx2' : x ^ 2 ≤ 1 / 2 ^ 60 := by
    have : x ^ 2 < (1 / 2 ^ 30) ^ 2 := by nlinarith
    linarith [show ((1 : ℝ) / 2 ^ 30) ^ 2 = 1 / 2 ^ 60 by norm_num]
  have hpos : 0 < π * x * Jn k x := by positivity
  have : (2 : ℝ) ^ 59 ≤ 2 / (π * x * Jn k x) := by
    rw [le_div_iff₀ hpos]
    nlinarith
  linarith

#print axioms tiny_value
#print axioms tiny_modulus

end Verified.Examples.BesselJnTiny
