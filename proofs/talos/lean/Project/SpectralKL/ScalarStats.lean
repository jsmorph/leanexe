import Project.SpectralKL.Executable
import Project.ProofKit.F64SequentialSum

namespace Project.SpectralKL.Scalar
open CodeLib.IEEE64 Project.ProofKit
open LeanExe.Examples.SpectralKL

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

noncomputable def exactMean (s : Array UInt64) : ℝ :=
  (s.toList.map value).sum / s.size
noncomputable def exactSecond (s : Array UInt64) : ℝ :=
  (s.toList.map fun x => value x ^ 2).sum / s.size

theorem sum_abs_bound {α : Type*} (xs : List α) (f : α → ℝ) (B : ℝ)
    (h : ∀ x ∈ xs, |f x| ≤ B) : |(xs.map f).sum| ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hi := ih (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have ht := abs_add_le (f x) (xs.map f).sum
    linarith

theorem sum_error_bound {α : Type*} (xs : List α) (f g : α → ℝ) (E : ℝ)
    (h : ∀ x ∈ xs, |f x-g x| ≤ E) :
    |(xs.map f).sum-(xs.map g).sum| ≤ xs.length * E := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hi := ih (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have ht := abs_add_le (f x-g x) ((xs.map f).sum-(xs.map g).sum)
    rw [show f x-g x+((xs.map f).sum-(xs.map g).sum) =
      (f x+(xs.map f).sum)-(g x+(xs.map g).sum) by ring] at ht
    linarith

theorem sampleSum_model (s : Array UInt64) :
    sampleSum s = F64SequentialSum.sum s.toList := by
  simp only [sampleSum, F64SequentialSum.sum, Array.foldl_toList, Operations.add]

theorem sampleSquares_model (s : Array UInt64) :
    sampleSquares s = F64SequentialSum.sum (s.toList.map fun x => Wasm.IEEE64.mul x x) := by
  simp only [sampleSquares, F64SequentialSum.sum, Array.foldl_toList, List.foldl_map,
    Operations.add, Operations.mul, Function.comp_def]

theorem sampleCount_model (s : Array UInt64) :
    sampleCount s = F64SequentialSum.sum (s.toList.map fun _ => (0x3FF0000000000000 : UInt64)) := by
  simp only [sampleCount, F64SequentialSum.sum, Array.foldl_toList, List.foldl_map,
    Operations.add, Function.comp_def]

theorem value_one : value 0x3FF0000000000000 = 1 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem reduction_error (s : List UInt64) (hn : s.length ≤ 1048576)
    (hx : ∀ x ∈ s, Finite x ∧ |value x| ≤ 1) :
    Finite (F64SequentialSum.sum s) ∧
      |value (F64SequentialSum.sum s)-(s.map value).sum| ≤
        (s.length : ℝ) * (1/2000000000) := by
  have h := F64SequentialSum.sum_error 1048576 1 (by norm_num)
    (by norm_num [arithmeticEpsilon]) (by norm_num) s hn hx
  refine ⟨h.1,h.2.trans ?_⟩
  have hc : (1048576+1:ℝ)*(1+1)*arithmeticEpsilon ≤ 1/2000000000 := by
    norm_num [arithmeticEpsilon]
  nlinarith [Nat.cast_nonneg (α := ℝ) s.length]

theorem reductions_error (s : Array UInt64) (hn : s.size ≤ 1048576)
    (hx : ∀ x ∈ s, Finite x ∧ |value x| ≤ 1/2) :
    (Finite (sampleSum s) ∧
      |value (sampleSum s)-(s.toList.map value).sum| ≤ s.size*(1/1000000000)) ∧
    (Finite (sampleSquares s) ∧
      |value (sampleSquares s)-(s.toList.map fun x => value x^2).sum| ≤ s.size*(1/1000000000)) ∧
    (Finite (sampleCount s) ∧
      |value (sampleCount s)-(s.size:ℝ)| ≤ s.size*(1/1000000000)) := by
  have hs := reduction_error s.toList (by simpa using hn)
    (fun x hx' => ⟨(hx x (by simpa using hx')).1,
      (hx x (by simpa using hx')).2.trans (by norm_num)⟩)
  have hp (x : UInt64) (hx' : x ∈ s.toList) :
      Finite (Wasm.IEEE64.mul x x) ∧
        |value (Wasm.IEEE64.mul x x)-value x^2| ≤ arithmeticEpsilon ∧
        |value (Wasm.IEEE64.mul x x)| ≤ 1 := by
    obtain ⟨hf,hb⟩ := hx x (by simpa using hx')
    have hsq : |value x * value x| ≤ 1/4 := by
      rw [abs_mul]; nlinarith [abs_nonneg (value x)]
    have hm := F64ArithmeticBounds.mul_error x x hf hf 1 (by norm_num) (by norm_num)
      (hsq.trans (by norm_num))
    have hv := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hm.2 hsq
    refine ⟨hm.1,by simpa only [pow_two, mul_one] using hm.2,?_⟩
    have he : arithmeticEpsilon ≤ 1/4 := by norm_num [arithmeticEpsilon]
    simpa only [mul_one] using hv.trans (by linarith)
  have hsquares := reduction_error (s.toList.map fun x => Wasm.IEEE64.mul x x)
    (by simpa using hn) (by
      intro w hw
      obtain ⟨x,hx',rfl⟩ := List.mem_map.mp hw
      exact ⟨(hp x hx').1,(hp x hx').2.2⟩)
  have hproducts := sum_error_bound s.toList (fun x => value (Wasm.IEEE64.mul x x))
    (fun x => value x^2) arithmeticEpsilon (fun x hx' => (hp x hx').2.1)
  have hc := reduction_error (s.toList.map fun _ => (0x3FF0000000000000 : UInt64))
    (by simpa using hn) (by
      intro w hw
      obtain ⟨x,hx',rfl⟩ := List.mem_map.mp hw
      exact ⟨by unfold CodeLib.IEEE64.Finite; decide,by simp [value_one]⟩)
  rw [sampleSum_model, sampleSquares_model, sampleCount_model]
  simp only [List.length_map, Array.length_toList, List.map_map, Function.comp_def] at hs hsquares hc hproducts ⊢
  have hcerror := hc.2
  simp only [value_one, List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one,
    Array.length_toList] at hcerror
  have hn0 : (0:ℝ) ≤ s.size := Nat.cast_nonneg _
  have he : arithmeticEpsilon ≤ 1/2000000000 := by norm_num [arithmeticEpsilon]
  refine ⟨⟨hs.1,by linarith [hs.2]⟩,⟨hsquares.1,?_⟩,⟨hc.1,?_⟩⟩
  · have ht := abs_sub_le (value (F64SequentialSum.sum (s.toList.map fun x => Wasm.IEEE64.mul x x)))
      (s.toList.map fun x => value (Wasm.IEEE64.mul x x)).sum (s.toList.map fun x => value x^2).sum
    nlinarith [hsquares.2, mul_le_mul_of_nonneg_left he hn0]
  · simpa only [List.map_const', Array.length_toList] using hcerror.trans (by nlinarith)

theorem quotient_error (a b : UInt64) (n v : ℝ) (ha : Finite a) (hb : Finite b)
    (hn : 1 ≤ n) (hv : |v| ≤ 1)
    (hea : |value a-n*v| ≤ n*(1/1000000000))
    (heb : |value b-n| ≤ n*(1/1000000000)) :
    Finite (LeanExe.IEEE64.divBits a b) ∧
      |value (LeanExe.IEEE64.divBits a b)-v| ≤ 1/100000000 := by
  have hn0 : 0 < n := by linarith
  have hbpos : 0 < value b := by linarith [(abs_le.mp heb).1]
  have hblower : n/2 ≤ value b := by linarith [(abs_le.mp heb).1]
  have haBound : |value a| ≤ n*(1+1/1000000000) := by
    have ht := abs_add_le (value a-n*v) (n*v)
    rw [sub_add_cancel, abs_mul, abs_of_pos hn0] at ht
    nlinarith
  have hquot : |value a/value b| ≤ 3 := by
    rw [abs_div, abs_of_pos hbpos]
    apply (div_le_iff₀ hbpos).mpr
    linarith
  have hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0 := by
    intro hz
    have hv0 : value b = 0 := by simp [value, Wasm.IEEE64.scaledValue, hz]
    linarith
  have hr := F64ArithmeticBounds.div_error a b ha hb hb0 3 (by norm_num) (by norm_num) hquot
  have he : |value a/value b-v| ≤ 4/1000000000 := by
    have ht := abs_add_le (value a-n*v) (v*(n-value b))
    have hi : value a-n*v+v*(n-value b) = value a-v*value b := by ring
    rw [hi, abs_mul, abs_sub_comm n (value b)] at ht
    have hm : |v| * |value b-n| ≤ n*(1/1000000000) :=
      (mul_le_mul_of_nonneg_right hv (abs_nonneg _)).trans (by simpa using heb)
    rw [show value a/value b-v = (value a-v*value b)/value b by field_simp,
      abs_div, abs_of_pos hbpos]
    apply (div_le_iff₀ hbpos).mpr
    linarith
  rw [Operations.div]
  refine ⟨hr.1,?_⟩
  have ht := abs_sub_le (value (Wasm.IEEE64.div a b)) (value a/value b) v
  have heps : arithmeticEpsilon*3 ≤ 1/1000000000 := by norm_num [arithmeticEpsilon]
  linarith [hr.2]

theorem exact_moments (s : Array UInt64) (hn : 0 < s.size)
    (hx : ∀ x ∈ s, |value x| ≤ 1/2) :
    |exactMean s| ≤ 1/2 ∧ 0 ≤ exactSecond s ∧ exactSecond s ≤ 1/4 := by
  have hnR : (0:ℝ) < s.size := by exact_mod_cast hn
  have hm := sum_abs_bound s.toList value (1/2) (by simpa using hx)
  have hsq := sum_abs_bound s.toList (fun x => value x^2) (1/4) (by
    intro x h
    have hb := hx x (by simpa using h)
    rw [abs_of_nonneg (sq_nonneg _)]
    have hab := abs_le.mp hb
    nlinarith [sq_abs (value x)])
  simp only [Array.length_toList] at hm hsq
  refine ⟨?_,?_,?_⟩
  · rw [exactMean, abs_div, abs_of_pos hnR]
    exact (div_le_iff₀ hnR).mpr (by linarith)
  · unfold exactSecond
    exact div_nonneg (List.sum_nonneg (by
      intro x hx'
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hx'
      exact sq_nonneg _)) hnR.le
  · unfold exactSecond
    apply (div_le_iff₀ hnR).mpr
    exact (le_abs_self _).trans (by simpa [mul_comm] using hsq)

theorem bounded_fold (xs : List UInt64) (bound : UInt64) (initial : Bool) :
    xs.foldl (fun valid x => valid && decide ((x &&& 0x7FFFFFFFFFFFFFFF) ≤ bound)) initial = true ↔
      initial = true ∧ ∀ x ∈ xs, (x &&& 0x7FFFFFFFFFFFFFFF) ≤ bound := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, and_assoc]

theorem samplesBounded_spec (s : Array UInt64) (bound : UInt64) :
    samplesBounded s bound = true ↔ ∀ x ∈ s, (x &&& 0x7FFFFFFFFFFFFFFF) ≤ bound := by
  simpa [samplesBounded, Array.foldl_toList] using bounded_fold s.toList bound true

theorem stats_success_data (s : Array UInt64) (hs : (scalarStats s).status = 0) :
    0 < s.size ∧ s.size ≤ 1048576 ∧
      scalarStats s = ⟨0,LeanExe.IEEE64.divBits (sampleSum s) (sampleCount s),
        LeanExe.IEEE64.divBits (sampleSquares s) (sampleCount s)⟩ := by
  unfold scalarStats at hs ⊢
  split at hs
  · exact False.elim ((by decide : (1:UInt64) ≠ 0) hs)
  · rename_i hg
    have hg' := hg
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or, not_lt] at hg'
    refine ⟨?_,hg'.1.2,?_⟩
    · by_contra hn
      have hz : s.size = 0 := by omega
      exact hg'.1.1 (by simp [Array.isEmpty, hz])
    · simp only [if_neg hg]

/-- Error in the actual computed mean and second moment, including count
accumulation, rounded squares and division. -/
theorem stats_error (s : Array UInt64) (hs : (scalarStats s).status = 0)
    (hx : ∀ x ∈ s, Finite x ∧ |value x| ≤ 1/2) :
    (Finite (scalarStats s).mean ∧ |value (scalarStats s).mean-exactMean s| ≤ 1/100000000) ∧
    (Finite (scalarStats s).second ∧ |value (scalarStats s).second-exactSecond s| ≤ 1/100000000) := by
  obtain ⟨hn,hl,heq⟩ := stats_success_data s hs
  have hred := reductions_error s hl hx
  have hm := exact_moments s hn (fun x h => (hx x h).2)
  have hnR : (1:ℝ) ≤ s.size := by exact_mod_cast hn
  have hn0 : (s.size:ℝ) ≠ 0 := by positivity
  have heMean : (s.toList.map value).sum = (s.size:ℝ)*exactMean s := by
    unfold exactMean; field_simp
  have heSecond : (s.toList.map fun x => value x^2).sum = (s.size:ℝ)*exactSecond s := by
    unfold exactSecond; field_simp
  rw [heMean] at hred
  rw [heSecond] at hred
  rw [heq]
  exact ⟨quotient_error _ _ _ _ hred.1.1 hred.2.2.1 hnR (hm.1.trans (by norm_num))
      hred.1.2 hred.2.2.2,
    quotient_error _ _ _ _ hred.2.1.1 hred.2.2.1 hnR
      (by rw [abs_of_nonneg hm.2.1]; linarith [hm.2.2]) hred.2.1.2 hred.2.2.2⟩

#print axioms stats_error
#print axioms reductions_error
#print axioms quotient_error
end Project.SpectralKL.Scalar
