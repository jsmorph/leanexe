import Project.Gpt2CachedStep.ExpNeg.Perturbation
import Project.ProofKit.F32PairError
import Project.ProofKit.F32SumError
import Project.Softmax.RealPerturbation

namespace Project.Gpt2CachedStep.CachedAttention.SoftmaxError
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32

def shifted (scores : Nat → UInt32) (maximum : UInt32) (i : Nat) : UInt32 :=
  LeanExe.Float32.subBits (scores i) maximum

def exponential (scores : Nat → UInt32) (maximum : UInt32) (i : Nat) : UInt32 :=
  expNeg (shifted scores maximum i)

def denominator (scores : Nat → UInt32) (maximum : UInt32) (n : Nat) : UInt32 :=
  F32SumError.sumPrefix (exponential scores maximum) n

def probability (scores : Nat → UInt32) (maximum : UInt32) (n i : Nat) : UInt32 :=
  LeanExe.Float32.divBits (exponential scores maximum i) (denominator scores maximum n)

structure Bounds where
  subBound : Nat → Nat
  sumBound : Nat → Nat
  divBound : Nat → Nat
  expMul : Nat → Nat → Nat
  expAdd : Nat → Nat → Nat
  expSquare : Nat → Nat → Nat
  lower : ℝ

noncomputable def reference (scores : Nat → UInt32) (maximum : UInt32) (i : Nat) : ℝ :=
  Real.exp (value (scores i) - value maximum)

noncomputable def expError (scores : Nat → UInt32) (maximum : UInt32) (b : Bounds) (i : Nat) : ℝ :=
  ExpNeg.ForwardError.error (shifted scores maximum i) (b.expMul i) (b.expAdd i) (b.expSquare i) +
    F32AdditionBounds.epsilon (b.subBound i)

noncomputable def sumError (scores : Nat → UInt32) (maximum : UInt32) (b : Bounds) (n : Nat) : ℝ :=
  ∑ i ∈ Finset.range n, (expError scores maximum b i + F32AdditionBounds.epsilon (b.sumBound i))

noncomputable def error (scores : Nat → UInt32) (maximum : UInt32) (b : Bounds) (n i : Nat) : ℝ :=
  F32DivisionBounds.epsilon (b.divBound i) +
    (expError scores maximum b i + |reference scores maximum i /
      (∑ j ∈ Finset.range n, reference scores maximum j)| * sumError scores maximum b n) / b.lower

structure Ranges (scores : Nat → UInt32) (maximum : UInt32) (b : Bounds) (n : Nat) : Prop where
  scoreFinite : ∀ i < n, CodeLib.IEEE32.Finite (scores i)
  maximumFinite : CodeLib.IEEE32.Finite maximum
  maximumUpper : ∀ i < n, value (scores i) ≤ value maximum
  subUpper : ∀ i < n, b.subBound i ≤ 276
  subRange : ∀ i < n, (Wasm.IEEE32.scaledValue (scores i) - Wasm.IEEE32.scaledValue maximum).natAbs < 2 ^ b.subBound i
  shiftedNonpositive : ∀ i < n, value (shifted scores maximum i) ≤ 0
  cutoff : ∀ i < n, shifted scores maximum i > 0xC2800000 → value (shifted scores maximum i) ≤ -64
  expRanges : ∀ i < n, shifted scores maximum i ≤ 0xC2800000 →
    ExpNeg.ForwardError.Ranges (shifted scores maximum i) (b.expMul i) (b.expAdd i) (b.expSquare i)
  sumUpper : ∀ i < n, b.sumBound i ≤ 276
  sumRange : ∀ i < n, (Wasm.IEEE32.scaledValue (denominator scores maximum i) +
    Wasm.IEEE32.scaledValue (exponential scores maximum i)).natAbs < 2 ^ b.sumBound i
  lowerPositive : 0 < b.lower
  denominatorLower : b.lower ≤ |value (denominator scores maximum n)|
  denominatorNonzero : Wasm.IEEE32.scaledMagnitude (denominator scores maximum n) ≠ 0
  divLower : ∀ i < n, 24 ≤ b.divBound i
  divUpper : ∀ i < n, b.divBound i ≤ 275
  divRange : ∀ i < n, Wasm.IEEE32.scaledMagnitude (exponential scores maximum i) * 2 ^ 149 ≤
    Wasm.IEEE32.scaledMagnitude (denominator scores maximum n) * 2 ^ b.divBound i

theorem exponential_error (scores : Nat → UInt32) (maximum : UInt32) (b : Bounds) (n i : Nat)
    (h : Ranges scores maximum b n) (hi : i < n) :
    CodeLib.IEEE32.Finite (exponential scores maximum i) ∧
      |value (exponential scores maximum i) - reference scores maximum i| ≤ expError scores maximum b i := by
  have hs := F32PairError.sub_roundoff (scores i) maximum (b.subBound i)
    (h.scoreFinite i hi) h.maximumFinite (h.subUpper i hi) (h.subRange i hi)
  exact ExpNeg.Perturbation.exp_error _ _ _ _ _ _ (h.cutoff i hi) (h.expRanges i hi)
    (h.shiftedNonpositive i hi) (sub_nonpos.mpr (h.maximumUpper i hi)) hs.2

theorem denominator_error (scores : Nat → UInt32) (maximum : UInt32) (b : Bounds) (n : Nat)
    (h : Ranges scores maximum b n) :
    CodeLib.IEEE32.Finite (denominator scores maximum n) ∧
      |value (denominator scores maximum n) - ∑ i ∈ Finset.range n, reference scores maximum i| ≤
        sumError scores maximum b n := by
  exact F32SumError.ordered_error _ _ _ b.sumBound n
    (fun i hi => (exponential_error scores maximum b n i h hi).1)
    (fun i hi => (exponential_error scores maximum b n i h hi).2) h.sumUpper h.sumRange

theorem reference_sum_positive (scores : Nat → UInt32) (maximum : UInt32) (n : Nat) (hn : 0 < n) :
    0 < ∑ i ∈ Finset.range n, reference scores maximum i := by
  apply lt_of_lt_of_le (b := reference scores maximum 0) (Real.exp_pos _)
    (Finset.single_le_sum _ (Finset.mem_range.mpr hn))
  intro i _
  exact (Real.exp_pos _).le

theorem probability_error (scores : Nat → UInt32) (maximum : UInt32) (b : Bounds) (n i : Nat)
    (h : Ranges scores maximum b n) (hi : i < n) :
    CodeLib.IEEE32.Finite (probability scores maximum n i) ∧
      |value (probability scores maximum n i) - reference scores maximum i /
        (∑ j ∈ Finset.range n, reference scores maximum j)| ≤ error scores maximum b n i := by
  have he := exponential_error scores maximum b n i h hi
  have hd := denominator_error scores maximum b n h
  exact F32ErrorPropagation.div _ _ _ _ _ _ _ _ he.1 hd.1
    (h.divLower i hi) (h.divUpper i hi) h.denominatorNonzero (h.divRange i hi)
    h.lowerPositive h.denominatorLower (ne_of_gt (reference_sum_positive scores maximum n (by omega))) he.2 hd.2

theorem shift_invariant (scores : Nat → UInt32) (maximum : UInt32) (n i : Nat) :
    reference scores maximum i / (∑ j ∈ Finset.range n, reference scores maximum j) =
      Real.exp (value (scores i)) / (∑ j ∈ Finset.range n, Real.exp (value (scores j))) := by
  simp only [reference, Real.exp_sub, div_eq_mul_inv, ← Finset.sum_mul]
  field_simp

theorem probability_real (scores : Nat → UInt32) (maximum : UInt32) (b : Bounds) (n : Nat)
    (h : Ranges scores maximum b n) (i : Fin n) :
    CodeLib.IEEE32.Finite (probability scores maximum n i) ∧
      |value (probability scores maximum n i) -
        Project.Softmax.Real.probability (fun _ : Fin n => true) (fun j => value (scores j)) i| ≤
        error scores maximum b n i := by
  have he := probability_error scores maximum b n i h i.isLt
  rw [shift_invariant] at he
  simpa only [Project.Softmax.Real.probability, Project.Softmax.Real.weight,
    Bool.true_eq, ite_true, ← Fin.sum_univ_eq_sum_range] using he

#print axioms probability_real
end Project.Gpt2CachedStep.CachedAttention.SoftmaxError
