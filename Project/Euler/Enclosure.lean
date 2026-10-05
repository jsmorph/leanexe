import Project.Euler.ReconstructedSpec
import Project.Euler.Outward
import Project.ProofKit.F64OutwardAccepted

/-! Real-number bounds for the reconstructed Euler solver: its outward operations agree with
the word-level outward operations of `Project.ProofKit.F64Outward`, whose results bound the exact
result from above or below. -/

namespace Project.Euler

open LeanExe.Examples.Euler Project.ProofKit

/-- A checked value as a word-level checked value. -/
def checkedWord (c : Checked) : Project.ProofKit.F64Outward.Checked := ⟨c.status, c.value.toBits⟩

theorem endpoint_word (up : Bool) (r : Float) :
    checkedWord (endpoint up r) = Project.ProofKit.F64Outward.endpoint up r.toBits := by
  have hn : (if up then nextUpBits r.toBits else nextDownBits r.toBits) =
      Project.ProofKit.F64Outward.neighbor up r.toBits := by
    cases up <;> simp [nextUpBits, nextDownBits, Project.ProofKit.F64Outward.neighbor,
      Project.ProofKit.F64Adjacent.nextUp, Project.ProofKit.F64Adjacent.nextDown]
  unfold endpoint Project.ProofKit.F64Outward.endpoint
  dsimp only
  rw [hn]
  generalize Project.ProofKit.F64Outward.neighbor up r.toBits = b
  by_cases h1 : r.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
    by_cases h2 : b &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
    simp [h1, h2, finite, absBits, Project.ProofKit.F64Order.finiteBits,
      Project.ProofKit.F64Order.absBits, checkedWord, rejectedChecked,
      Project.ProofKit.F64Outward.rejected, zero_toBits]
  exact toBits_ofBits_of_finite h2

open CodeLib.IEEE64 (value Finite)

theorem endpoint_rejected {up : Bool} {r : Float} (h : ¬(endpoint up r).status = 0) :
    endpoint up r = rejectedChecked := by
  unfold endpoint at h ⊢
  dsimp only at h ⊢
  generalize (if up then nextUpBits r.toBits else nextDownBits r.toBits) = w at h ⊢
  by_cases hc : (finite r && decide (absBits w < 0x7FF0000000000000)) = true
  · simp [hc] at h
  · simp only [hc, Bool.false_eq_true, ite_false]

theorem outAdd_word (up : Bool) (a b : Float) :
    checkedWord (outAdd up a b) = Project.ProofKit.F64Outward.add up a.toBits b.toBits := by
  unfold outAdd Project.ProofKit.F64Outward.add
  dsimp only
  rw [← F64Bits.toBits_add, ← endpoint_word]
  by_cases he : (endpoint up (a + b)).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hb : b.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      simp [ha, hb, he, finite, absBits, Project.ProofKit.F64Order.finiteBits,
        Project.ProofKit.F64Order.absBits, checkedWord, rejectedChecked,
        Project.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, rejectedChecked, Project.ProofKit.F64Outward.rejected, zero_toBits]

theorem outAdd_accepted {up : Bool} {a b : Float} (h : (outAdd up a b).status = 0) :
    Finite a.toBits ∧ Finite b.toBits ∧
      Project.ProofKit.F64Outward.Sound up (checkedWord (outAdd up a b)) (value a.toBits + value b.toBits) := by
  have := Project.ProofKit.F64Outward.add_accepted up a.toBits b.toBits
    (by rw [← outAdd_word]; exact h)
  rwa [← outAdd_word] at this

theorem outSub_word (up : Bool) (a b : Float) :
    checkedWord (outSub up a b) = Project.ProofKit.F64Outward.sub up a.toBits b.toBits := by
  unfold outSub Project.ProofKit.F64Outward.sub
  dsimp only
  rw [← F64Bits.toBits_sub, ← endpoint_word]
  by_cases he : (endpoint up (a - b)).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hb : b.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      simp [ha, hb, he, finite, absBits, Project.ProofKit.F64Order.finiteBits,
        Project.ProofKit.F64Order.absBits, checkedWord, rejectedChecked,
        Project.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, rejectedChecked, Project.ProofKit.F64Outward.rejected, zero_toBits]

theorem outSub_accepted {up : Bool} {a b : Float} (h : (outSub up a b).status = 0) :
    Finite a.toBits ∧ Finite b.toBits ∧
      Project.ProofKit.F64Outward.Sound up (checkedWord (outSub up a b)) (value a.toBits - value b.toBits) := by
  have := Project.ProofKit.F64Outward.sub_accepted up a.toBits b.toBits
    (by rw [← outSub_word]; exact h)
  rwa [← outSub_word] at this

theorem outMul_word (up : Bool) (a b : Float) :
    checkedWord (outMul up a b) = Project.ProofKit.F64Outward.mul up a.toBits b.toBits := by
  unfold outMul Project.ProofKit.F64Outward.mul
  dsimp only
  rw [← F64Bits.toBits_mul, ← endpoint_word]
  by_cases he : (endpoint up (a * b)).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hb : b.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      simp [ha, hb, he, finite, absBits, Project.ProofKit.F64Order.finiteBits,
        Project.ProofKit.F64Order.absBits, checkedWord, rejectedChecked,
        Project.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, rejectedChecked, Project.ProofKit.F64Outward.rejected, zero_toBits]

theorem outMul_accepted {up : Bool} {a b : Float} (h : (outMul up a b).status = 0) :
    Finite a.toBits ∧ Finite b.toBits ∧
      Project.ProofKit.F64Outward.Sound up (checkedWord (outMul up a b)) (value a.toBits * value b.toBits) := by
  have := Project.ProofKit.F64Outward.mul_accepted up a.toBits b.toBits
    (by rw [← outMul_word]; exact h)
  rwa [← outMul_word] at this

theorem outDiv_word (up : Bool) (a b : Float) :
    checkedWord (outDiv up a b) = Project.ProofKit.F64Outward.div up a.toBits b.toBits := by
  unfold outDiv Project.ProofKit.F64Outward.div
  dsimp only
  rw [← F64Bits.toBits_div, ← endpoint_word]
  by_cases he : (endpoint up (a / b)).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hb : b.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hz : 0 < b.toBits &&& 0x7FFFFFFFFFFFFFFF <;>
      simp [ha, hb, hz, he, finite, absBits, Project.ProofKit.F64Order.finiteBits,
        Project.ProofKit.F64Order.absBits, checkedWord, rejectedChecked,
        Project.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, rejectedChecked, Project.ProofKit.F64Outward.rejected, zero_toBits]

theorem outDiv_accepted {up : Bool} {a b : Float} (h : (outDiv up a b).status = 0) :
    Finite a.toBits ∧ Finite b.toBits ∧ Wasm.IEEE64.scaledMagnitude b.toBits ≠ 0 ∧
      Project.ProofKit.F64Outward.Sound up (checkedWord (outDiv up a b))
        (value a.toBits / value b.toBits) := by
  have := Project.ProofKit.F64Outward.div_accepted up a.toBits b.toBits
    (by rw [← outDiv_word]; exact h)
  rwa [← outDiv_word] at this

theorem outSqrt_word (up : Bool) (a : Float) :
    checkedWord (outSqrt up a) = Project.ProofKit.F64Outward.sqrt up a.toBits := by
  unfold outSqrt Project.ProofKit.F64Outward.sqrt
  dsimp only
  rw [← F64Bits.toBits_sqrt, ← endpoint_word]
  by_cases he : (endpoint up a.sqrt).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hs : a.toBits ≤ 0x8000000000000000 <;>
      simp [ha, hs, he, finite, absBits, Project.ProofKit.F64Order.finiteBits,
        Project.ProofKit.F64Order.absBits, checkedWord, rejectedChecked,
        Project.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, rejectedChecked, Project.ProofKit.F64Outward.rejected, zero_toBits]

theorem outSqrt_accepted {up : Bool} {a : Float} (h : (outSqrt up a).status = 0) :
    Finite a.toBits ∧ 0 ≤ value a.toBits ∧
      Project.ProofKit.F64Outward.Sound up (checkedWord (outSqrt up a))
        (Real.sqrt (value a.toBits)) := by
  have := Project.ProofKit.F64Outward.sqrt_accepted up a.toBits (by rw [← outSqrt_word]; exact h)
  rwa [← outSqrt_word] at this

end Project.Euler
