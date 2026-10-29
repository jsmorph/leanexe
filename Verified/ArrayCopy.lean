import Verified.HeapStep
import Verified.LocalFrame
import Verified.RuntimeFacts
import Verified.AllocCost
import Verified.ArrayCopyCode
import LeanExe.Pipeline.RuntimeSpec
import LeanExe.ProofKit.ArrayPrefix

/-! The specifications of the code that allocates arrays and copies them into new blocks. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The address of element `k` of the array at `ptr`. -/
theorem element_address (ptr : UInt64) (k : Nat) :
    (ptr + (UInt64.ofNat k + 1) * 8).toUInt32 = UInt64Array.wordAddress ptr (k + 1) := by
  unfold UInt64Array.wordAddress
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

/-- An array after a write of element `k`: the array with that element replaced. -/
theorem _root_.LeanExe.ProofKit.UInt64Array.At.writeElement {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : UInt64Array.At store ptr values) {k : Nat}
    (hk : k < values.size) (v : UInt64) :
    UInt64Array.At (UInt64Array.writeElement store ptr k v) ptr (values.set k v hk) := by
  have hFit := h.1
  refine ⟨by simpa using h.1, by simpa using h.2.1, ?_, fun j hj => ?_⟩
  · rw [Array.size_set]
    refine (Memory.read64_write64_disjoint store.mem _ _ ptr.toUInt32 (Or.inl ?_)).trans
      h.lengthRead
    rw [UInt64Array.wordAddress_toNat hFit (by omega), Memory.toUInt32_toNat,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Array.size_set] at hj
    rw [Array.getElem_set]
    show (store.mem.write64 (UInt64Array.wordAddress ptr (k + 1)) v).read64
      (UInt64Array.wordAddress ptr (j + 1)) = _
    split
    · subst k
      exact Memory.read64_write64 ..
    · rw [Memory.read64_write64_disjoint _ _ _ _ (by
        rw [UInt64Array.wordAddress_toNat hFit (by omega),
          UInt64Array.wordAddress_toNat hFit (by omega)]
        omega)]
      exact h.elementRead j hj

/-- `words` with elements `k` to `k + i - 1` replaced by the first `i` elements of `xs`. -/
def overlay (words xs : Array UInt64) (k i : Nat) : Array UInt64 :=
  Array.ofFn (n := words.size) fun j =>
    if k ≤ j.val ∧ j.val < k + i then xs[j.val - k]! else words[j.val]

theorem overlay_size (words xs : Array UInt64) (k i : Nat) :
    (overlay words xs k i).size = words.size := Array.size_ofFn

theorem overlay_zero (words xs : Array UInt64) (k : Nat) : overlay words xs k 0 = words := by
  apply Array.ext (overlay_size ..) fun j _ _ => ?_
  simp only [overlay, Array.getElem_ofFn]
  rw [ite_eq_right (by omega)]

theorem overlay_succ {words xs : Array UInt64} {k i : Nat} (hki : k + i < words.size)
    (hi : i < xs.size) :
    (overlay words xs k i).set (k + i) xs[i] (by rw [overlay_size]; exact hki) =
      overlay words xs k (i + 1) := by
  apply Array.ext (by simp [overlay_size]) fun j h1 _ => ?_
  rw [Array.getElem_set]
  simp only [overlay, Array.getElem_ofFn]
  by_cases hj : k + i = j
  · subst hj
    rw [ite_eq_left rfl, ite_eq_left (by omega), Nat.add_sub_cancel_left, getElem!_pos xs i hi]
  · rw [ite_eq_right hj]
    by_cases hin : k ≤ j ∧ j < k + i
    · rw [ite_eq_left hin, ite_eq_left (by omega)]
    · rw [ite_eq_right hin, ite_eq_right (by omega)]

/-- The address of element `k + i` of the array at `ptr`, from `ptr + 8 * k` and `i`. -/
theorem element_address_at (ptr : UInt64) (k i : Nat) :
    (ptr + UInt64.ofNat (8 * k) + (UInt64.ofNat i + 1) * 8).toUInt32 =
      UInt64Array.wordAddress ptr (k + i + 1) := by
  unfold UInt64Array.wordAddress
  congr 1
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

end Verified
