import Verified.RuntimeFacts
import Verified.HeapStep
import Verified.LocalFrame
import Verified.TreeStorage
import Verified.TreeCopyCode
import Verified.TreeSelect

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem treeRecordBytes (shape : TreeShape) (r : Fin shape.records) :
    (8 * UInt64.ofNat (shape.width r)).toNat = 8 * shape.width r ∧
      allocSize (8 * UInt64.ofNat (shape.width r)) = 8 * UInt64.ofNat (shape.width r) := by
  have hPositive := shape.width_pos r
  have hShort := shape.width_le r
  obtain ⟨hBytes, hAligned⟩ := allocSize_words (size := shape.width r - 1) (by omega)
  have hEq : (UInt64.ofNat (shape.width r - 1) + 1) * 8 = 8 * UInt64.ofNat (shape.width r) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  rw [hEq] at hBytes hAligned
  exact ⟨by omega, hAligned⟩

end Verified
