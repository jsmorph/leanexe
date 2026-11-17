import Verified.Shim
import LeanExe.A64.Proof.WasiPreopen

/-!
The stubs of the preopened directory against the shim's host environment.  `prestat_placed`
states the record that `prestatInvoke` writes for descriptor 3 while it is the preopened
directory as Talos's `write64` of `2^32`, the word that the stub of `fd_prestat_get` stores.
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

/-- Talos's `write64` as the write of its eight bytes, the lowest first. -/
theorem write64_writeBytes (m : Mem) (y : UInt32) (v : UInt64) :
    m.write64 y v = m.writeBytes y.toNat [(v &&& 0xFF).toUInt8, ((v >>> 8) &&& 0xFF).toUInt8,
      ((v >>> 16) &&& 0xFF).toUInt8, ((v >>> 24) &&& 0xFF).toUInt8, ((v >>> 32) &&& 0xFF).toUInt8,
      ((v >>> 40) &&& 0xFF).toUInt8, ((v >>> 48) &&& 0xFF).toUInt8,
      ((v >>> 56) &&& 0xFF).toUInt8] := by
  cases m with
  | mk pages bytes =>
    simp only [Mem.write64, Mem.writeBytes, List.length_cons, List.length_nil]
    congr 1
    funext i
    by_cases h : y.toNat ≤ i ∧ i < y.toNat + 8
    · rw [dif_pos h]
      obtain ⟨k, hk, rfl⟩ : ∃ k, k < 8 ∧ i = y.toNat + k := ⟨i - y.toNat, by omega, by omega⟩
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · rw [dif_neg h, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The record that `fd_prestat_get` writes for descriptor 3 while it is the preopened directory:
the word `2^32`. -/
theorem prestat_placed (m : Mem) (p : UInt32) :
    placeReply m (fun outputs => [(p, outputs.headD Bytes.empty)]) (prestatReply true 3) =
      m.write64 p (2 ^ 32) := by
  rw [write64_writeBytes]
  simp only [prestatReply, and_self, ↓reduceIte, placeReply, placeAll, List.headD_cons]
  rfl

end Verified.ShimA64
