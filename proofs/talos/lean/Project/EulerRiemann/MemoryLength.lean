import Project.EulerRiemann.MemoryWrite
import Project.ProofKit.FixedArrayResult

namespace Project.EulerRiemann.Memory
open Wasm Project.ProofKit.FixedArrayResult Project.ProofKit.Memory

theorem writeLength_prefix (store : Store Unit) (target : UInt64) (grid : Array Traversal.Cell)
    (hFit32 : target.toNat + 8 * (7 * grid.size + 1) ≤ 4294967296)
    (hFit : target.toNat + 8 * (7 * grid.size + 1) ≤ store.mem.pages * 65536) :
    PrefixAt (writeLength store target (UInt64.ofNat grid.size)) target grid 0 := by
  apply PrefixAt.empty _ _ _ hFit32
  · simpa only [writeLength_pages] using hFit
  · exact read64_write64 ..

theorem GridAt.writeLength_disjoint {store : Store Unit} {source target : UInt64}
    {grid : Array Traversal.Cell} (length : UInt64) (hGrid : GridAt store source grid)
    (hTarget32 : target.toNat + 8 ≤ 4294967296)
    (hSep : source.toNat + 8 * (7 * grid.size + 1) ≤ target.toNat ∨
      target.toNat + 8 ≤ source.toNat) :
    GridAt (writeLength store target length) source grid := by
  apply hGrid.frame
  · rw [writeLength_pages]
  · intro address hLow hHigh
    apply write64_bytes_outside
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    omega

#print axioms writeLength_prefix
#print axioms GridAt.writeLength_disjoint

end Project.EulerRiemann.Memory
