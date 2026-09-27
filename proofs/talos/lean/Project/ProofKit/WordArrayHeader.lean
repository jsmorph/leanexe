import Project.ProofKit.FixedArrayResult
import Project.ProofKit.MemoryFrame

namespace Project.ProofKit.FixedArrayResult
open Wasm

theorem writeLength_frame (store : Store Unit) (root length : UInt64)
    (hRoot : root.toNat + 8 ≤ 4294967296) :
    Memory.WritesRange store (writeLength store root length) root.toNat (root.toNat + 8) := by
  apply Memory.WritesRange.write64
  all_goals rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]

theorem writeLength_read (store : Store Unit) (root length : UInt64) :
    (writeLength store root length).mem.read64 root.toUInt32 = length :=
  Memory.read64_write64 ..

#print axioms writeLength_frame
#print axioms writeLength_read
end Project.ProofKit.FixedArrayResult
