import LeanExe.Dialect.Bytes
import LeanExe.ProofKit.MemoryFrame

namespace Verified.Bytes

open Wasm LeanExe.ProofKit

theorem index_address (root index : UInt64) (count : Nat)
    (hFit : root.toNat + count ≤ 4294967296) (hIndex : index.toNat < count) :
    (root + index).toUInt32.toNat = root.toNat + index.toNat := by
  have hSum : (root + index).toNat = root.toNat + index.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  rw [Memory.toUInt32_toNat, hSum, Nat.mod_eq_of_lt (by omega)]

structure At (mem : Mem) (root : UInt64) (bytes : LeanExe.Bytes) : Prop where
  address : root.toNat + bytes.data.size ≤ 4294967296
  memory : root.toNat + bytes.data.size ≤ mem.pages * 65536
  contents : ∀ (i : Nat) (hi : i < bytes.data.size),
    mem.bytes (root.toNat + i) = bytes.data[i]

theorem At.index_address {memory : Mem} {root : UInt64} {bytes : LeanExe.Bytes}
    (h : At memory root bytes) (index : UInt64) (hi : index.toNat < bytes.data.size) :
    (root + index).toUInt32.toNat = root.toNat + index.toNat :=
  Verified.Bytes.index_address root index bytes.data.size h.address hi

theorem At.read8 {memory : Mem} {root : UInt64} {bytes : LeanExe.Bytes}
    (h : At memory root bytes) (index : UInt64) (hi : index.toNat < bytes.data.size) :
    memory.read8 (root + index).toUInt32 = bytes.data[index.toNat] := by
  rw [Mem.read8, h.index_address index hi]
  exact h.contents _ hi

theorem At.frame {memory memory' : Mem} {root : UInt64} {bytes : LeanExe.Bytes}
    (h : At memory root bytes) (hPages : memory.pages ≤ memory'.pages)
    (hBytes : ∀ i < bytes.data.size,
      memory'.bytes (root.toNat + i) = memory.bytes (root.toNat + i)) :
    At memory' root bytes :=
  ⟨h.address, h.memory.trans (Nat.mul_le_mul_right 65536 hPages),
    fun i hi => (hBytes i hi).trans (h.contents i hi)⟩

theorem At.writesRange {store store' : Store α} {root : UInt64} {bytes : LeanExe.Bytes}
    {start stop : Nat} (h : At store.mem root bytes)
    (hWrites : Memory.WritesRange store store' start stop)
    (hApart : root.toNat + bytes.data.size ≤ start ∨ stop ≤ root.toNat) :
    At store'.mem root bytes :=
  h.frame hWrites.2.1.ge fun i hi => hWrites.2.2 _ (by omega)

end Verified.Bytes
