import Project.PackedRead.Program
import Project.ProofKit.PackedMemory
import LeanExe.Examples.Packed
import Interpreter.Wasm.Wp.Tactic

namespace Project.PackedRead.Spec

open Wasm Project.Common Project.ProofKit.PackedMemory

theorem readWord_exact (env : HostEnv Unit) (initial : Store Unit)
    (ptr : UInt64) (bytes : ByteArray) (offset : Nat)
    (hbytes : ByteArrayAt initial.mem ptr.toNat bytes)
    (hvalid : offset + 4 ≤ bytes.size) :
    TerminatesWith env «module» 0 initial
      [.i64 (UInt64.ofNat offset), .i64 (UInt64.ofNat bytes.size), .i64 ptr]
      (fun final values => final = initial ∧
        values = [.i64 (LeanExe.Examples.Packed.readWord bytes offset).toUInt64]) := by
  have hsize : bytes.size < UInt64.size := by
    have := hbytes.1
    change bytes.size < 18446744073709551616
    omega
  have hoffset : offset < UInt64.size := by omega
  have hle : UInt64.ofNat offset ≤ UInt64.ofNat bytes.size := by
    simp only [UInt64.le_iff_toNat_le, toNat_ofNat_lt hoffset, toNat_ofNat_lt hsize]
    omega
  have hsub : 4 ≤ UInt64.ofNat bytes.size - UInt64.ofNat offset := by
    simp only [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ hle,
      toNat_ofNat_lt hoffset, toNat_ofNat_lt hsize]
    change 4 ≤ bytes.size - offset
    omega
  have haddress : (ptr + UInt64.ofNat offset).toUInt32.toNat = ptr.toNat + offset := by
    have := hbytes.1
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_add,
      toNat_ofNat_lt hoffset]
    omega
  have hbound : (ptr + UInt64.ofNat offset).toUInt32.toNat + 4 ≤
      initial.mem.pages * 65536 := by
    have := hbytes.2.1
    rw [haddress]
    omega
  have hread := read32_eq_getUInt32LE initial.mem ptr.toNat bytes offset
    (ptr + UInt64.ofNat offset).toUInt32 hbytes hvalid haddress
  have hmask (word : UInt32) : word.toUInt64 &&& 4294967295 = word.toUInt64 := by
    apply UInt64.toNat.inj
    simp only [UInt64.toNat_and, UInt32.toNat_toUInt64]
    change word.toNat &&& (2^32 - 1) = word.toNat
    exact Nat.and_two_pow_sub_one_of_lt_two_pow word.toNat_lt
  simp at hbound
  have haddr : UInt32.ofNat ((ptr.toNat + offset) % 4294967296) =
      (ptr + UInt64.ofNat offset).toUInt32 := by
    apply UInt32.toNat.inj
    rw [toUInt32_ofNat_mod_toNat, haddress]
    have := hbytes.1
    omega
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · simp [«module»]
  · change wp «module» func0 _ initial
      { params := [.i64 ptr, .i64 (UInt64.ofNat bytes.size), .i64 (UInt64.ofNat offset)],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0], values := [] } env
    unfold func0
    wp_run [Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp [hle])]
    wp_run [Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp [hsub])]
    wp_run [Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
    simp [hbound, hmask, LeanExe.Examples.Packed.readWord, func0Def]
    rw [haddr, hread]

#print axioms readWord_exact

end Project.PackedRead.Spec
