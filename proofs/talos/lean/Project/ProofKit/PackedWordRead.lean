import Project.ProofKit.PackedMemory
import Project.ProofKit.CallRemainder
import Interpreter.Wasm.Wp.Tactic

namespace Project.ProofKit.PackedWordRead

open Wasm Project.Common PackedMemory

def program : Wasm.Program :=
  [
  .localGet 1,
  .localSet 5,
  .localGet 2,
  .localSet 6,
  .localGet 3,
  .localSet 8,
  .constI64 4,
  .localSet 9,
  .localGet 9,
  .constI64 0,
  .eqI64,
  .iff 0 1 [
   .constI64 0
  ] [
   .constI64 (-1),
   .localGet 9,
   .divUI64,
   .localGet 8,
   .ltUI64,
   .iff 0 1 [
    .unreachable
   ] [
    .localGet 8,
    .localGet 9,
    .mulI64
   ] [] [.i64]
  ] [] [.i64],
  .localSet 7,
  .localGet 7,
  .localGet 6,
  .leUI64,
  .iff 0 1 [
   .localGet 6,
   .localGet 7,
   .subI64,
   .constI64 4,
   .geUI64,
   .iff 0 1 [
    .localGet 5,
    .localGet 7,
    .addI64,
    .wrapI64,
    .load32 0,
    .extendUI32
   ] [
    .unreachable
   ] [] [.i64]
  ] [
   .unreachable
  ] [] [.i64],
  .localSet 4,
  .localGet 4
 ]

def function (typeIdx : Option Nat) : Wasm.Function :=
  { params := [.i64, .i64, .i64, .i64], locals := List.replicate 6 .i64,
    body := program, results := [.i64], typeIdx := typeIdx }

theorem exact (module_ : Wasm.Module) (id : Nat) (typeIdx : Option Nat)
    (himports : module_.imports = [])
    (hfunction : module_.funcs[id]? = some (function typeIdx))
    (env : HostEnv Unit) (initial : Store Unit) (owner ptr : UInt64)
    (bytes : ByteArray) (index : Nat)
    (hbytes : ByteArrayAt initial.mem ptr.toNat bytes)
    (hvalid : index * 4 + 4 ≤ bytes.size) :
    TerminatesWith env module_ id initial
      [.i64 (UInt64.ofNat index), .i64 (UInt64.ofNat bytes.size), .i64 ptr, .i64 owner]
      (fun final values => final = initial ∧
        values = [.i64 (LeanExe.Packed.getUInt32LE! bytes (index * 4)).toUInt64]) := by
  have hsize : bytes.size < UInt64.size := by
    have := hbytes.1
    change bytes.size < 18446744073709551616
    omega
  have hindex : index < UInt64.size := by omega
  have hoffset : index * 4 < UInt64.size := by omega
  have hmul : UInt64.ofNat index * 4 = UInt64.ofNat (index * 4) := by simp
  have hsafe : ¬ (-1 : UInt64) / 4 < UInt64.ofNat index := by
    simp only [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt hindex]
    change ¬ 4611686018427387903 < index
    have := hbytes.1
    omega
  have hle : UInt64.ofNat (index * 4) ≤ UInt64.ofNat bytes.size := by
    simp only [UInt64.le_iff_toNat_le, toNat_ofNat_lt hoffset, toNat_ofNat_lt hsize]
    omega
  have hsub : 4 ≤ UInt64.ofNat bytes.size - UInt64.ofNat (index * 4) := by
    simp only [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ hle,
      toNat_ofNat_lt hoffset, toNat_ofNat_lt hsize]
    change 4 ≤ bytes.size - index * 4
    omega
  have haddress : (ptr + UInt64.ofNat (index * 4)).toUInt32.toNat = ptr.toNat + index * 4 := by
    have := hbytes.1
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_add, toNat_ofNat_lt hoffset]
    omega
  have hbound : (ptr + UInt64.ofNat (index * 4)).toUInt32.toNat + 4 ≤
      initial.mem.pages * 65536 := by
    have := hbytes.2.1
    rw [haddress]
    omega
  have hread := read32_eq_getUInt32LE initial.mem ptr.toNat bytes (index * 4)
    (ptr + UInt64.ofNat (index * 4)).toUInt32 hbytes hvalid haddress
  have haddr : UInt32.ofNat ((ptr.toNat + index * 4) % 4294967296) =
      (ptr + UInt64.ofNat (index * 4)).toUInt32 := by
    apply UInt32.toNat.inj
    rw [toUInt32_ofNat_mod_toNat, haddress]
    have := hbytes.1
    omega
  simp at hbound
  apply TerminatesWith.of_wp_entry_for (f := function typeIdx) (hImp := by simp [himports])
  · simpa [himports] using hfunction
  · change wp module_ program _ initial
      { params := [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat bytes.size), .i64 (UInt64.ofNat index)],
        locals := List.replicate 6 (.i64 0), values := [] } env
    unfold program
    wp_run [Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    wp_run [Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simpa using hsafe)]
    wp_run [Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, hmul]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp only [hmul, hle, ite_true]; decide)]
    wp_run [Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp only [hmul, ge_iff_le, hsub, ite_true]; decide)]
    wp_run [Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
    simp [hbound, function]
    rw [haddr, hread]

#print axioms exact

end Project.ProofKit.PackedWordRead
