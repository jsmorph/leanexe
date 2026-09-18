import Project.PackedGenerate.Program
import Project.ProofKit.PackedGenerateLoop
import LeanExe.Examples.Packed

namespace Project.PackedGenerate.Spec

open Wasm Project.ProofKit Project.ProofKit.PackedGenerateLoop
open Project.ProofKit.PackedMemory Project.ProofKit.Memory

def wordProgram : Wasm.Program :=
  [.localGet 1, .constI64 4294967295, .andI64,
    .localGet 3, .constI64 4294967295, .andI64,
    .addI64, .constI64 4294967295, .andI64]

theorem emitted_loop : (func0.drop 42).take 1 = program 3 8 9 wordProgram := rfl

theorem mask32 (word : UInt64) :
    word &&& 4294967295 = word.toUInt32.toUInt64 := by
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_and, UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
  exact Nat.and_two_pow_sub_one_eq_mod word.toNat 32

theorem word_value (offset : UInt32) (index : Nat) :
    ((offset.toUInt64 &&& 4294967295) +
      (UInt64.ofNat index &&& 4294967295)) &&& 4294967295 =
      (offset + index.toUInt32).toUInt64 := by
  simp only [mask32, UInt64.toUInt32_add, UInt32.toUInt32_toUInt64,
    UInt64.toUInt32_ofNat']

theorem generated_loop_spec (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (pointer : UInt64) (count : Nat) (offset : UInt32)
    (hready : Ready 3 8 9 count 0 pointer frame)
    (hoffset : frame.get 1 = some (.i64 offset.toUInt64))
    (hfit : pointer.toNat + 4 * count ≤ 2^32)
    (hbound : pointer.toNat + 4 * count ≤ initial.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hdone : ∀ final result,
      Ready 3 8 9 count count pointer result →
      result.get 1 = some (.i64 offset.toUInt64) →
      ByteArrayAt final.mem pointer.toNat (LeanExe.Examples.Packed.makeWords count offset) →
      WritesRange initial final pointer.toNat (pointer.toNat + 4 * count) →
      wp «module» rest Q final result env) :
    wp «module» ((func0.drop 42).take 1 ++ rest) Q initial frame env := by
  rw [emitted_loop]
  apply program_spec 3 8 9 wordProgram «module» env initial frame pointer count
    (fun index => offset + index.toUInt32)
    (fun result => result.get 1 = some (.i64 offset.toUInt64))
    (by decide) (by decide) hready hoffset hfit hbound
  · intro next index hvalid h
    exact (FixedArrayCopy.counterFrame_get_ne _ _ _ _ _ (by decide)).trans h
  · intro current next index _ hready hoffset _ Q rest hnext
    simp only [wordProgram, List.cons_append, List.nil_append,
      wp_localGet_cons, Frame.withValues_get, hoffset, hready.2.1,
      wp_constI64_cons, wp_andI64_cons, wp_addI64_cons, word_value]
    exact hnext next hready hoffset
  · exact hdone

#print axioms emitted_loop
#print axioms generated_loop_spec

end Project.PackedGenerate.Spec
