import Project.ProofKit.PackedByteMemory
import Project.ProofKit.FixedArrayCopy
import Project.ProofKit.PackedGenerateLoop

namespace Project.ProofKit.PackedByteGenerateLoop

open Wasm Project.Common PackedMemory PackedByteSource Memory FixedArrayCopy

def body (counterLocal lengthLocal pointerLocal : Nat) (byteCode : Wasm.Program) : Wasm.Program :=
  [.localGet counterLocal, .constI64 1, .mulI64, .localGet lengthLocal,
    .geUI64, .br_if 1, .localGet pointerLocal, .localGet counterLocal,
    .constI64 1, .mulI64, .addI64, .wrapI64] ++ byteCode ++
  [.wrapI64, .store8 0, .localGet counterLocal, .constI64 1, .addI64,
    .localSet counterLocal, .br 0]

def program (counterLocal lengthLocal pointerLocal : Nat) (byteCode : Wasm.Program) : Wasm.Program :=
  [.block 0 0 [.loop 0 0 (body counterLocal lengthLocal pointerLocal byteCode)]]

def Ready (counterLocal lengthLocal pointerLocal count index : Nat)
    (pointer : UInt64) (frame : Locals) : Prop :=
  frame.values = [] ∧
  frame.get counterLocal = some (.i64 (UInt64.ofNat index)) ∧
  frame.get lengthLocal = some (.i64 (UInt64.ofNat count)) ∧
  frame.get pointerLocal = some (.i64 pointer) ∧
  frame.validIndex counterLocal

def address (pointer : UInt64) (index : Nat) : UInt32 :=
  (pointer + UInt64.ofNat index * 1).toUInt32

theorem address_toNat (pointer : UInt64) (count index : Nat)
    (hfit : pointer.toNat + count ≤ 2^32) (hindex : index < count) :
    (address pointer index).toNat = pointer.toNat + index := by
  simp only [address, UInt64.toNat_toUInt32, UInt64.toNat_add,
    UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.toNat_ofNat]
  omega

theorem ready_advance {counterLocal lengthLocal pointerLocal count index : Nat}
    {pointer : UInt64} {frame : Locals}
    (hready : Ready counterLocal lengthLocal pointerLocal count index pointer frame)
    (hlength : lengthLocal ≠ counterLocal) (hpointer : pointerLocal ≠ counterLocal) :
    Ready counterLocal lengthLocal pointerLocal count (index + 1) pointer
      (counterFrame frame counterLocal (index + 1) hready.2.2.2.2) := by
  exact ⟨rfl, counterFrame_get_counter ..,
    (counterFrame_get_ne _ _ _ _ _ hlength).trans hready.2.2.1,
    (counterFrame_get_ne _ _ _ _ _ hpointer).trans hready.2.2.2.1,
    (counterFrame_validIndex ..).2 hready.2.2.2.2⟩

theorem program_spec (counterLocal lengthLocal pointerLocal : Nat) (byteCode : Wasm.Program)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (pointer : UInt64) (count : Nat) (value : Nat → UInt8) (P : Locals → Prop)
    (hlength : lengthLocal ≠ counterLocal) (hpointer : pointerLocal ≠ counterLocal)
    (hready : Ready counterLocal lengthLocal pointerLocal count 0 pointer frame)
    (hP : P frame)
    (hfit : pointer.toNat + count ≤ 2^32)
    (hbound : pointer.toNat + count ≤ initial.mem.pages * 65536)
    (hadvance : ∀ next index (h : next.validIndex counterLocal), P next →
      P (counterFrame next counterLocal index h))
    (hbyte : ∀ current next index,
      index < count → Ready counterLocal lengthLocal pointerLocal count index pointer next →
      P next → WritesRange initial current pointer.toNat (pointer.toNat + count) →
      ∀ (Q : Assertion Unit) rest,
      (∀ result, Ready counterLocal lengthLocal pointerLocal count index pointer result → P result →
        wp module_ rest Q current
          { result with values := [.i64 (value index).toUInt64, .i32 (address pointer index)] } env) →
      wp module_ (byteCode ++ rest) Q current
        { next with values := [.i32 (address pointer index)] } env)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hdone : ∀ final result,
      Ready counterLocal lengthLocal pointerLocal count count pointer result → P result →
      ByteArrayAt final.mem pointer.toNat (LeanExe.Packed.generateUInt8 count value) →
      WritesRange initial final pointer.toNat (pointer.toNat + count) →
      wp module_ rest Q final result env) :
    wp module_ (program counterLocal lengthLocal pointerLocal byteCode ++ rest) Q initial frame env := by
  let Inv : AssertionF Unit := fun current next => ∃ index, index ≤ count ∧
    Ready counterLocal lengthLocal pointerLocal count index pointer next ∧ P next ∧
    ByteArrayAt current.mem pointer.toNat (bytePrefix index value) ∧
    WritesRange initial current pointer.toNat (pointer.toNat + count)
  have hcount : count < UInt64.size := by change count < 18446744073709551616; omega
  have hentryValues := hready.1
  simp only [program, List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := Inv) (μ := PackedGenerateLoop.measure counterLocal count)
  · refine ⟨0, by omega, hready, hP, ?_, WritesRange.refl ..⟩
    refine ⟨by simpa using (show pointer.toNat ≤ 2^32 by omega),
      by simpa using (show pointer.toNat ≤ initial.mem.pages * 65536 by omega), ?_⟩
    intro index hindex
    simp only [bytePrefix_size] at hindex
    omega
  · rintro current next ⟨index, hindex, hready, hP, hbytes, hwrites⟩
    have hindex64 : index < UInt64.size := lt_of_le_of_lt hindex hcount
    have hmul : UInt64.ofNat index * 1 = UInt64.ofNat index := by
      simp
    have hindexNat := UInt64.toNat_ofNat_of_lt' hindex64
    simp only [body, List.cons_append, List.nil_append,
      wp_localGet_cons, Frame.withValues_get, hready.1, hready.2.1, hready.2.2.1,
      wp_constI64_cons, wp_mulI64_cons, hmul, wp_geUI64_cons, wp_br_if_cons]
    by_cases hlast : index = count
    · subst index
      have hguard : UInt64.ofNat count ≥ UInt64.ofNat count := by simp
      rw [ite_eq_left hguard]
      simp [hentryValues]
      have hempty : ({ next with values := [] } : Locals) = next := by
        exact Frame.ext _ _ rfl rfl hready.1.symm
      simpa only [hempty, generate_eq_bytePrefix] using
        hdone current next hready hP (by rwa [generate_eq_bytePrefix]) hwrites
    · have hlt : index < count := by omega
      have hguard : ¬UInt64.ofNat count ≤ UInt64.ofNat index := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hcount,
          UInt64.toNat_ofNat_of_lt' hindex64]
        omega
      simp only [ge_iff_le, hguard, ite_false, hready.2.2.2.1,
        wp_addI64_cons, wp_wrapI64_cons]
      have hruntime : UInt32.ofNat ((pointer + UInt64.ofNat index).toNat % 2^32) =
          address pointer index := by
        rw [← hmul]
        exact (Project.Common.toUInt32_eq_ofNat _).symm
      rw [hruntime]
      change wp module_ (byteCode ++ _) _ current
        { next with values := [.i32 (address pointer index)] } env
      apply hbyte current next index hlt hready hP hwrites
      intro result hresult hPresult
      have haddr := address_toNat pointer count index hfit hlt
      have hmem : (address pointer index).toNat + 1 ≤ current.mem.pages * 65536 := by
        rw [haddr, hwrites.2.1]
        omega
      have hsucc : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by simp
      have hcast : (UInt32.ofNat ((value index).toUInt64.toNat % 2^32)).toUInt8 = value index := by simp
      simp only [wp_wrapI64_cons, wp_store8_cons,
        hcast, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero,
        Nat.not_lt.mpr hmem, ite_false, wp_localGet_cons, Frame.withValues_get,
        hresult.2.1, wp_constI64_cons, wp_addI64_cons, hsucc, wp_localSet_cons,
        PackedGenerateLoop.setCounter result counterLocal (index + 1) _ hresult.2.2.2.2, wp_br_cons,
        List.take_zero, List.drop_zero, List.nil_append]
      refine ⟨?_, ?_⟩
      · refine ⟨index + 1, by omega, ready_advance hresult hlength hpointer,
          hadvance _ _ _ hPresult, ?_, ?_⟩
        · exact PackedByteMemory.write8_bytePrefix _ _ _ _ _ hbytes haddr (by omega)
            (by rw [hwrites.2.1]; omega)
        · exact hwrites.trans (PackedByteMemory.write8_range _ _ _ _ _ (by rw [haddr]; omega)
            (by rw [haddr]; omega))
      · change PackedGenerateLoop.measure counterLocal count _
            (counterFrame result counterLocal (index + 1) hresult.2.2.2.2) <
          PackedGenerateLoop.measure counterLocal count current next
        simp only [PackedGenerateLoop.measure, counterFrame_get_counter, hready.2.1,
          UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by omega), hindexNat]
        omega

#print axioms program_spec

end Project.ProofKit.PackedByteGenerateLoop
