import Project.ProofKit.ArrayPrefix
import Project.ProofKit.PackedGenerateLoop
import Project.ProofKit.RangeGuard

namespace Project.ProofKit.WordArrayGenerateLoop
open Wasm Memory FixedArrayCopy UInt64Array

def body (counterLocal lengthLocal pointerLocal : Nat) (wordCode : Wasm.Program) : Wasm.Program :=
  RangeGuard.program counterLocal lengthLocal ++
  [.localGet pointerLocal, .localGet counterLocal, .constI64 1, .mulI64, .constI64 1,
    .addI64, .constI64 8, .mulI64, .addI64, .wrapI64] ++ wordCode ++
  [.store64 0, .localGet counterLocal, .constI64 1, .addI64, .localSet counterLocal, .br 0]

def program (counterLocal lengthLocal pointerLocal : Nat) (wordCode : Wasm.Program) : Wasm.Program :=
  [.block 0 0 [.loop 0 0 (body counterLocal lengthLocal pointerLocal wordCode)]]

def Ready (counterLocal lengthLocal pointerLocal count index : Nat)
    (pointer : UInt64) (frame : Locals) : Prop :=
  frame.values = [] ∧ frame.get counterLocal = some (.i64 (UInt64.ofNat index)) ∧
  frame.get lengthLocal = some (.i64 (UInt64.ofNat count)) ∧
  frame.get pointerLocal = some (.i64 pointer) ∧ frame.validIndex counterLocal

theorem ready_advance {counterLocal lengthLocal pointerLocal count index : Nat}
    {pointer : UInt64} {frame : Locals}
    (h : Ready counterLocal lengthLocal pointerLocal count index pointer frame)
    (hlength : lengthLocal ≠ counterLocal) (hpointer : pointerLocal ≠ counterLocal) :
    Ready counterLocal lengthLocal pointerLocal count (index + 1) pointer
      (counterFrame frame counterLocal (index + 1) h.2.2.2.2) :=
  ⟨rfl, counterFrame_get_counter ..,
    (counterFrame_get_ne _ _ _ _ _ hlength).trans h.2.2.1,
    (counterFrame_get_ne _ _ _ _ _ hpointer).trans h.2.2.2.1,
    (counterFrame_validIndex ..).2 h.2.2.2.2⟩

theorem program_spec (counterLocal lengthLocal pointerLocal : Nat) (wordCode : Wasm.Program)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (pointer : UInt64) (values : Array UInt64) (P : Locals → Prop)
    (hlength : lengthLocal ≠ counterLocal) (hpointer : pointerLocal ≠ counterLocal)
    (hready : Ready counterLocal lengthLocal pointerLocal values.size 0 pointer frame)
    (hP : P frame) (hEmpty : PrefixAt initial pointer values 0)
    (hadvance : ∀ next index (h : next.validIndex counterLocal), P next →
      P (counterFrame next counterLocal index h))
    (hword : ∀ current next index (hi : index < values.size),
      Ready counterLocal lengthLocal pointerLocal values.size index pointer next → P next →
      WritesRange initial current pointer.toNat (pointer.toNat + 8 * (values.size + 1)) →
      ∀ (Q : Assertion Unit) rest,
      (∀ result, Ready counterLocal lengthLocal pointerLocal values.size index pointer result → P result →
        wp module_ rest Q current
          { result with values := [.i64 values[index], .i32 (wordAddress pointer (index + 1))] } env) →
      wp module_ (wordCode ++ rest) Q current
        { next with values := [.i32 (wordAddress pointer (index + 1))] } env)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hdone : ∀ final result,
      Ready counterLocal lengthLocal pointerLocal values.size values.size pointer result → P result →
      At final pointer values →
      WritesRange initial final pointer.toNat (pointer.toNat + 8 * (values.size + 1)) →
      wp module_ rest Q final result env) :
    wp module_ (program counterLocal lengthLocal pointerLocal wordCode ++ rest) Q initial frame env := by
  let Inv : AssertionF Unit := fun current next => ∃ index, index ≤ values.size ∧
    Ready counterLocal lengthLocal pointerLocal values.size index pointer next ∧ P next ∧
    PrefixAt current pointer values index ∧
    WritesRange initial current pointer.toNat (pointer.toNat + 8 * (values.size + 1))
  have hcount : values.size < UInt64.size := by
    have := hEmpty.1
    change values.size < 18446744073709551616
    omega
  have hentryValues := hready.1
  simp only [program, List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := Inv) (μ := PackedGenerateLoop.measure counterLocal values.size)
  · exact ⟨0, by omega, hready, hP, hEmpty, WritesRange.refl ..⟩
  · rintro current next ⟨index, hindex, hready, hP, hprefix, hwrites⟩
    have hindex64 : index < UInt64.size := lt_of_le_of_lt hindex hcount
    simp only [body, List.append_assoc]
    apply RangeGuard.program_spec counterLocal lengthLocal _ _ _ _
      (UInt64.ofNat index) (UInt64.ofNat values.size) hready.1 hready.2.1 hready.2.2.1
    by_cases hlast : index = values.size
    · subst index
      rw [if_pos (show UInt64.ofNat values.size ≤ UInt64.ofNat values.size by simp)]
      have hempty : ({ next with values := [] } : Locals) = next :=
        Frame.ext _ _ rfl rfl hready.1.symm
      simpa only [List.take_zero, List.drop_zero, List.nil_append, hentryValues, hempty] using
        hdone current next hready hP hprefix.complete hwrites
    · have hlt : index < values.size := by omega
      have hguard : ¬ UInt64.ofNat values.size ≤ UInt64.ofNat index := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hcount,
          UInt64.toNat_ofNat_of_lt' hindex64]
        omega
      rw [if_neg hguard]
      simp only [List.cons_append, List.nil_append, wp_localGet_cons, Frame.withValues_get,
        hready.1, hready.2.1, hready.2.2.2.1, wp_constI64_cons, wp_mulI64_cons, wp_addI64_cons,
        wp_wrapI64_cons, generatedElementAddress]
      apply hword current next index hlt hready hP hwrites
      intro result hresult hPresult
      have hmem := hprefix.elementBound index hlt
      have hsucc : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by simp
      simp only [wp_store64_cons, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero,
        Nat.not_lt.mpr hmem, ite_false, wp_localGet_cons, Frame.withValues_get,
        hresult.2.1, wp_constI64_cons, wp_addI64_cons, hsucc, wp_localSet_cons,
        PackedGenerateLoop.setCounter result counterLocal (index + 1) _ hresult.2.2.2.2,
        wp_br_cons, List.take_zero, List.drop_zero, List.nil_append]
      constructor
      · exact ⟨index + 1, by omega, ready_advance hresult hlength hpointer,
          hadvance _ _ _ hPresult, hprefix.write_next hlt,
          hwrites.trans (writeElement_frame current pointer values.size index values[index] hprefix.1 hlt)⟩
      · change PackedGenerateLoop.measure counterLocal values.size _
            (counterFrame result counterLocal (index + 1) hresult.2.2.2.2) <
          PackedGenerateLoop.measure counterLocal values.size current next
        simp only [PackedGenerateLoop.measure, counterFrame_get_counter, hready.2.1,
          UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by omega),
          UInt64.toNat_ofNat_of_lt' hindex64]
        omega

#print axioms program_spec
end Project.ProofKit.WordArrayGenerateLoop
