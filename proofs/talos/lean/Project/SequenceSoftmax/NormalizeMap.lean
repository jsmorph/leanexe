import Project.SequenceSoftmax.Program
import Project.SequenceSoftmax.Model
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.ArrayPrefix
import Project.ProofKit.BlockLoop

namespace Project.SequenceSoftmax.Spec
open Wasm Project.ProofKit UInt64Array Memory

def normalizeMapSuffix : Wasm.Program :=
  [.localGet 9, .localGet 10, .constI64 1, .mulI64, .constI64 1, .addI64,
   .constI64 8, .mulI64, .addI64, .wrapI64,
   .localGet 3, .f64ReinterpretI64, .localGet 2, .f64ReinterpretI64,
   .f64Div, .i64ReinterpretF64, .store64 0,
   .localGet 10, .constI64 1, .addI64, .localSet 10, .br 0]

def normalizeMapBody : Wasm.Program :=
  FixedArrayTraversalInput.continuingProgram 7 10 8 3 ++ normalizeMapSuffix

def normalizeMapFrame (owner ptr denominator root : UInt64) (size index : Nat)
    (last : UInt64) (tail : List Value) : Locals :=
  { params := [.i64 owner, .i64 ptr, .i64 denominator]
    locals := [.i64 last, .i64 0, .i64 0, .i64 0, .i64 ptr,
      .i64 (UInt64.ofNat size), .i64 root, .i64 (UInt64.ofNat index), .i64 0, .i64 0] ++ tail
    values := [] }

macro "wp_normalize_map" : tactic => `(tactic|
  simp +arith [wp_simp, Locals.get, Locals.set?, Locals.set, Locals.validIndex,
    normalizeMapFrame, FixedArrayTraversalInput.dynamicResultFrame, Wasm.f64Div])

def normalizeMapInv (initial : Store Unit) (owner ptr denominator root : UInt64)
    (input : Array UInt64) (tail : List Value) : AssertionF Unit := fun st frame =>
  ∃ index last, index ≤ input.size ∧
    frame = normalizeMapFrame owner ptr denominator root input.size index last tail ∧
    PrefixAt st root (normalize input denominator) index ∧
    WritesRange initial st root.toNat (root.toNat+8*(input.size+1))

def normalizeMapDone (initial : Store Unit) (owner ptr denominator root : UInt64)
    (input : Array UInt64) (tail : List Value) : AssertionF Unit := fun st frame =>
  ∃ last, frame = normalizeMapFrame owner ptr denominator root input.size input.size last tail ∧
    UInt64Array.At st root (normalize input denominator) ∧
    WritesRange initial st root.toNat (root.toNat+8*(input.size+1))

def normalizeMapMeasure (input : Array UInt64) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 10 with
  | some (.i64 index) => input.size-index.toNat
  | _ => 0

theorem normalizeMap_step (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr denominator root : UInt64) (input : Array UInt64) (tail : List Value)
    (hInput : UInt64Array.At initial ptr input)
    (hDisjoint : ptr.toNat+8*(input.size+1) ≤ root.toNat ∨
      root.toNat+8*(input.size+1) ≤ ptr.toNat)
    (st : Store Unit) (frame : Locals)
    (hInv : normalizeMapInv initial owner ptr denominator root input tail st frame) :
    wp module normalizeMapBody
      (BlockLoop.stepPost (normalizeMapInv initial owner ptr denominator root input tail)
        (normalizeMapDone initial owner ptr denominator root input tail)
        (normalizeMapMeasure input) (normalizeMapMeasure input st frame)) st frame env := by
  rcases hInv with ⟨index, last, hIndex, rfl, hPrefix, hWrites⟩
  have hCurrent := hInput.writesRange hWrites hDisjoint
  have hIndexNat : (UInt64.ofNat index).toNat = index :=
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt hIndex hInput.size_lt)
  have hSizeNat : (UInt64.ofNat input.size).toNat = input.size :=
    UInt64.toNat_ofNat_of_lt' hInput.size_lt
  by_cases hEnd : index = input.size
  · subst index
    unfold normalizeMapBody
    refine FixedArrayTraversalInput.continuingProgram_exit_spec 7 10 8 3 module env st _
      (UInt64.ofNat input.size) rfl (by simp +arith [normalizeMapFrame, Locals.get])
      (by simp +arith [normalizeMapFrame, Locals.get]) _ _ ?_
    exact ⟨last, rfl, PrefixAt.complete (by simpa [normalize] using hPrefix), hWrites⟩
  · have hi : index < input.size := by omega
    have hlt : UInt64.ofNat index < UInt64.ofNat input.size := by
      rw [UInt64.lt_iff_toNat_lt, hIndexNat, hSizeNat]
      exact hi
    unfold normalizeMapBody
    refine FixedArrayTraversalInput.continuingProgram_spec 7 10 8 3 module env st _
      ptr (UInt64.ofNat index) (UInt64.ofNat input.size) input index rfl
      (by simp +arith [normalizeMapFrame, Locals.get]) (by simp +arith [normalizeMapFrame, Locals.get])
      (by simp +arith [normalizeMapFrame, Locals.get]) rfl hlt
      (by simp [normalizeMapFrame, Locals.validIndex]) hCurrent hi _ _ ?_
    unfold normalizeMapSuffix
    wp_normalize_map
    have hAddress := generatedElementAddress root index
    simp +arith at hAddress
    rw [hAddress]
    have hBound := hPrefix.elementBound index (by simpa [normalize] using hi)
    have hBoundNat := hBound
    rw [← hAddress] at hBoundNat
    simp at hBoundNat
    have hNext := hPrefix.write_next (by simpa [normalize] using hi)
    have hFrame := writeElement_frame st root input.size index (Wasm.IEEE64.div input[index] denominator)
      (by simpa [normalize] using hPrefix.1) hi
    rw [ite_eq_right (show ¬65536*st.mem.pages ≤ (8*index+root.toNat+8)%4294967296+7 by omega)]
    constructor
    · refine ⟨index+1, input[index], by omega, ?_, ?_, hWrites.trans hFrame⟩
      · simp [normalizeMapFrame, UInt64.ofNat_add]
      · simpa [writeElement, normalize, hi] using hNext
    · have hNextMod : (index+1)%18446744073709551616 = index+1 :=
        Nat.mod_eq_of_lt (lt_of_le_of_lt (by omega) hInput.size_lt)
      simp +arith [normalizeMapMeasure, Locals.get, hNextMod, hIndexNat]
      omega

theorem normalizeMap_program_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr denominator root : UInt64) (input : Array UInt64) (tail : List Value)
    (hInput : UInt64Array.At initial ptr input)
    (hDisjoint : ptr.toNat+8*(input.size+1) ≤ root.toNat ∨
      root.toNat+8*(input.size+1) ≤ ptr.toNat)
    (hPrefix : PrefixAt initial root (normalize input denominator) 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ st last, UInt64Array.At st root (normalize input denominator) →
      WritesRange initial st root.toNat (root.toNat+8*(input.size+1)) →
      wp module rest Q st
        (normalizeMapFrame owner ptr denominator root input.size input.size last tail) env) :
    wp module ([.block 0 0 [.loop 0 0 normalizeMapBody]] ++ rest) Q initial
      (normalizeMapFrame owner ptr denominator root input.size 0 0 tail) env := by
  refine BlockLoop.program_spec module env initial _ normalizeMapBody
    (normalizeMapInv initial owner ptr denominator root input tail)
    (normalizeMapDone initial owner ptr denominator root input tail) (normalizeMapMeasure input)
    ?_ ?_ ?_ (normalizeMap_step env initial owner ptr denominator root input tail hInput hDisjoint) _ _ ?_
  · rintro st frame ⟨index, last, _, rfl, _⟩
    rfl
  · rintro st frame ⟨last, rfl, _⟩
    rfl
  · exact ⟨0, 0, Nat.zero_le _, rfl, hPrefix, WritesRange.refl ..⟩
  · rintro st frame ⟨last, rfl, hOut, hWrites⟩
    exact hNext st last hOut hWrites

#print axioms normalizeMap_step
#print axioms normalizeMap_program_spec
end Project.SequenceSoftmax.Spec
