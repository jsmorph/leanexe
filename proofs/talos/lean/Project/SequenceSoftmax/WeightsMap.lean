import Project.SequenceSoftmax.Scalar
import Project.SequenceSoftmax.Model
import Project.ProofKit.ExactCall
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.ArrayPrefix
import Project.ProofKit.BlockLoop

namespace Project.SequenceSoftmax.Spec
open Wasm Project.ProofKit UInt64Array Memory

def weightsMapSuffix : Wasm.Program :=
  [.localGet 11, .localGet 12, .constI64 1, .mulI64, .constI64 1, .addI64,
   .constI64 8, .mulI64, .addI64, .wrapI64,
   .localGet 3, .f64ReinterpretI64, .localGet 2, .f64ReinterpretI64,
   .f64Sub, .i64ReinterpretF64, .localSet 4, .localGet 4, .call 5,
   .localSet 5, .localGet 5, .store64 0,
   .localGet 12, .constI64 1, .addI64, .localSet 12, .br 0]

def weightsMapBody : Wasm.Program :=
  FixedArrayTraversalInput.continuingProgram 9 12 10 3 ++ weightsMapSuffix

def weightsMapFrame (owner ptr maximum root : UInt64) (size index : Nat)
    (last argument result : UInt64) (tail : List Value) : Locals :=
  { params := [.i64 owner, .i64 ptr, .i64 maximum]
    locals := [.i64 last, .i64 argument, .i64 result, .i64 0, .i64 0, .i64 0,
      .i64 ptr, .i64 (UInt64.ofNat size), .i64 root, .i64 (UInt64.ofNat index),
      .i64 0, .i64 0] ++ tail
    values := [] }

macro "wp_weights_map" : tactic => `(tactic|
  simp +arith [wp_simp, Locals.get, Locals.set?, Locals.set, Locals.validIndex,
    weightsMapFrame, FixedArrayTraversalInput.dynamicResultFrame, Wasm.f64Sub])

def weightsMapInv (initial : Store Unit) (owner ptr maximum root : UInt64)
    (input : Array UInt64) (tail : List Value) : AssertionF Unit := fun st frame =>
  ∃ index last argument result, index ≤ input.size ∧
    frame = weightsMapFrame owner ptr maximum root input.size index last argument result tail ∧
    PrefixAt st root (weights input maximum) index ∧
    WritesRange initial st root.toNat (root.toNat+8*(input.size+1))

def weightsMapDone (initial : Store Unit) (owner ptr maximum root : UInt64)
    (input : Array UInt64) (tail : List Value) : AssertionF Unit := fun st frame =>
  ∃ last argument result,
    frame = weightsMapFrame owner ptr maximum root input.size input.size last argument result tail ∧
    UInt64Array.At st root (weights input maximum) ∧
    WritesRange initial st root.toNat (root.toNat+8*(input.size+1))

def weightsMapMeasure (input : Array UInt64) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 12 with
  | some (.i64 index) => input.size-index.toNat
  | _ => 0

theorem weightsMap_step (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr maximum root : UInt64) (input : Array UInt64) (tail : List Value)
    (hInput : UInt64Array.At initial ptr input)
    (hDisjoint : ptr.toNat+8*(input.size+1) ≤ root.toNat ∨
      root.toNat+8*(input.size+1) ≤ ptr.toNat)
    (st : Store Unit) (frame : Locals)
    (hInv : weightsMapInv initial owner ptr maximum root input tail st frame) :
    wp module weightsMapBody
      (BlockLoop.stepPost (weightsMapInv initial owner ptr maximum root input tail)
        (weightsMapDone initial owner ptr maximum root input tail)
        (weightsMapMeasure input) (weightsMapMeasure input st frame)) st frame env := by
  rcases hInv with ⟨index, last, argument, result, hIndex, rfl, hPrefix, hWrites⟩
  have hCurrent := hInput.writesRange hWrites hDisjoint
  have hIndexNat : (UInt64.ofNat index).toNat = index :=
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt hIndex hInput.size_lt)
  have hSizeNat : (UInt64.ofNat input.size).toNat = input.size :=
    UInt64.toNat_ofNat_of_lt' hInput.size_lt
  by_cases hEnd : index = input.size
  · subst index
    unfold weightsMapBody
    refine FixedArrayTraversalInput.continuingProgram_exit_spec 9 12 10 3 module env st _
      (UInt64.ofNat input.size) rfl (by simp +arith [weightsMapFrame, Locals.get])
      (by simp +arith [weightsMapFrame, Locals.get]) _ _ ?_
    exact ⟨last, argument, result, rfl, PrefixAt.complete (by simpa [weights] using hPrefix), hWrites⟩
  · have hi : index < input.size := by omega
    have hlt : UInt64.ofNat index < UInt64.ofNat input.size := by
      rw [UInt64.lt_iff_toNat_lt, hIndexNat, hSizeNat]
      exact hi
    unfold weightsMapBody
    refine FixedArrayTraversalInput.continuingProgram_spec 9 12 10 3 module env st _
      ptr (UInt64.ofNat index) (UInt64.ofNat input.size) input index rfl
      (by simp +arith [weightsMapFrame, Locals.get]) (by simp +arith [weightsMapFrame, Locals.get])
      (by simp +arith [weightsMapFrame, Locals.get]) rfl hlt
      (by simp [weightsMapFrame, Locals.validIndex]) hCurrent hi _ _ ?_
    unfold weightsMapSuffix
    wp_weights_map
    have hAddress := generatedElementAddress root index
    simp +arith at hAddress
    rw [hAddress]
    refine wp_call_exact_append (exponential_exact env st (Wasm.IEEE64.sub input[index] maximum))
      rfl rfl rfl [.i32 (wordAddress root (index+1))] rfl ?_
    have hBound := hPrefix.elementBound index (by simpa [weights] using hi)
    have hNext := hPrefix.write_next (by simpa [weights] using hi)
    have hFrame := writeElement_frame st root input.size index
      (ExpNeg.evaluate (Wasm.IEEE64.sub input[index] maximum)) (by simpa [weights] using hPrefix.1) hi
    wp_weights_map
    rw [ite_eq_right (show ¬65536*st.mem.pages ≤ (wordAddress root (index+1)).toNat+7 by omega)]
    constructor
    · refine ⟨index+1, input[index], Wasm.IEEE64.sub input[index] maximum,
        ExpNeg.evaluate (Wasm.IEEE64.sub input[index] maximum), by omega, ?_, ?_, hWrites.trans hFrame⟩
      · simp [weightsMapFrame, UInt64.ofNat_add]
      · simpa [writeElement, weights, hi] using hNext
    · have hNextMod : (index+1)%18446744073709551616 = index+1 :=
        Nat.mod_eq_of_lt (lt_of_le_of_lt (by omega) hInput.size_lt)
      simp +arith [weightsMapMeasure, Locals.get, hNextMod, hIndexNat]
      omega

theorem weightsMap_program_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr maximum root : UInt64) (input : Array UInt64) (tail : List Value)
    (hInput : UInt64Array.At initial ptr input)
    (hDisjoint : ptr.toNat+8*(input.size+1) ≤ root.toNat ∨
      root.toNat+8*(input.size+1) ≤ ptr.toNat)
    (hPrefix : PrefixAt initial root (weights input maximum) 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ st last argument result, UInt64Array.At st root (weights input maximum) →
      WritesRange initial st root.toNat (root.toNat+8*(input.size+1)) →
      wp module rest Q st
        (weightsMapFrame owner ptr maximum root input.size input.size last argument result tail) env) :
    wp module ([.block 0 0 [.loop 0 0 weightsMapBody]] ++ rest) Q initial
      (weightsMapFrame owner ptr maximum root input.size 0 0 0 0 tail) env := by
  refine BlockLoop.program_spec module env initial _ weightsMapBody
    (weightsMapInv initial owner ptr maximum root input tail)
    (weightsMapDone initial owner ptr maximum root input tail) (weightsMapMeasure input)
    ?_ ?_ ?_ (weightsMap_step env initial owner ptr maximum root input tail hInput hDisjoint) _ _ ?_
  · rintro st frame ⟨index, last, argument, result, _, rfl, _⟩
    rfl
  · rintro st frame ⟨last, argument, result, rfl, _⟩
    rfl
  · exact ⟨0, 0, 0, 0, Nat.zero_le _, rfl, hPrefix, WritesRange.refl ..⟩
  · rintro st frame ⟨last, argument, result, rfl, hOut, hWrites⟩
    exact hNext st last argument result hOut hWrites

#print axioms weightsMap_step
#print axioms weightsMap_program_spec
end Project.SequenceSoftmax.Spec
