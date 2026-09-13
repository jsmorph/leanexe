import Project.EulerRiemann.OutputMapLoad

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

structure OutputMapFrameAt (pressure : Bool) (base : Locals) (index : Nat)
    (frame : Locals) : Prop where
  paramsLength : frame.params.length = 5
  localsLength : frame.locals.length = 52
  values : frame.values = []
  counter : frame.get 39 = some (.i64 (UInt64.ofNat index))
  preserved : ∀ localIndex : Nat,
    (localIndex < outputItemStart pressure ∨ outputItemStart pressure + 7 ≤ localIndex) →
    localIndex ≠ 39 → frame.get localIndex = base.get localIndex

theorem OutputMapFrameAt.initial (pressure : Bool) (base : Locals) (index : Nat)
    (hParams : base.params.length = 5) (hLocals : base.locals.length = 52)
    (hValues : base.values = []) (hIndex : base.get 39 = some (.i64 (UInt64.ofNat index))) :
    OutputMapFrameAt pressure base index base :=
  ⟨hParams, hLocals, hValues, hIndex, fun _ _ _ => rfl⟩

theorem OutputMapFrameAt.loaded_valid {pressure : Bool} {base frame : Locals} {index : Nat}
    (h : OutputMapFrameAt pressure base index frame) (cell : Traversal.Cell) :
    (outputLoadedFrame pressure frame cell).validIndex 39 := by
  simp [Locals.validIndex, h.paramsLength, h.localsLength]

theorem OutputMapFrameAt.next {pressure : Bool} {base frame : Locals} {index : Nat}
    (h : OutputMapFrameAt pressure base index frame) (cell : Traversal.Cell) :
    OutputMapFrameAt pressure base (index + 1)
      (FixedArrayCopy.counterFrame (outputLoadedFrame pressure frame cell) 39 (index + 1)
        (h.loaded_valid cell)) := by
  refine ⟨?_, ?_, rfl, FixedArrayCopy.counterFrame_get_counter .., ?_⟩
  · simpa only [FixedArrayCopy.counterFrame_params_length, outputLoadedFrame_params]
      using h.paramsLength
  · simpa only [FixedArrayCopy.counterFrame_locals_length, outputLoadedFrame_length]
      using h.localsLength
  · intro localIndex hOther hNe
    rw [FixedArrayCopy.counterFrame_get_ne _ _ _ _ _ hNe,
      output_loaded_get_other _ _ _ _ h.paramsLength hOther]
    exact h.preserved localIndex hOther hNe

theorem output_map_increment_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (index : Nat) (hValid : frame.validIndex 39) (hValues : frame.values = [])
    (hIndex : frame.get 39 = some (.i64 (UInt64.ofNat index))) (Q : Assertion Unit)
    (hNext : Q (.Break 0 store (FixedArrayCopy.counterFrame frame 39 (index + 1) hValid))) :
    wp module [.localGet 39, .constI64 1, .addI64, .localSet 39, .br 0]
      Q store frame env := by
  have hAdd : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) :=
    (UInt64.ofNat_add index 1).symm
  simp only [wp_localGet_cons, hIndex, wp_constI64_cons, wp_addI64_cons,
    wp_localSet_cons, hValues, hAdd]
  have hLocal : 39 < frame.params.length + frame.locals.length := hValid
  by_cases hParam : 39 < frame.params.length
  · simpa [wp_br_cons, FixedArrayCopy.counterFrame, Locals.set, Locals.set?, hParam] using hNext
  · simpa [wp_br_cons, FixedArrayCopy.counterFrame, Locals.set, Locals.set?, hParam, hLocal] using hNext

#print axioms OutputMapFrameAt.next
#print axioms output_map_increment_spec

end Project.EulerRiemann.Execution
