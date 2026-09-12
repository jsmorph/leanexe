import Project.EulerRiemann.InitialMapUpdate

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

structure InitialMapFrameAt (base : Locals) (index : Nat) (frame : Locals) : Prop where
  paramsLength : frame.params.length = 5
  localsLength : frame.locals.length = 61
  values : frame.values = []
  counter : frame.get 51 = some (.i64 (UInt64.ofNat index))
  preserved : ∀ localIndex : Nat, (localIndex < 11 ∨ 33 < localIndex) →
    (localIndex < 54 ∨ 56 < localIndex) → localIndex ≠ 51 →
      frame.get localIndex = base.get localIndex

theorem InitialMapFrameAt.initial (base : Locals) (index : Nat)
    (hParams : base.params.length = 5) (hLocals : base.locals.length = 61)
    (hValues : base.values = []) (hIndex : base.get 51 = some (.i64 (UInt64.ofNat index))) :
    InitialMapFrameAt base index base :=
  ⟨hParams, hLocals, hValues, hIndex, fun _ _ _ _ => rfl⟩

theorem InitialMapFrameAt.get {base frame : Locals} {index : Nat}
    (h : InitialMapFrameAt base index frame) (localIndex : Nat)
    (hLow : localIndex < 11 ∨ 33 < localIndex)
    (hHigh : localIndex < 54 ∨ 56 < localIndex) (hNe : localIndex ≠ 51) :
    frame.get localIndex = base.get localIndex := h.preserved localIndex hLow hHigh hNe

theorem InitialMapFrameAt.mapped_valid {base frame : Locals} {index : Nat}
    (h : InitialMapFrameAt base index frame) (n offset : Nat) (cell : Traversal.Cell) :
    (initialMappedFrame frame n offset cell).validIndex 51 := by
  simp [Locals.validIndex, initialMappedFrame, h.paramsLength, h.localsLength]

theorem InitialMapFrameAt.next {base frame : Locals} {index : Nat}
    (h : InitialMapFrameAt base index frame) (n offset : Nat) (cell : Traversal.Cell) :
    InitialMapFrameAt base (index + 1)
      (FixedArrayCopy.counterFrame (initialMappedFrame frame n offset cell) 51 (index + 1)
        (h.mapped_valid n offset cell)) := by
  refine ⟨?_, ?_, rfl, FixedArrayCopy.counterFrame_get_counter .., ?_⟩
  · simpa only [FixedArrayCopy.counterFrame_params_length, initialMappedFrame,
      initialCalledFrame_params, initialLoadedFrame_params] using h.paramsLength
  · simpa only [FixedArrayCopy.counterFrame_locals_length, initialMappedFrame,
      initialCalledFrame_length, initialLoadedFrame_length] using h.localsLength
  · intro localIndex hLow hHigh hNe
    rw [FixedArrayCopy.counterFrame_get_ne _ _ _ _ _ hNe,
      initial_mapped_get_other _ _ _ _ _ h.paramsLength hLow hHigh]
    exact h.preserved localIndex hLow hHigh hNe

theorem initial_map_increment_shape : initialMapLoop.drop 210 =
    [.localGet 51, .constI64 1, .addI64, .localSet 51, .br 0] := by
  rfl

theorem initial_map_increment_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (index : Nat) (hValid : frame.validIndex 51) (hValues : frame.values = [])
    (hIndex : frame.get 51 = some (.i64 (UInt64.ofNat index))) (Q : Assertion Unit)
    (hNext : Q (.Break 0 store (FixedArrayCopy.counterFrame frame 51 (index + 1) hValid))) :
    wp module (initialMapLoop.drop 210) Q store frame env := by
  rw [initial_map_increment_shape]
  have hAdd : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) :=
    (UInt64.ofNat_add index 1).symm
  simp only [wp_localGet_cons, hIndex, wp_constI64_cons, wp_addI64_cons,
    wp_localSet_cons, hValues, hAdd]
  have hLocal : 51 < frame.params.length + frame.locals.length := hValid
  by_cases hParam : 51 < frame.params.length
  · simpa [wp_br_cons, FixedArrayCopy.counterFrame, Locals.set, Locals.set?, hParam] using hNext
  · simpa [wp_br_cons, FixedArrayCopy.counterFrame, Locals.set, Locals.set?, hParam, hLocal] using hNext

#print axioms InitialMapFrameAt.next
#print axioms initial_map_increment_shape
#print axioms initial_map_increment_spec

end Project.EulerRiemann.Execution
