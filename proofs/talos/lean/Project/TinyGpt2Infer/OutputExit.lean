import Project.TinyGpt2Infer.OutputLoop

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.TinyGpt2 Project.Clob Project.Runtime Project.ProofKit ArrayPushLayout FixedArrayFold

def outputExitProgram : Wasm.Program :=
  [.localGet 23, .localSet 42, .localGet 24, .localSet 43, .localGet 43, .localSet 44,
   .localGet 21, .constI64 0, .eqI64, .eqz,
   .iff 0 0 [.localGet 21, .call 79] [], .localGet 44]

theorem output_exit_shape : func75.drop 90 = outputExitProgram := rfl

def outputExitFrame (frame : Locals) (output : UInt64) : Locals :=
  { params := frame.params,
    locals := ((frame.locals.set 37 (.i64 output)).set 38 (.i64 output)).set 39 (.i64 output),
    values := [.i64 output] }

theorem output_exit_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (empty capacity head releases frees output : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 62)
    (hValues : frame.values = [])
    (hCurrent : frame.get 23 = some (.i64 output)) (hOutput : frame.get 24 = some (.i64 output))
    (hEmpty : frame.get 21 = some (.i64 empty))
    (hRoot : 48 ≤ empty.toNat) (hHeader : FreshFixedArrayAt initial empty capacity 1)
    (hArray : UInt64Array.At initial empty #[])
    (hHead : initial.globals.globals[1]? = some (.i64 head))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees))
    (Q : Assertion Unit)
    (hNext : Q (.Fallthrough (FixedArrayRelease.store initial empty head releases frees)
      (outputExitFrame frame output))) :
    wp module (func75.drop 90) Q initial frame env := by
  have hCur := Frame.internal_getElem?_of_get frame 5 18 (.i64 output)
    hParams (by rw [hLocals]; decide) hCurrent
  have hOut := Frame.internal_getElem?_of_get frame 5 19 (.i64 output)
    hParams (by rw [hLocals]; decide) hOutput
  have hEmp := Frame.internal_getElem?_of_get frame 5 16 (.i64 empty)
    hParams (by rw [hLocals]; decide) hEmpty
  have hNonzero : empty ≠ 0 := by
    intro hZero
    rw [hZero] at hRoot
    contradiction
  rw [output_exit_shape]
  unfold outputExitProgram
  wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff,
    hParams, hLocals, hValues, hCur, hOut, hEmp, hNonzero]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simp [hNonzero])]
  wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff, hParams, hLocals, hEmp]
  refine wp_call_tw (output_release_exact env initial empty capacity head releases frees #[]
    hRoot hHeader hArray hHead hReleases hFrees) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff, hParams, hLocals]
  simpa only [outputExitFrame, List.nil_append] using hNext

theorem output_exit_memory (store : Store Unit) (start : Nat) (releases frees : UInt64)
    (output : Array UInt64) (hFit : top start 256 < 4294967296)
    (hOutput : UInt64Array.At store (node start 256).root output) :
    let final := FixedArrayRelease.store store (node start 0).root
      (freeHead (freed start 256)) releases frees
    UInt64Array.At final (node start 256).root output ∧
    final.mem.pages = store.mem.pages ∧
    (∀ address : Nat, address < start → final.mem.bytes address = store.mem.bytes address) ∧
    final = { store with mem := final.mem, globals := final.globals } := by
  have hEmptyFit := (top_mono start (show 0 ≤ 256 by decide)).trans_lt hFit
  have hEmpty := node_toNat start 0 hEmptyFit
  have hResult := node_toNat start 256 hFit
  have hRoot := root_ge start 0
  have hBytes := FixedArrayRelease.bytes_outside store (node start 0).root
    (freeHead (freed start 256)) releases frees
    (by rw [hEmpty.1]; omega)
    (by rw [hEmpty.1]; exact ((Nat.le_add_right _ _).trans_lt hEmptyFit).le)
  refine ⟨hOutput.frame (by rfl) ?_, rfl, ?_, rfl⟩
  · intro address hLow _
    apply hBytes address (Or.inr ?_)
    rw [hEmpty.1]
    rw [hResult.1] at hLow
    have hSep := separated start (show 0 < 256 by decide)
    simp only [top, root] at hSep hLow ⊢
    omega
  · intro address hAddress
    apply hBytes address (Or.inl ?_)
    rw [hEmpty.1]
    omega

#print axioms output_exit_spec
#print axioms output_exit_memory
end Project.TinyGpt2Infer.Spec
