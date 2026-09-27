import Project.TinyGpt2Checked.OutputLoop
import Project.TinyGpt2Infer.OutputExit

namespace Project.TinyGpt2Checked.Spec
open Project.TinyGpt2Infer
open Wasm Project.TinyGpt2 Project.Clob Project.Runtime Project.ProofKit ArrayPushLayout FixedArrayFold

def outputExitProgram : Wasm.Program :=
  [.localGet 24, .localSet 43, .localGet 25, .localSet 44,
   .localGet 43, .localSet 45, .localGet 44, .localSet 46,
   .localGet 45, .localSet 47, .localGet 46, .localSet 48,
   .localGet 22, .constI64 0, .eqI64, .eqz,
   .iff 0 1 [.localGet 22, .localGet 47, .eqI64, .eqz] [.const 0] [] [.i32],
   .iff 0 0 [.localGet 22, .call 89] [], .localGet 47, .localGet 48]

theorem output_exit_shape : func84.drop 90 = outputExitProgram := rfl

def outputExitFrame (frame : Locals) (output : UInt64) : Locals :=
  { params := frame.params,
    locals := (((((frame.locals.set 37 (.i64 output)).set 38 (.i64 output)).set 39 (.i64 output)).set 40 (.i64 output)).set 41 (.i64 output)).set 42 (.i64 output),
    values := [.i64 output, .i64 output] }

theorem output_exit_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (empty capacity head releases frees output : UInt64)
    (hParams : frame.params.length = 6) (hLocals : frame.locals.length = 66)
    (hValues : frame.values = [])
    (hCurrent : frame.get 24 = some (.i64 output)) (hOutput : frame.get 25 = some (.i64 output))
    (hEmpty : frame.get 22 = some (.i64 empty)) (hSeparate : empty ≠ output)
    (hRoot : 48 ≤ empty.toNat) (hHeader : FreshFixedArrayAt initial empty capacity 1)
    (hArray : UInt64Array.At initial empty #[])
    (hHead : initial.globals.globals[1]? = some (.i64 head))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees))
    (Q : Assertion Unit)
    (hNext : Q (.Fallthrough (FixedArrayRelease.store initial empty head releases frees)
      (outputExitFrame frame output))) :
    wp module (func84.drop 90) Q initial frame env := by
  have hCur := Frame.internal_getElem?_of_get frame 6 18 (.i64 output)
    hParams (by rw [hLocals]; decide) hCurrent
  have hOut := Frame.internal_getElem?_of_get frame 6 19 (.i64 output)
    hParams (by rw [hLocals]; decide) hOutput
  have hEmp := Frame.internal_getElem?_of_get frame 6 16 (.i64 empty)
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
  wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff,
    hParams, hLocals, hEmp, hSeparate]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simp [hSeparate])]
  wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff, hParams, hLocals, hEmp]
  refine wp_call_tw (output_release_exact env initial empty capacity head releases frees #[]
    hRoot hHeader hArray hHead hReleases hFrees) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff, hParams, hLocals]
  simpa only [outputExitFrame, List.nil_append, List.append] using hNext

#print axioms output_exit_spec
end Project.TinyGpt2Checked.Spec
