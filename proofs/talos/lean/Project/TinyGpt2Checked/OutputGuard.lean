import Project.TinyGpt2Checked.OutputIteration

namespace Project.TinyGpt2Checked.Spec
open Project.TinyGpt2Infer
open Wasm Project.TinyGpt2 Project.ProofKit

theorem output_guard_shape : outputBody =
    [.localGet 51, .localGet 52, .geUI64, .br_if 1] ++ outputBody.drop 4 := by
  exact (List.take_append_drop 4 outputBody).symm

theorem output_guard_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (owner pointer empty root : UInt64) (x : Row) (count : Nat)
    (hLocals : OutputLoopLocals owner pointer empty x root count frame) (hCount : count ≤ 256)
    (Q : Assertion Unit)
    (hDone : count = 256 → Q (.Break 1 initial frame))
    (hNext : count < 256 → wp module (outputBody.drop 4) Q initial frame env) :
    wp module outputBody Q initial frame env := by
  have hCounter := Frame.internal_getElem?_of_get frame 6 45 (.i64 (UInt64.ofNat count))
    hLocals.params (by rw [hLocals.locals]; decide) hLocals.counter
  have hLimit := Frame.internal_getElem?_of_get frame 6 46 (.i64 256)
    hLocals.params (by rw [hLocals.locals]; decide) hLocals.limit
  have hToken : (UInt64.ofNat count).toNat = count := by
    apply UInt64.toNat_ofNat_of_lt'
    change count < 18446744073709551616
    omega
  have hFrame : ({ params := frame.params, locals := frame.locals, values := [] } : Locals) = frame :=
    Frame.ext _ _ rfl rfl hLocals.values.symm
  rw [output_guard_shape]
  simp only [List.cons_append, List.nil_append]
  by_cases hStop : count = 256
  · have hGe : (256 : UInt64) ≤ UInt64.ofNat count := by
      change 256 ≤ (UInt64.ofNat count).toNat
      omega
    wp_fixed_frame [hLocals.params, hLocals.locals, hLocals.values, hCounter, hLimit, hGe]
    simpa [hFrame] using hDone hStop
  · have hGe : ¬(256 : UInt64) ≤ UInt64.ofNat count := by
      change ¬256 ≤ (UInt64.ofNat count).toNat
      omega
    wp_fixed_frame [hLocals.params, hLocals.locals, hLocals.values, hCounter, hLimit, hGe]
    simpa only [hFrame] using hNext (by omega)

#print axioms output_guard_spec
end Project.TinyGpt2Checked.Spec
