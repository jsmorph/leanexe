import Project.EulerGridStep.CopyModel
import Project.ProofKit.FixedArrayCopy

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayCopy

theorem copyFrame_get_withValues (frame : Locals) (values : List Value) (index : Nat) :
    ({ frame with values := values } : Locals).get index = frame.get index := rfl

theorem copyFrame_ofParts (frame : Locals) (hValues : frame.values = []) :
    ({ params := frame.params, locals := frame.locals } : Locals) = frame := by
  cases frame
  simp_all

theorem copyFrame_set_counter (frame : Locals)
    (counterLocal current next : Nat) (values : List Value)
    (hCounter : frame.validIndex counterLocal) :
    ({ counterFrame frame counterLocal current hCounter with values := values } : Locals).set?
        counterLocal (.i64 (UInt64.ofNat next)) =
      some ({ counterFrame frame counterLocal next hCounter with values := values } : Locals) := by
  unfold counterFrame Wasm.Locals.set Wasm.Locals.set?
  by_cases hParam : counterLocal < frame.params.length
  · simp [hParam, List.set_set]
  · have hLocal : counterLocal < frame.params.length + frame.locals.length := hCounter
    simp [hParam, hLocal, List.set_set]

theorem copy_initialize_counter {m : Wasm.Module} {env : HostEnv Unit} {initial : Store Unit}
    {frame : Locals} {counterLocal : Nat} (hCounter : frame.validIndex counterLocal)
    (hValues : frame.values = []) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial (counterFrame frame counterLocal 0 hCounter) env) :
    wp m (.constI64 0 :: .localSet counterLocal :: rest) Q initial frame env := by
  simp only [wp_constI64_cons, wp_localSet_cons, hValues]
  by_cases hParam : counterLocal < frame.params.length
  · simpa [counterFrame, Wasm.Locals.set, Wasm.Locals.set?, hParam] using hNext
  · have hLocal : counterLocal < frame.params.length + frame.locals.length := hCounter
    simpa [counterFrame, Wasm.Locals.set, Wasm.Locals.set?, hParam, hLocal] using hNext

theorem copyRuntimeAddress (pointer : UInt64) (index : Nat) :
    UInt32.ofNat ((pointer + (UInt64.ofNat index + 1) * 8).toNat % (2 ^ 32)) =
      UInt64Array.wordAddress pointer (index + 1) := by
  have hOffset : (UInt64.ofNat index + 1) * 8 = UInt64.ofNat (8 * (index + 1)) := by
    calc
      _ = UInt64.ofNat (index + 1) * 8 :=
        congrArg (fun x : UInt64 => x * 8) (UInt64.ofNat_add index 1).symm
      _ = UInt64.ofNat ((index + 1) * 8) := (UInt64.ofNat_mul (index + 1) 8).symm
      _ = _ := by rw [Nat.mul_comm]
  rw [hOffset]
  exact (Memory.toUInt32_eq_ofNat _).symm

def copyMeasure (counterLocal count : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get counterLocal with
  | some (.i64 index) => count - index.toNat
  | _ => 0

theorem copyMeasure_frame (frame : Locals) (counterLocal count index : Nat) (initial : Store Unit)
    (hCounter : frame.validIndex counterLocal) :
    copyMeasure counterLocal count initial (counterFrame frame counterLocal index hCounter) =
      count - (UInt64.ofNat index).toNat := by
  unfold copyMeasure
  rw [counterFrame_get_counter]

#print axioms copy_initialize_counter
#print axioms copyRuntimeAddress
end Project.EulerGridStep.Execution
