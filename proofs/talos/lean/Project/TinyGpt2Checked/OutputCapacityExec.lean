import Project.TinyGpt2Infer.OutputCapacityExec
import Project.TinyGpt2Checked.OutputCode
import Project.TinyGpt2Checked.OutputFrame
import Project.ProofKit.FixedArrayCapacityArithmetic
import Project.ProofKit.FixedFrame

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.TinyGpt2 Project.ProofKit FixedArrayFold ArrayPushLayout

def outputCapacityPrefix : Wasm.Program :=
  [.localGet 37,
   .localSet 54,
   .localGet 36,
   .localSet 60,
   .localGet 54,
   .wrapI64,
   .load64 0,
   .localSet 55,
   .localGet 55,
   .constI64 1,
   .mulI64,
   .localSet 56,
   .localGet 55,
   .constI64 1,
   .addI64,
   .localSet 57]

theorem output_capacity_shape : (outputBody.drop 35).take 34 =
    outputCapacityPrefix ++ FixedArrayCapacity.localProgram 57 1 63 := rfl

def outputCapacityFrame (frame : Locals) (output value : UInt64) (count : Nat) : Locals :=
  [(54, output), (60, value), (55, UInt64.ofNat count), (56, UInt64.ofNat count),
    (57, UInt64.ofNat (count + 1)), (63, UInt64.ofNat (capacity (count + 1)))].foldl
      (fun current assignment => resultFrame current assignment.1 assignment.2) frame

theorem outputCapacityFrame_saved {frame : Locals} {owner pointer empty : UInt64} {x : Row}
    (h : OutputSaved owner pointer empty x frame) (output value : UInt64) (count : Nat) :
    OutputSaved owner pointer empty x (outputCapacityFrame frame output value count) := by
  unfold outputCapacityFrame
  simp only [List.foldl]
  repeat first
    | exact h
    | refine OutputSaved.result ?_ _ _ (by decide) (by decide) (by decide)

theorem outputCapacityFrame_get (frame : Locals) (output value : UInt64) (count : Nat)
    (hParams : frame.params.length = 6) (hLocals : frame.locals.length = 68) :
    let next := outputCapacityFrame frame output value count
    next.get 54 = some (.i64 output) ∧ next.get 60 = some (.i64 value) ∧
    next.get 55 = some (.i64 (UInt64.ofNat count)) ∧
    next.get 56 = some (.i64 (UInt64.ofNat count)) ∧
    next.get 57 = some (.i64 (UInt64.ofNat (count + 1))) ∧
    next.get 63 = some (.i64 (UInt64.ofNat (capacity (count + 1)))) ∧
    next.get 24 = frame.get 24 ∧ next.get 25 = frame.get 25 ∧
    next.get 51 = frame.get 51 ∧ next.get 72 = frame.get 72 := by
  simp [outputCapacityFrame, List.foldl, resultFrame, Locals.get, hParams, hLocals,
    List.getElem?_set]

theorem output_capacity_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (owner pointer empty output value : UInt64) (input : Array UInt64) (x : Row) (count : Nat)
    (hSaved : OutputSaved owner pointer empty x frame)
    (hOutput : frame.get 37 = some (.i64 output))
    (hValue : frame.get 36 = some (.i64 value))
    (hInput : UInt64Array.At initial output input) (hSize : input.size = count)
    (hCount : count < 256)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q initial (outputCapacityFrame frame output value count) env) :
    wp module ((outputBody.drop 35).take 34 ++ rest) Q initial frame env := by
  have hOut := Frame.internal_getElem?_of_get frame 6 31 (.i64 output)
    hSaved.params (by rw [hSaved.locals]; decide) hOutput
  have hVal := Frame.internal_getElem?_of_get frame 6 30 (.i64 value)
    hSaved.params (by rw [hSaved.locals]; decide) hValue
  have hRead : initial.mem.read64 output.toUInt32 = UInt64.ofNat count := by
    simpa only [hSize] using hInput.lengthRead
  have hBound : ¬initial.mem.pages * 65536 < output.toUInt32.toNat + 8 :=
    Nat.not_lt.mpr hInput.lengthBound
  have hAdd : UInt64.ofNat count + 1 = UInt64.ofNat (count + 1) := by
    change UInt64.ofNat count + UInt64.ofNat 1 = _
    rw [UInt64.ofNat_add]
  rw [output_capacity_shape]
  simp only [outputCapacityPrefix, List.cons_append, List.nil_append]
  wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reducePow,
    UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero, hSaved.params, hSaved.locals,
    hSaved.values, hOut, hVal, ← Memory.toUInt32_eq_ofNat, hBound, hRead, UInt64.mul_one, hAdd]
  apply FixedArrayCapacity.localProgram_spec 57 (UInt64.ofNat (count + 1)) 1 63 module env initial
  · simp [Locals.get, hSaved.params, hSaved.locals, List.getElem?_set]
  · rfl
  · simpa only [hSaved.params] using (show 6 ≤ 63 by decide)
  · simp [Locals.validIndex, hSaved.params, hSaved.locals]
  · simpa only [outputCapacityFrame, List.foldl, resultFrame, FixedArrayCapacity.capacityFrame,
      hSaved.params, Nat.reduceSub, TinyGpt2Infer.Spec.output_capacity_word count hCount] using hNext

#print axioms output_capacity_spec
end Project.TinyGpt2Checked.Spec
