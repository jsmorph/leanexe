import Project.TinyGpt2Infer.OutputCode
import Project.TinyGpt2Infer.OutputFrame
import Project.ProofKit.FixedArrayCapacityArithmetic
import Project.ProofKit.FixedFrame

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.TinyGpt2 Project.ProofKit FixedArrayFold ArrayPushLayout

def outputCapacityPrefix : Wasm.Program :=
  [.localGet 36,
   .localSet 51,
   .localGet 35,
   .localSet 57,
   .localGet 51,
   .wrapI64,
   .load64 0,
   .localSet 52,
   .localGet 52,
   .constI64 1,
   .mulI64,
   .localSet 53,
   .localGet 52,
   .constI64 1,
   .addI64,
   .localSet 54]

theorem output_capacity_shape : (outputBody.drop 33).take 34 =
    outputCapacityPrefix ++ FixedArrayCapacity.localProgram 54 1 60 := rfl

def outputCapacityFrame (frame : Locals) (output value : UInt64) (count : Nat) : Locals :=
  [(51, output), (57, value), (52, UInt64.ofNat count), (53, UInt64.ofNat count),
    (54, UInt64.ofNat (count + 1)), (60, UInt64.ofNat (capacity (count + 1)))].foldl
      (fun current assignment => resultFrame current assignment.1 assignment.2) frame

theorem output_capacity_word (count : Nat) (hCount : count < 256) :
    FixedArrayCapacity.normalizedCapacity (UInt64.ofNat (count + 1)) 1 =
      UInt64.ofNat (capacity (count + 1)) := by
  have hLength : (UInt64.ofNat (count + 1)).toNat = count + 1 := by
    apply UInt64.toNat_ofNat_of_lt'
    change count + 1 < 18446744073709551616
    omega
  have hCapacity : (UInt64.ofNat (capacity (count + 1))).toNat = capacity (count + 1) := by
    apply UInt64.toNat_ofNat_of_lt'
    change 8 * (count + 1 + 1) < 18446744073709551616
    omega
  apply UInt64.toNat.inj
  rw [FixedArrayCapacity.normalizedCapacity_toNat_of_fits _ _ (by
    rw [hLength]
    change 8 + (count + 1) * 1 * 8 + 7 < 18446744073709551616
    omega), hLength, hCapacity]
  change 8 + (count + 1) * 1 * 8 = 8 * (count + 1 + 1)
  omega

theorem outputCapacityFrame_saved {frame : Locals} {pointer empty : UInt64} {x : Row}
    (h : OutputSaved pointer empty x frame) (output value : UInt64) (count : Nat) :
    OutputSaved pointer empty x (outputCapacityFrame frame output value count) := by
  unfold outputCapacityFrame
  simp only [List.foldl]
  repeat first
    | exact h
    | refine OutputSaved.result ?_ _ _ (by decide) (by decide) (by decide)

theorem outputCapacityFrame_get (frame : Locals) (output value : UInt64) (count : Nat)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 65) :
    let next := outputCapacityFrame frame output value count
    next.get 51 = some (.i64 output) ∧ next.get 57 = some (.i64 value) ∧
    next.get 52 = some (.i64 (UInt64.ofNat count)) ∧
    next.get 53 = some (.i64 (UInt64.ofNat count)) ∧
    next.get 54 = some (.i64 (UInt64.ofNat (count + 1))) ∧
    next.get 60 = some (.i64 (UInt64.ofNat (capacity (count + 1)))) ∧
    next.get 23 = frame.get 23 ∧ next.get 24 = frame.get 24 ∧
    next.get 48 = frame.get 48 ∧ next.get 69 = frame.get 69 := by
  simp [outputCapacityFrame, List.foldl, resultFrame, Locals.get, hParams, hLocals,
    List.getElem?_set]

theorem output_capacity_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (pointer empty output value : UInt64) (input : Array UInt64) (x : Row) (count : Nat)
    (hSaved : OutputSaved pointer empty x frame)
    (hOutput : frame.get 36 = some (.i64 output))
    (hValue : frame.get 35 = some (.i64 value))
    (hInput : UInt64Array.At initial output input) (hSize : input.size = count)
    (hCount : count < 256)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q initial (outputCapacityFrame frame output value count) env) :
    wp module ((outputBody.drop 33).take 34 ++ rest) Q initial frame env := by
  have hOut := Frame.internal_getElem?_of_get frame 5 31 (.i64 output)
    hSaved.params (by rw [hSaved.locals]; decide) hOutput
  have hVal := Frame.internal_getElem?_of_get frame 5 30 (.i64 value)
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
  apply FixedArrayCapacity.localProgram_spec 54 (UInt64.ofNat (count + 1)) 1 60 module env initial
  · simp [Locals.get, hSaved.params, hSaved.locals, List.getElem?_set]
  · rfl
  · simpa only [hSaved.params] using (show 5 ≤ 60 by decide)
  · simp [Locals.validIndex, hSaved.params, hSaved.locals]
  · simpa only [outputCapacityFrame, List.foldl, resultFrame, FixedArrayCapacity.capacityFrame,
      hSaved.params, Nat.reduceSub, output_capacity_word count hCount] using hNext

#print axioms output_capacity_word
#print axioms output_capacity_spec
end Project.TinyGpt2Infer.Spec
