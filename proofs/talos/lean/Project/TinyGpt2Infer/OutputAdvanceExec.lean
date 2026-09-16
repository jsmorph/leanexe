import Project.TinyGpt2Infer.OutputFrame
import Project.TinyGpt2Infer.OutputCode
import Project.ProofKit.FixedFrame

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.TinyGpt2 Project.ProofKit FixedArrayFold

def outputAdvanceProgram : Wasm.Program :=
  [.localGet 45, .localSet 48, .localGet 47, .localSet 49,
   .localGet 48, .localGet 49, .addI64, .localTee 50, .localGet 48, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 50] [] [.i64], .localSet 45, .br 0]

theorem output_advance_shape : outputBody.drop 131 = outputAdvanceProgram := rfl

def outputAdvanceFrame (frame : Locals) (count : Nat) : Locals :=
  [(48, UInt64.ofNat count), (49, 1), (50, UInt64.ofNat (count + 1)),
    (45, UInt64.ofNat (count + 1))].foldl
      (fun current assignment => resultFrame current assignment.1 assignment.2) frame

theorem outputAdvanceFrame_saved {frame : Locals} {pointer empty : UInt64} {x : Row}
    (h : OutputSaved pointer empty x frame) (count : Nat) :
    OutputSaved pointer empty x (outputAdvanceFrame frame count) := by
  unfold outputAdvanceFrame
  simp only [List.foldl]
  repeat first
    | exact h
    | refine OutputSaved.result ?_ _ _ (by decide) (by decide) (by decide)

theorem outputAdvanceFrame_get (frame : Locals) (count : Nat)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 62) :
    let next := outputAdvanceFrame frame count
    next.get 23 = frame.get 23 ∧ next.get 24 = frame.get 24 ∧
    next.get 45 = some (.i64 (UInt64.ofNat (count + 1))) ∧ next.get 66 = frame.get 66 := by
  simp [outputAdvanceFrame, List.foldl, resultFrame, Locals.get, hParams, hLocals,
    List.getElem?_set]

theorem output_advance_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (count : Nat) (hCount : count < 256)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 62)
    (hValues : frame.values = [])
    (hCounter : frame.get 45 = some (.i64 (UInt64.ofNat count)))
    (hStep : frame.get 47 = some (.i64 1))
    (Q : Assertion Unit) (hNext : Q (.Break 0 initial (outputAdvanceFrame frame count))) :
    wp module (outputBody.drop 131) Q initial frame env := by
  have hCounter' := Frame.internal_getElem?_of_get frame 5 40 (.i64 (UInt64.ofNat count))
    hParams (by rw [hLocals]; decide) hCounter
  have hStep' := Frame.internal_getElem?_of_get frame 5 42 (.i64 1)
    hParams (by rw [hLocals]; decide) hStep
  have hAdd : UInt64.ofNat count + 1 = UInt64.ofNat (count + 1) := by
    change UInt64.ofNat count + UInt64.ofNat 1 = _
    rw [UInt64.ofNat_add]
  have hNoWrap : ¬UInt64.ofNat (count + 1) < UInt64.ofNat count := by
    change ¬(UInt64.ofNat (count + 1)).toNat < (UInt64.ofNat count).toNat
    rw [UInt64.toNat_ofNat_of_lt' (by change count + 1 < 18446744073709551616; omega),
      UInt64.toNat_ofNat_of_lt' (by change count < 18446744073709551616; omega)]
    omega
  rw [output_advance_shape]
  unfold outputAdvanceProgram
  wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff,
    hParams, hLocals, hValues, hCounter', hStep', hAdd, hNoWrap]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simp [hNoWrap])]
  wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff, hParams, hLocals]
  simpa only [outputAdvanceFrame, List.foldl, resultFrame, hParams, Nat.reduceSub,
    List.take, List.drop, List.nil_append, List.cons_append] using hNext

#print axioms output_advance_spec
end Project.TinyGpt2Infer.Spec
