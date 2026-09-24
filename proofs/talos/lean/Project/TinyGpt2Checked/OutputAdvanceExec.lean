import Project.TinyGpt2Checked.OutputFrame
import Project.TinyGpt2Checked.OutputCode
import Project.ProofKit.FixedFrame

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.TinyGpt2 Project.ProofKit FixedArrayFold

def outputAdvanceProgram : Wasm.Program :=
  [.localGet 51, .localSet 54, .localGet 53, .localSet 55,
   .localGet 54, .localGet 55, .addI64, .localTee 56, .localGet 54, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 56] [] [.i64], .localSet 51, .br 0]

theorem output_advance_shape : outputBody.drop 147 = outputAdvanceProgram := rfl

def outputAdvanceFrame (frame : Locals) (count : Nat) : Locals :=
  [(54, UInt64.ofNat count), (55, 1), (56, UInt64.ofNat (count + 1)),
    (51, UInt64.ofNat (count + 1))].foldl
      (fun current assignment => resultFrame current assignment.1 assignment.2) frame

theorem outputAdvanceFrame_saved {frame : Locals} {owner pointer empty : UInt64} {x : Row}
    (h : OutputSaved owner pointer empty x frame) (count : Nat) :
    OutputSaved owner pointer empty x (outputAdvanceFrame frame count) := by
  unfold outputAdvanceFrame
  simp only [List.foldl]
  repeat first
    | exact h
    | refine OutputSaved.result ?_ _ _ (by decide) (by decide) (by decide)

theorem outputAdvanceFrame_get (frame : Locals) (count : Nat)
    (hParams : frame.params.length = 6) (hLocals : frame.locals.length = 68) :
    let next := outputAdvanceFrame frame count
    next.get 24 = frame.get 24 ∧ next.get 25 = frame.get 25 ∧
    next.get 51 = some (.i64 (UInt64.ofNat (count + 1))) ∧ next.get 72 = frame.get 72 := by
  simp [outputAdvanceFrame, List.foldl, resultFrame, Locals.get, hParams, hLocals,
    List.getElem?_set]

theorem output_advance_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (count : Nat) (hCount : count < 256)
    (hParams : frame.params.length = 6) (hLocals : frame.locals.length = 68)
    (hValues : frame.values = [])
    (hCounter : frame.get 51 = some (.i64 (UInt64.ofNat count)))
    (hStep : frame.get 53 = some (.i64 1))
    (Q : Assertion Unit) (hNext : Q (.Break 0 initial (outputAdvanceFrame frame count))) :
    wp module (outputBody.drop 147) Q initial frame env := by
  have hCounter' := Frame.internal_getElem?_of_get frame 6 45 (.i64 (UInt64.ofNat count))
    hParams (by rw [hLocals]; decide) hCounter
  have hStep' := Frame.internal_getElem?_of_get frame 6 47 (.i64 1)
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
end Project.TinyGpt2Checked.Spec
