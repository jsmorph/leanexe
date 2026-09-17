import Project.TinyGpt2Checked.OutputCode
import Project.TinyGpt2Checked.OutputFrame
import Project.TinyGpt2Checked.Components

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.TinyGpt2 Project.ProofKit FixedArrayFold Project.TinyGpt2Hidden.Spec

def outputLogitProgram : Wasm.Program :=
  [.localGet 47,
   .localSet 26,
   .localGet 25,
   .localSet 28,
   .localGet 28,
   .localSet 37,
   .localGet 0,
   .localSet 29,
   .localGet 1,
   .localSet 30,
   .localGet 17,
   .localSet 31,
   .localGet 18,
   .localSet 32,
   .localGet 19,
   .localSet 33,
   .localGet 20,
   .localSet 34,
   .localGet 26,
   .localSet 35,
   .localGet 29,
   .localGet 30,
   .localGet 31,
   .localGet 32,
   .localGet 33,
   .localGet 34,
   .localGet 35,
   .call 83,
   .localSet 36]

theorem output_logit_shape : (outputBody.drop 4).take 29 = outputLogitProgram := rfl

def outputLogitFrame (frame : Locals) (owner pointer output token value : UInt64) (x : Row) : Locals :=
  [(26, token), (28, output), (37, output), (29, owner), (30, pointer),
    (31, x.x0), (32, x.x1), (33, x.x2), (34, x.x3), (35, token), (36, value)].foldl
      (fun current assignment => resultFrame current assignment.1 assignment.2) frame

theorem outputLogitFrame_saved {frame : Locals} {owner pointer empty : UInt64} {x : Row}
    (h : OutputSaved owner pointer empty x frame) (output token value : UInt64) :
    OutputSaved owner pointer empty x (outputLogitFrame frame owner pointer output token value x) := by
  unfold outputLogitFrame
  simp only [List.foldl]
  repeat first
    | exact h
    | refine OutputSaved.result ?_ _ _ (by decide) (by decide) (by decide)

theorem outputLogitFrame_get (frame : Locals) (owner pointer output token value : UInt64) (x : Row)
    (hParams : frame.params.length = 6) (hLocals : frame.locals.length = 63) :
    let next := outputLogitFrame frame owner pointer output token value x
    next.get 36 = some (.i64 value) ∧ next.get 37 = some (.i64 output) ∧
    next.get 24 = frame.get 24 ∧ next.get 25 = frame.get 25 ∧
    next.get 47 = frame.get 47 ∧ next.get 68 = frame.get 68 := by
  simp [outputLogitFrame, List.foldl, resultFrame, Locals.get, hParams, hLocals,
    List.getElem?_set]

theorem output_logit_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (owner pointer empty output token : UInt64) (weights : Array UInt64) (x : Row)
    (hSaved : OutputSaved owner pointer empty x frame)
    (hOutput : frame.get 25 = some (.i64 output))
    (hToken : frame.get 47 = some (.i64 token))
    (hInput : UInt64Array.At initial pointer weights) (hSize : 2488 ≤ weights.size)
    (hBound : token.toNat < 256)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q initial
      (outputLogitFrame frame owner pointer output token (logit weights x token) x) env) :
    wp module ((outputBody.drop 4).take 29 ++ rest) Q initial frame env := by
  have hPointer : frame.params[1]? = some (.i64 pointer) := by
    simpa only [Locals.get, hSaved.params, Nat.reduceLT, ↓reduceIte] using hSaved.pointer
  have hOwner : frame.params[0]? = some (.i64 owner) := by
    simpa only [Locals.get, hSaved.params, Nat.reduceLT, ↓reduceIte] using hSaved.owner
  have hX0 := Frame.internal_getElem?_of_get frame 6 11 (.i64 x.x0)
    hSaved.params (by rw [hSaved.locals]; decide) hSaved.x0
  have hX1 := Frame.internal_getElem?_of_get frame 6 12 (.i64 x.x1)
    hSaved.params (by rw [hSaved.locals]; decide) hSaved.x1
  have hX2 := Frame.internal_getElem?_of_get frame 6 13 (.i64 x.x2)
    hSaved.params (by rw [hSaved.locals]; decide) hSaved.x2
  have hX3 := Frame.internal_getElem?_of_get frame 6 14 (.i64 x.x3)
    hSaved.params (by rw [hSaved.locals]; decide) hSaved.x3
  have hOut := Frame.internal_getElem?_of_get frame 6 19 (.i64 output)
    hSaved.params (by rw [hSaved.locals]; decide) hOutput
  have hTok := Frame.internal_getElem?_of_get frame 6 41 (.i64 token)
    hSaved.params (by rw [hSaved.locals]; decide) hToken
  rw [output_logit_shape]
  unfold outputLogitProgram
  simp only [List.cons_append, List.nil_append]
  wp_fixed_frame [List.length_set, List.getElem?_set, hSaved.params, hSaved.locals, hSaved.values, hPointer, hOwner,
    hX0, hX1, hX2, hX3, hOut, hTok]
  refine wp_call_exact_append (logit_exact env initial owner pointer weights x token hInput hSize hBound)
    rfl rfl rfl [] ?_ ?_
  · rfl
  wp_fixed_frame [List.length_set, List.getElem?_set, hSaved.params, hSaved.locals]
  simpa only [outputLogitFrame, List.foldl, resultFrame, hSaved.params,
    Nat.reduceSub, List.append_nil] using hNext

#print axioms output_logit_spec
end Project.TinyGpt2Checked.Spec
