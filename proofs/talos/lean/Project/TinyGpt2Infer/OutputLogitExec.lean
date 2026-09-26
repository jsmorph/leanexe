import Project.TinyGpt2Infer.OutputCode
import Project.TinyGpt2Infer.OutputFrame
import Project.TinyGpt2Infer.Logit

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.TinyGpt2 Project.ProofKit FixedArrayFold Project.TinyGpt2Hidden.Spec

def outputLogitProgram : Wasm.Program :=
  [.localGet 48,
   .localSet 25,
   .localGet 24,
   .localSet 27,
   .localGet 27,
   .localSet 36,
   .constI64 0,
   .localSet 28,
   .localGet 0,
   .localSet 29,
   .localGet 16,
   .localSet 30,
   .localGet 17,
   .localSet 31,
   .localGet 18,
   .localSet 32,
   .localGet 19,
   .localSet 33,
   .localGet 25,
   .localSet 34,
   .localGet 28,
   .localGet 29,
   .localGet 30,
   .localGet 31,
   .localGet 32,
   .localGet 33,
   .localGet 34,
   .call 77,
   .localSet 35]

theorem output_logit_shape : (outputBody.drop 4).take 29 = outputLogitProgram := rfl

def outputLogitFrame (frame : Locals) (pointer output token value : UInt64) (x : Row) : Locals :=
  [(25, token), (27, output), (36, output), (28, 0), (29, pointer),
    (30, x.x0), (31, x.x1), (32, x.x2), (33, x.x3), (34, token), (35, value)].foldl
      (fun current assignment => resultFrame current assignment.1 assignment.2) frame

theorem outputLogitFrame_saved {frame : Locals} {pointer empty : UInt64} {x : Row}
    (h : OutputSaved pointer empty x frame) (output token value : UInt64) :
    OutputSaved pointer empty x (outputLogitFrame frame pointer output token value x) := by
  unfold outputLogitFrame
  simp only [List.foldl]
  repeat first
    | exact h
    | refine OutputSaved.result ?_ _ _ (by decide) (by decide) (by decide)

theorem outputLogitFrame_get (frame : Locals) (pointer output token value : UInt64) (x : Row)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 66) :
    let next := outputLogitFrame frame pointer output token value x
    next.get 35 = some (.i64 value) ∧ next.get 36 = some (.i64 output) ∧
    next.get 23 = frame.get 23 ∧ next.get 24 = frame.get 24 ∧
    next.get 48 = frame.get 48 ∧ next.get 69 = frame.get 69 := by
  simp [outputLogitFrame, List.foldl, resultFrame, Locals.get, hParams, hLocals,
    List.getElem?_set]

theorem output_logit_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (pointer empty output token : UInt64) (weights : Array UInt64) (x : Row)
    (hSaved : OutputSaved pointer empty x frame)
    (hOutput : frame.get 24 = some (.i64 output))
    (hToken : frame.get 48 = some (.i64 token))
    (hInput : UInt64Array.At initial pointer weights) (hSize : 2488 ≤ weights.size)
    (hBound : token.toNat < 256)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q initial
      (outputLogitFrame frame pointer output token (logit weights x token) x) env) :
    wp module ((outputBody.drop 4).take 29 ++ rest) Q initial frame env := by
  have hPointer : frame.params[0]? = some (.i64 pointer) := by
    simpa only [Locals.get, hSaved.params, Nat.reduceLT, ↓reduceIte] using hSaved.pointer
  have hX0 := Frame.internal_getElem?_of_get frame 5 11 (.i64 x.x0)
    hSaved.params (by rw [hSaved.locals]; decide) hSaved.x0
  have hX1 := Frame.internal_getElem?_of_get frame 5 12 (.i64 x.x1)
    hSaved.params (by rw [hSaved.locals]; decide) hSaved.x1
  have hX2 := Frame.internal_getElem?_of_get frame 5 13 (.i64 x.x2)
    hSaved.params (by rw [hSaved.locals]; decide) hSaved.x2
  have hX3 := Frame.internal_getElem?_of_get frame 5 14 (.i64 x.x3)
    hSaved.params (by rw [hSaved.locals]; decide) hSaved.x3
  have hOut := Frame.internal_getElem?_of_get frame 5 19 (.i64 output)
    hSaved.params (by rw [hSaved.locals]; decide) hOutput
  have hTok := Frame.internal_getElem?_of_get frame 5 43 (.i64 token)
    hSaved.params (by rw [hSaved.locals]; decide) hToken
  rw [output_logit_shape]
  unfold outputLogitProgram
  simp only [List.cons_append, List.nil_append]
  wp_fixed_frame [List.length_set, List.getElem?_set, hSaved.params, hSaved.locals, hSaved.values, hPointer,
    hX0, hX1, hX2, hX3, hOut, hTok]
  refine wp_call_exact_append (logit_exact env initial 0 pointer weights x token hInput hSize hBound)
    rfl rfl rfl [] ?_ ?_
  · rfl
  wp_fixed_frame [List.length_set, List.getElem?_set, hSaved.params, hSaved.locals]
  simpa only [outputLogitFrame, List.foldl, resultFrame, hSaved.params,
    Nat.reduceSub, List.append_nil] using hNext

#print axioms output_logit_spec
end Project.TinyGpt2Infer.Spec
