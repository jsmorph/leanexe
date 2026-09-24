import Project.TinyGpt2Infer.OutputCode
import Project.TinyGpt2Infer.OutputRelease
import Project.TinyGpt2Infer.OutputFrame
import Project.ProofKit.FixedFrame
import Project.ProofKit.FixedArrayFrame

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.ProofKit Project.Clob FixedArrayFold

def outputReleaseProgram : Wasm.Program :=
  [.localGet 57, .localSet 38, .localGet 38, .localSet 39,
   .localGet 38, .localSet 40, .localGet 39, .localSet 41,
   .constI64 0, .localSet 42,
   .localGet 38, .constI64 0, .eqI64, .eqz,
   .iff 0 1 [.localGet 38, .localGet 40, .eqI64, .eqz] [.const 0] [] [.i32],
   .iff 0 0 [.localGet 38, .call 82, .globalGet 5, .localSet 43] [],
   .localGet 40, .localSet 69, .localGet 41, .localSet 70, .localGet 42, .localSet 68,
   .localGet 23, .constI64 0, .neI64,
   .localGet 23, .localGet 71, .neI64, .and,
   .localGet 23, .localGet 69, .neI64, .and,
   .iff 0 0 [.localGet 23, .call 82] [],
   .localGet 69, .localSet 23, .localGet 70, .localSet 24,
   .localGet 68, .constI64 0, .neI64, .br_if 1]

theorem output_release_shape : (outputBody.drop 105).take 42 = outputReleaseProgram := rfl

def outputReleaseFrame (frame : Locals) (output : UInt64) : Locals :=
  [(38, output), (39, output), (40, output), (41, output), (42, 0),
    (69, output), (70, output), (68, 0), (23, output), (24, output)].foldl
      (fun current assignment => resultFrame current assignment.1 assignment.2) frame

theorem outputReleaseFrame_saved {frame : Locals} {pointer empty : UInt64}
    {x : Project.TinyGpt2.Row} (h : OutputSaved pointer empty x frame) (output : UInt64) :
    OutputSaved pointer empty x (outputReleaseFrame frame output) := by
  unfold outputReleaseFrame
  simp only [List.foldl]
  repeat first
    | exact h
    | refine OutputSaved.result ?_ _ _ (by decide) (by decide) (by decide)

theorem outputReleaseFrame_get (frame : Locals) (output : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 68) :
    let next := outputReleaseFrame frame output
    next.get 23 = some (.i64 output) ∧ next.get 24 = some (.i64 output) ∧
    next.get 50 = frame.get 50 ∧ next.get 71 = frame.get 71 := by
  simp [outputReleaseFrame, List.foldl, resultFrame, Locals.get, hParams, hLocals,
    List.getElem?_set]

theorem output_release_region_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (root empty capacity head releases frees output : UInt64) (input : Array UInt64) (count : Nat)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 68)
    (hValues : frame.values = [])
    (hCurrent : frame.get 23 = some (.i64 root)) (hOutput : frame.get 57 = some (.i64 output))
    (hOwned : frame.get 71 = some (.i64 empty))
    (hEmpty : root = empty ↔ count = 0) (hSeparate : root ≠ output)
    (hOutputNonzero : output ≠ 0)
    (hRoot : 48 ≤ root.toNat) (hHeader : FreshFixedArrayAt initial root capacity 1)
    (hInput : UInt64Array.At initial root input)
    (hHead : initial.globals.globals[1]? = some (.i64 head))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q
      (if count = 0 then initial else FixedArrayRelease.store initial root head releases frees)
      (outputReleaseFrame frame output) env) :
    wp module ((outputBody.drop 105).take 42 ++ rest) Q initial frame env := by
  have hCurrent' := Frame.internal_getElem?_of_get frame 5 18 (.i64 root)
    hParams (by rw [hLocals]; decide) hCurrent
  have hOutput' := Frame.internal_getElem?_of_get frame 5 52 (.i64 output)
    hParams (by rw [hLocals]; decide) hOutput
  have hOwned' := Frame.internal_getElem?_of_get frame 5 66
    (.i64 empty) hParams (by rw [hLocals]; decide) hOwned
  have hNonzero : root ≠ 0 := by
    intro hZero
    rw [hZero] at hRoot
    contradiction
  rw [output_release_shape]
  simp only [outputReleaseProgram, List.cons_append, List.nil_append]
  wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff,
    hParams, hLocals, hValues, hCurrent', hOutput', hOwned', hOutputNonzero]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simp [hOutputNonzero])]
  wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff, hParams, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  by_cases hCount : count = 0
  · have hSame := hEmpty.mpr hCount
    wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff,
      hParams, hLocals, hCurrent', hOwned', hSame, hNonzero, hSeparate]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simp)]
    wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff, hParams, hLocals]
    simpa only [outputReleaseFrame, List.foldl, resultFrame, hParams, Nat.reduceSub, hCount,
      ↓reduceIte, ne_eq, not_true_eq_false, ite_false, List.nil_append, List.append_nil, List.append] using hNext
  · have hDifferent : root ≠ empty := fun h => hCount (hEmpty.mp h)
    wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff,
      hParams, hLocals, hCurrent', hOwned', hDifferent, hNonzero, hSeparate]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp [hSeparate, hDifferent, hNonzero])]
    wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff, hParams, hLocals, hCurrent']
    refine wp_call_tw (output_release_exact env initial root capacity head releases frees input
      hRoot hHeader hInput hHead hReleases hFrees) ?_
    rintro final values ⟨rfl, rfl⟩
    wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff, hParams, hLocals]
    simpa only [outputReleaseFrame, List.foldl, resultFrame, hParams, Nat.reduceSub, hCount,
      ↓reduceIte, ne_eq, not_true_eq_false, ite_false, List.nil_append, List.append_nil, List.append] using hNext

#print axioms output_release_region_spec
end Project.TinyGpt2Infer.Spec
