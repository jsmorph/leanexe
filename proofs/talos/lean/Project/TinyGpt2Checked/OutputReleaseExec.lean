import Project.TinyGpt2Checked.OutputCode
import Project.TinyGpt2Checked.OutputRelease
import Project.TinyGpt2Checked.OutputFrame
import Project.ProofKit.FixedFrame
import Project.ProofKit.FixedArrayFrame

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.ProofKit Project.Clob FixedArrayFold

def outputReleaseProgram : Wasm.Program :=
  [.localGet 56,
   .localSet 39,
   .localGet 39,
   .localSet 40,
   .localGet 39,
   .localSet 41,
   .localGet 40,
   .localSet 42,
   .localGet 41,
   .localSet 68,
   .localGet 42,
   .localSet 69,
   .constI64 0,
   .localSet 67,
   .localGet 70,
   .constI64 0,
   .neI64,
   .iff 0 0 [
     .localGet 24,
     .constI64 0,
     .neI64,
     .iff 0 0 [
      .localGet 24,
      .call 89
     ] []
    ] [],
   .localGet 68,
   .localSet 24,
   .localGet 69,
   .localSet 25,
   .constI64 1,
   .localSet 70,
   .localGet 67,
   .constI64 0,
   .neI64,
   .br_if 1]

theorem output_release_shape : (outputBody.drop 103).take 28 = outputReleaseProgram := rfl

def outputReleaseFrame (frame : Locals) (output : UInt64) : Locals :=
  [(39, output), (40, output), (41, output), (42, output), (68, output), (69, output),
    (67, 0), (24, output), (25, output), (70, 1)].foldl
      (fun current assignment => resultFrame current assignment.1 assignment.2) frame

theorem outputReleaseFrame_saved {frame : Locals} {owner pointer empty : UInt64}
    {x : Project.TinyGpt2.Row} (h : OutputSaved owner pointer empty x frame) (output : UInt64) :
    OutputSaved owner pointer empty x (outputReleaseFrame frame output) := by
  unfold outputReleaseFrame
  simp only [List.foldl]
  repeat first
    | exact h
    | refine OutputSaved.result ?_ _ _ (by decide) (by decide) (by decide)

theorem outputReleaseFrame_get (frame : Locals) (output : UInt64)
    (hParams : frame.params.length = 6) (hLocals : frame.locals.length = 65) :
    let next := outputReleaseFrame frame output
    next.get 24 = some (.i64 output) ∧ next.get 25 = some (.i64 output) ∧
    next.get 49 = frame.get 49 ∧ next.get 70 = some (.i64 1) := by
  simp [outputReleaseFrame, List.foldl, resultFrame, Locals.get, hParams, hLocals,
    List.getElem?_set]

theorem output_release_region_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (root capacity head releases frees output : UInt64) (input : Array UInt64) (count : Nat)
    (hParams : frame.params.length = 6) (hLocals : frame.locals.length = 65)
    (hValues : frame.values = [])
    (hCurrent : frame.get 24 = some (.i64 root)) (hOutput : frame.get 56 = some (.i64 output))
    (hOwned : frame.get 70 = some (.i64 (if count = 0 then 0 else 1)))
    (hRoot : 48 ≤ root.toNat) (hHeader : FreshFixedArrayAt initial root capacity 1)
    (hInput : UInt64Array.At initial root input)
    (hHead : initial.globals.globals[1]? = some (.i64 head))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q
      (if count = 0 then initial else FixedArrayRelease.store initial root head releases frees)
      (outputReleaseFrame frame output) env) :
    wp module ((outputBody.drop 103).take 28 ++ rest) Q initial frame env := by
  have hCurrent' := Frame.internal_getElem?_of_get frame 6 18 (.i64 root)
    hParams (by rw [hLocals]; decide) hCurrent
  have hOutput' := Frame.internal_getElem?_of_get frame 6 50 (.i64 output)
    hParams (by rw [hLocals]; decide) hOutput
  have hOwned' := Frame.internal_getElem?_of_get frame 6 64
    (.i64 (if count = 0 then 0 else 1)) hParams (by rw [hLocals]; decide) hOwned
  have hNonzero : root ≠ 0 := by
    intro hZero
    rw [hZero] at hRoot
    contradiction
  rw [output_release_shape]
  simp only [outputReleaseProgram, List.cons_append, List.nil_append]
  by_cases hCount : count = 0
  · wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff,
      hParams, hLocals, hValues, hCurrent', hOutput', hOwned', hCount]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simp)]
    wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff, hParams, hLocals]
    simpa only [outputReleaseFrame, List.foldl, resultFrame, hParams, Nat.reduceSub, hCount,
      ↓reduceIte, ne_eq, not_true_eq_false, ite_false, List.nil_append] using hNext
  · wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff,
      hParams, hLocals, hValues, hCurrent', hOutput', hOwned', hCount]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide)]
    wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff,
      hParams, hLocals, hCurrent', hNonzero]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp [hNonzero])]
    wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff, hParams, hLocals, hCurrent']
    refine wp_call_tw (output_release_exact env initial root capacity head releases frees input
      hRoot hHeader hInput hHead hReleases hFrees) ?_
    rintro final values ⟨rfl, rfl⟩
    wp_fixed_frame [List.length_set, List.getElem?_set, Nat.reduceEqDiff, hParams, hLocals]
    simpa only [outputReleaseFrame, List.foldl, resultFrame, hParams, Nat.reduceSub, hCount,
      ↓reduceIte, ne_eq, not_true_eq_false, ite_false, List.nil_append] using hNext

#print axioms output_release_region_spec
end Project.TinyGpt2Checked.Spec
