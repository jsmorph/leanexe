import LeanExeGen.GeneratedRc28a1499719cbaa0.FormalSpec
import LeanExeGen.GeneratedRc28a1499719cbaa0.Program
import LeanExeGen.GeneratedRc28a1499719cbaa0.AnnotationMatches
import Project.ProofKit.FixedArrayFilterLt

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRc28a1499719cbaa0.Behavior

open Wasm Project.ProofKit

theorem artifact_behavior :
    LeanExeGen.GeneratedRc28a1499719cbaa0.FormalSpec.ArtifactSpec LeanExeGen.GeneratedRc28a1499719cbaa0.«module» := by
  refine ⟨0, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with
    ⟨hArray, heapTop, allocs, retains, releases, frees, hGlobals,
      hInputBelow, hOutputFit32, hOutputFitMemory,
      hHeapFit32, hHeapFitMemory, hPages⟩
  change UInt64Array.At initial inputPtr input at hArray
  have hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop) := by
    simp [hGlobals]
  have hFreeList : initial.globals.globals[1]? = some (.i64 0) := by
    simp [hGlobals]
  have hAllocs : initial.globals.globals[2]? = some (.i64 allocs) := by
    simp [hGlobals]
  have hAtIff (st : Store Unit) (ptr : UInt64) (values : Array UInt64) :
      LeanExeGen.GeneratedRc28a1499719cbaa0.FormalSpec.UInt64ArrayAt st ptr values ↔
        UInt64Array.At st ptr values := by
    rfl
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRc28a1499719cbaa0.func0Def) rfl
  unfold LeanExeGen.GeneratedRc28a1499719cbaa0.func0Def
  simp only [Wasm.Function.numParams, List.length, List.drop,
    Nat.zero_add, List.append_nil]
  simp only [hAtIff]
  apply Wasm.wp.conseq (Q :=
    FixedArrayPairResult.publicPost (LeanExeGen.GeneratedRc28a1499719cbaa0.FormalSpec.expected input))
  · intro continuation hPost
    cases continuation <;> simp_all [FixedArrayPairResult.publicPost]
  have hProgram : LeanExeGen.GeneratedRc28a1499719cbaa0.func0 =
      FixedArrayFilterLt.wrapperProgram 8 100 := by
    simpa [Annotation.region, Annotation.resolve,
      LeanExeGen.GeneratedRc28a1499719cbaa0.func0] using
      LeanExeGen.GeneratedRc28a1499719cbaa0.AnnotationMatches.function_0_filter_lt_0_eq
  have hExpected : LeanExeGen.GeneratedRc28a1499719cbaa0.FormalSpec.expected input =
      FixedArrayFilterLt.expected 8 100 input := by
    rfl
  have hReserve : LeanExeGen.GeneratedRc28a1499719cbaa0.FormalSpec.heapReserveBytes input =
      FixedArrayFilterLt.heapReserveBytes 8 input := by
    rfl
  rw [hReserve] at hHeapFitMemory
  change wp LeanExeGen.GeneratedRc28a1499719cbaa0.«module» LeanExeGen.GeneratedRc28a1499719cbaa0.func0
    (FixedArrayPairResult.publicPost (LeanExeGen.GeneratedRc28a1499719cbaa0.FormalSpec.expected input))
    initial (FixedArrayFilterLt.entryFrame inputPtr) env
  rw [hProgram, hExpected]
  apply FixedArrayFilterLt.wrapperProgram_spec 8 100
    LeanExeGen.GeneratedRc28a1499719cbaa0.«module» env initial inputPtr input heapTop allocs
  · norm_num [UInt64.size]
  · exact hArray
  · exact hInputBelow
  · exact hHeapFitMemory
  · exact hPages
  · rfl
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs

end LeanExeGen.GeneratedRc28a1499719cbaa0.Behavior
