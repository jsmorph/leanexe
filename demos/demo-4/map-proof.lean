import LeanExeGen.GeneratedRc77513211b55010d.FormalSpec
import LeanExeGen.GeneratedRc77513211b55010d.Program
import LeanExeGen.GeneratedRc77513211b55010d.AnnotationMatches
import Project.ProofKit.FixedArrayMapAdd

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRc77513211b55010d.Behavior

open Wasm Project.ProofKit

theorem artifact_behavior :
    LeanExeGen.GeneratedRc77513211b55010d.FormalSpec.ArtifactSpec LeanExeGen.GeneratedRc77513211b55010d.«module» := by
  refine ⟨0, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with
    ⟨hArray, heapTop, allocs, retains, releases, frees, hGlobals,
      hInputBelow, hFit32, hFitMemory, hPages⟩
  change UInt64Array.At initial inputPtr input at hArray
  have hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop) := by
    simp [hGlobals]
  have hFreeList : initial.globals.globals[1]? = some (.i64 0) := by
    simp [hGlobals]
  have hAllocs : initial.globals.globals[2]? = some (.i64 allocs) := by
    simp [hGlobals]
  have hAtIff (st : Store Unit) (ptr : UInt64) (values : Array UInt64) :
      LeanExeGen.GeneratedRc77513211b55010d.FormalSpec.UInt64ArrayAt st ptr values ↔
        UInt64Array.At st ptr values := by
    rfl
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRc77513211b55010d.func0Def) rfl
  unfold LeanExeGen.GeneratedRc77513211b55010d.func0Def
  simp only [Wasm.Function.numParams, List.length, List.drop,
    Nat.zero_add, List.append_nil]
  simp only [hAtIff]
  apply Wasm.wp.conseq (Q :=
    FixedArrayPairResult.publicPost (LeanExeGen.GeneratedRc77513211b55010d.FormalSpec.expected input))
  · intro continuation hPost
    cases continuation <;> simp_all [FixedArrayPairResult.publicPost]
  have hProgram : LeanExeGen.GeneratedRc77513211b55010d.func0 =
      FixedArrayMapAdd.wrapperProgram 8 1 := by
    simpa [Annotation.region, Annotation.resolve,
      LeanExeGen.GeneratedRc77513211b55010d.func0] using
      LeanExeGen.GeneratedRc77513211b55010d.AnnotationMatches.function_0_map_add_0_eq
  have hExpected : LeanExeGen.GeneratedRc77513211b55010d.FormalSpec.expected input =
      FixedArrayMapAdd.expected 8 1 input := by
    rfl
  change wp LeanExeGen.GeneratedRc77513211b55010d.«module» LeanExeGen.GeneratedRc77513211b55010d.func0
    (FixedArrayPairResult.publicPost (LeanExeGen.GeneratedRc77513211b55010d.FormalSpec.expected input))
    initial (FixedArrayMapAdd.entryFrame inputPtr) env
  rw [hProgram, hExpected]
  apply FixedArrayMapAdd.wrapperProgram_spec 8 1
    LeanExeGen.GeneratedRc77513211b55010d.«module» env initial inputPtr input heapTop allocs
  · norm_num [UInt64.size]
  · exact hArray
  · exact hInputBelow
  · exact hFit32
  · exact hFitMemory
  · exact hPages
  · rfl
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs

end LeanExeGen.GeneratedRc77513211b55010d.Behavior
