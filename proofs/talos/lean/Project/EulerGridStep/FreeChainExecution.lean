import Project.EulerGridStep.FreeChain

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

theorem FieldResult.globals {choice : FieldAllocation} {initial final : Store Unit}
    {source : UInt64} {input : Array UInt64} {index : Nat} {value : UInt64}
    (hResult : FieldResult choice initial final source input index value) :
    final.globals.globals = (choice.store initial input.size).globals.globals := by
  have h := congrArg (fun s : Store Unit => s.globals.globals) hResult.write.frame
  exact h

/-- A complete field write consumes one bounded free node and preserves the remaining chain. -/
theorem writeCellField_from_free_chain {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused source root allocs : UInt64)
    (input : Array UInt64) (rest : List UInt64) (index field : Nat) (value : UInt64)
    (hInput : UInt64Array.At initial source input) (hi : 1 + 6 * index + field < input.size)
    (hChain : FreeChain initial input.size (root :: rest))
    (hFreeList : initial.globals.globals[1]? = some (.i64 root))
    (hAllocs : initial.globals.globals[2]? = some (.i64 allocs))
    (hSeparateSource : ObjectsSeparate root input.size source input.size)
    (hSeparateTail : ∀ other ∈ rest, ObjectsSeparate root input.size other input.size)
    (hPages : initial.mem.pages ≤ 65536) :
    TerminatesWith env m 27 initial
      [.i64 value, .i64 (UInt64.ofNat field), .i64 (UInt64.ofNat index), .i64 source, .i64 unused]
      (fun final values => values = [.i64 root, .i64 root] ∧
        FieldResult (.reuse root (fieldRequest input.size) (rest.headD 0) allocs)
          initial final source input (1 + 6 * index + field) value ∧
        FreeChain final input.size rest ∧
        final.globals.globals =
          (initial.globals.globals.set 1 (.i64 (rest.headD 0))).set 2 (.i64 (allocs + 1))) := by
  have hValid := freeChain_allocation_valid initial source root allocs input rest
    hChain hFreeList hAllocs hSeparateSource
  apply (writeCellField_exact_in_module layout
    (.reuse root (fieldRequest input.size) (rest.headD 0) allocs) env initial unused source
    input index field value hInput hi hValid hPages).mono
  rintro final values ⟨hValues, hResult⟩
  refine ⟨hValues, hResult,
    hResult.preserves_free_chain input.size rest hChain.2.2.2 hSeparateTail, ?_⟩
  simpa only [FieldAllocation.store, reuseAllocatedStore, reuseStore, writeAllocationHeader,
    writeHeaderWord, reuseUnlinkedStore] using hResult.globals

/-- Exact release adds the owned scalar buffer as the head of a preserved free chain. -/
theorem release_owned_to_free_chain {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (root releases frees : UInt64)
    (input : Array UInt64) (rest : List UInt64)
    (hHeader : OwnedHeader initial root (fieldRequest input.size))
    (hArray : UInt64Array.At initial root input)
    (hChain : FreeChain initial input.size rest)
    (hFreeList : initial.globals.globals[1]? = some (.i64 (rest.headD 0)))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees))
    (hSeparate : ∀ other ∈ rest, ObjectsSeparate root input.size other input.size) :
    TerminatesWith env m 40 initial [.i64 root]
      (fun final values => values = [] ∧
        ReleaseResult initial final root (fieldRequest input.size) (rest.headD 0) input ∧
        FreeChain final input.size (root :: rest) ∧
        final.globals.globals =
          ((initial.globals.globals.set 4 (.i64 (releases + 1))).set 5
            (.i64 (frees + 1))).set 1 (.i64 root)) := by
  apply (release_owned_framed layout env initial root (fieldRequest input.size)
    (rest.headD 0) releases frees input hHeader hArray hFreeList hReleases hFrees).mono
  rintro final values ⟨hValues, hGlobals, hResult⟩
  exact ⟨hValues, hResult, freeChain_release_cons initial final root input rest hResult hChain hSeparate,
    hGlobals⟩

#print axioms FieldResult.globals
#print axioms writeCellField_from_free_chain
#print axioms release_owned_to_free_chain
end Project.EulerGridStep.Execution
