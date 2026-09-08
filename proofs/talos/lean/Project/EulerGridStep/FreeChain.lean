import Project.EulerGridStep.ReleaseFramed

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- A finite free list of equally sized buffers, with readable headers and physical bounds. -/
def FreeChain (current : Store Unit) (count : Nat) : List UInt64 → Prop
  | [] => True
  | root :: rest =>
      FreeHeader current root (fieldRequest count) (rest.headD 0) ∧
      root.toNat + 8 * (count + 1) ≤ 4294967296 ∧
      root.toNat + 8 * (count + 1) ≤ current.mem.pages * 65536 ∧
      FreeChain current count rest

theorem freeChain_of_header_frame (initial final : Store Unit) (count : Nat) (roots : List UInt64)
    (hChain : FreeChain initial count roots) (hPages : final.mem.pages = initial.mem.pages)
    (hHeaders : ∀ root ∈ roots, ∀ next, FreeHeader initial root (fieldRequest count) next →
      FreeHeader final root (fieldRequest count) next) :
    FreeChain final count roots := by
  induction roots with
  | nil => trivial
  | cons root rest ih =>
      rcases hChain with ⟨hHeader, hFit32, hFitMemory, hTail⟩
      exact ⟨hHeaders root (by simp) _ hHeader, hFit32,
        by rw [hPages]; exact hFitMemory,
        ih hTail (fun p hp next h => hHeaders p (by simp [hp]) next h)⟩

theorem FieldResult.preserves_free_chain {choice : FieldAllocation} {initial final : Store Unit}
    {source : UInt64} {input : Array UInt64} {index : Nat} {value : UInt64}
    (hResult : FieldResult choice initial final source input index value)
    (count : Nat) (roots : List UInt64) (hChain : FreeChain initial count roots)
    (hSeparate : ∀ other ∈ roots, ObjectsSeparate choice.root input.size other count) :
    FreeChain final count roots := by
  apply freeChain_of_header_frame initial final count roots hChain hResult.pages
  intro other hOther next hHeader
  exact hResult.preserves_free_header other (fieldRequest count) next count hHeader
    (hSeparate other hOther)

theorem ReleaseResult.preserves_free_chain {initial final : Store Unit} {root capacity next : UInt64}
    {input : Array UInt64} (hResult : ReleaseResult initial final root capacity next input)
    (count : Nat) (roots : List UInt64) (hChain : FreeChain initial count roots)
    (hSeparate : ∀ other ∈ roots, ObjectsSeparate root input.size other count) :
    FreeChain final count roots := by
  apply freeChain_of_header_frame initial final count roots hChain hResult.pages
  intro other hOther otherNext hHeader
  exact hResult.preserves_free_header other (fieldRequest count) otherNext count hHeader
    (hSeparate other hOther)

/-- The first bounded free node supplies all concrete allocator preconditions. -/
theorem freeChain_allocation_valid (initial : Store Unit) (source root allocs : UInt64)
    (input : Array UInt64) (rest : List UInt64)
    (hChain : FreeChain initial input.size (root :: rest))
    (hFreeList : initial.globals.globals[1]? = some (.i64 root))
    (hAllocs : initial.globals.globals[2]? = some (.i64 allocs))
    (hSeparate : ObjectsSeparate root input.size source input.size) :
    (FieldAllocation.reuse root (fieldRequest input.size) (rest.headD 0) allocs).Valid
      initial source input := by
  rcases hChain with ⟨hHeader, hFit32, hFitMemory, _⟩
  have hSize : 8 * (input.size + 1) < UInt64.size := by
    change 8 * (input.size + 1) < 18446744073709551616
    omega
  have hRequestNat : (fieldRequest input.size).toNat = 8 * (input.size + 1) :=
    UInt64.toNat_ofNat_of_lt' hSize
  refine ⟨⟨hFreeList, hAllocs, hHeader.capacityRead, hHeader.nextRead⟩,
    hHeader.root48, hHeader.root32, ?_, ?_, ?_, ?_⟩
  · change 8 * (input.size + 1) ≤ (fieldRequest input.size).toNat
    rw [hRequestNat]
  · change root.toNat + (fieldRequest input.size).toNat ≤ 4294967296
    rwa [hRequestNat]
  · change root.toNat + (fieldRequest input.size).toNat ≤ initial.mem.pages * 65536
    rwa [hRequestNat]
  · change source.toNat + 8 * (input.size + 1) ≤ root.toNat - 48 ∨
      root.toNat + 8 * (input.size + 1) ≤ source.toNat
    unfold ObjectsSeparate at hSeparate
    omega

/-- A released buffer becomes a bounded new head while preserving the previous chain. -/
theorem freeChain_release_cons (initial final : Store Unit) (root : UInt64)
    (input : Array UInt64) (rest : List UInt64)
    (hResult : ReleaseResult initial final root (fieldRequest input.size) (rest.headD 0) input)
    (hChain : FreeChain initial input.size rest)
    (hSeparate : ∀ other ∈ rest, ObjectsSeparate root input.size other input.size) :
    FreeChain final input.size (root :: rest) :=
  ⟨hResult.header, hResult.array.1, hResult.array.2.1,
    hResult.preserves_free_chain input.size rest hChain hSeparate⟩

#print axioms freeChain_of_header_frame
#print axioms FieldResult.preserves_free_chain
#print axioms ReleaseResult.preserves_free_chain
#print axioms freeChain_allocation_valid
#print axioms freeChain_release_cons
end Project.EulerGridStep.Execution
