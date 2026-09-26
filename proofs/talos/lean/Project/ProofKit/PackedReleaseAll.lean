import Project.ProofKit.PackedOwners

namespace Project.ProofKit.PackedReleaseAll
open Wasm Project.Runtime Project.EulerRiemann.Execution PackedReleaseMany

theorem program_spec (env : HostEnv Unit) (module_ : Wasm.Module) (releaseId : Nat)
    (initial : Store Unit) (heap before : Heap) (original : Store Unit)
    (frame : Locals) (items : List Item) (firstLocal secondLocal : Nat)
    {typeIdx : Option Nat}
    (hFunction : module_.funcs[releaseId - module_.imports.length]? =
      some { releaseFuncDef releaseId with typeIdx := typeIdx })
    (hImport : module_.imports[releaseId]? = none)
    (hHeap : heap.At initial) (hOwners : Owners before heap initial items)
    (hFrame : before.Frame original heap initial)
    (hValues : frame.values = [])
    (hBindings : ∀ item ∈ items, frame.get item.ownerLocal = some (.i64 item.node.root))
    (hFirst : frame.get firstLocal = some (.i64 0))
    (hSecond : frame.get secondLocal = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : (finalHeap heap items).At (finalStore heap initial items) →
      before.Frame original (finalHeap heap items) (finalStore heap initial items) →
      wp module_ rest Q (finalStore heap initial items) frame env) :
    wp module_ (program items firstLocal secondLocal releaseId ++ rest) Q initial frame env := by
  induction items generalizing heap initial with
  | nil => exact hNext hHeap hFrame
  | cons item items ih =>
    have hOwner := hOwners.owned item (by simp)
    have hRoot := hOwner.buffer.rootBound
    have hRoot32 : item.node.root.toNat ≤ 4294967296 := by
      have := hOwner.buffer.addressBound
      omega
    have hNonzero : item.node.root ≠ 0 := by
      intro hZero
      rw [hZero] at hRoot
      contradiction
    have hPair := List.pairwise_cons.mp hOwners.disjoint
    simp only [program, List.flatMap_cons, List.append_assoc]
    apply PackedReleaseGuard.programTwo_spec env module_ releaseId initial heap frame item.node item.bytes
      0 0 item.ownerLocal firstLocal secondLocal hFunction hImport hHeap hOwner hValues
      (hBindings item (by simp)) hFirst hSecond hNonzero hNonzero
    intro hReleased
    apply ih (heap := heap.release item.node) (initial := heap.releaseStore initial item.node) hReleased
    · refine ⟨?_, hPair.2, ?_⟩
      · intro other hOther
        exact (hOwners.owned other (by simp [hOther])).released item.node hRoot hRoot32
          (regionsDisjoint_symm (hPair.1 other hOther))
      · intro other hOther
        exact hOwners.fresh other (by simp [hOther])
    · exact hFrame.released item.node hRoot hRoot32 (hOwners.fresh item (by simp))
    · intro other hOther
      exact hBindings other (by simp [hOther])
    · exact hNext

#print axioms program_spec
end Project.ProofKit.PackedReleaseAll
