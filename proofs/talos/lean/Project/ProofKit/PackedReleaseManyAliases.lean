import Project.ProofKit.PackedReleaseMany
import Project.ProofKit.PackedReleaseAliases

namespace Project.ProofKit.PackedReleaseManyAliases
open Wasm Project.Runtime Project.EulerRiemann.Execution PackedReleaseMany

/-- Sequential cleanup with the compiler's per-owner retained-local lists. -/
def program (items : List Item) (kept : Nat → List Nat) (releaseId : Nat) : Wasm.Program :=
  items.flatMap fun item => PackedReleaseAliases.program item.ownerLocal (kept item.ownerLocal) releaseId

theorem program_spec (env : HostEnv Unit) (module_ : Wasm.Module) (releaseId : Nat)
    (initial : Store Unit) (heap : Heap) (before : Heap) (original : Store Unit)
    (frame : Locals) (items : List Item) (first second : FreeNode)
    (firstBytes secondBytes : ByteArray) (kept : Nat → List Nat)
    {typeIdx : Option Nat}
    (hFunction : module_.funcs[releaseId - module_.imports.length]? =
      some { releaseFuncDef releaseId with typeIdx := typeIdx })
    (hImport : module_.imports[releaseId]? = none)
    (hHeap : heap.At initial)
    (hOwners : ∀ item ∈ items, heap.OwnsPacked initial item.node item.bytes)
    (hFirst : heap.OwnsPacked initial first firstBytes)
    (hSecond : heap.OwnsPacked initial second secondBytes)
    (hDisjoint : items.Pairwise fun a b => regionsDisjoint a.node.region b.node.region)
    (hFirstSep : ∀ item ∈ items, regionsDisjoint item.node.region first.region)
    (hSecondSep : ∀ item ∈ items, regionsDisjoint item.node.region second.region)
    (hFrame : before.Frame original heap initial)
    (hProtected : ∀ item ∈ items, ∀ lo hi, before.Protects lo hi →
      hi ≤ item.node.root.toNat - 48 ∨ item.node.root.toNat + item.node.capacity.toNat ≤ lo)
    (hValues : frame.values = [])
    (hBindings : ∀ item ∈ items, frame.get item.ownerLocal = some (.i64 item.node.root))
    (hKept : ∀ item ∈ items, ∀ slot ∈ kept item.ownerLocal, ∃ other : UInt64,
      frame.get slot = some (.i64 other) ∧ item.node.root ≠ other)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : (finalHeap heap items).At (finalStore heap initial items) →
      (finalHeap heap items).OwnsPacked (finalStore heap initial items) first firstBytes →
      (finalHeap heap items).OwnsPacked (finalStore heap initial items) second secondBytes →
      before.Frame original (finalHeap heap items) (finalStore heap initial items) →
      wp module_ rest Q (finalStore heap initial items) frame env) :
    wp module_ (program items kept releaseId ++ rest) Q initial frame env := by
  induction items generalizing heap initial with
  | nil =>
    simpa only [program, List.flatMap_nil, List.nil_append, finalStore] using
      hNext hHeap hFirst hSecond hFrame
  | cons item items ih =>
    have hOwner := hOwners item (by simp)
    have hRoot := hOwner.buffer.rootBound
    have hRoot32 : item.node.root.toNat ≤ 4294967296 := by
      have := hOwner.buffer.addressBound
      omega
    have hPair := List.pairwise_cons.mp hDisjoint
    simp only [program, List.flatMap_cons, List.append_assoc]
    apply PackedReleaseAliases.program_spec env module_ releaseId initial heap frame item.node item.bytes
      item.ownerLocal (kept item.ownerLocal) hFunction hImport hHeap hOwner
      hValues (hBindings item (by simp)) (hKept item (by simp))
    intro hReleased
    apply ih (heap := heap.release item.node) (initial := heap.releaseStore initial item.node) hReleased
    · intro other hOther
      exact (hOwners other (by simp [hOther])).released item.node hRoot hRoot32
        (regionsDisjoint_symm (hPair.1 other hOther))
    · exact hFirst.released item.node hRoot hRoot32 (regionsDisjoint_symm (hFirstSep item (by simp)))
    · exact hSecond.released item.node hRoot hRoot32 (regionsDisjoint_symm (hSecondSep item (by simp)))
    · exact hPair.2
    · intro other hOther
      exact hFirstSep other (by simp [hOther])
    · intro other hOther
      exact hSecondSep other (by simp [hOther])
    · exact hFrame.released item.node hRoot hRoot32 (hProtected item (by simp))
    · intro other hOther
      exact hProtected other (by simp [hOther])
    · intro other hOther
      exact hBindings other (by simp [hOther])
    · intro other hOther
      exact hKept other (by simp [hOther])
    · exact hNext

#print axioms program_spec
end Project.ProofKit.PackedReleaseManyAliases
