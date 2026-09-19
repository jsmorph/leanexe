import Project.ProofKit.PackedReleaseGuard

namespace Project.ProofKit.PackedReleaseMany
open Wasm Project.Runtime Project.EulerRiemann.Execution

structure Item where
  ownerLocal : Nat
  node : FreeNode
  bytes : ByteArray

def program (items : List Item) (firstLocal secondLocal releaseId : Nat) : Wasm.Program :=
  items.flatMap fun item =>
    PackedReleaseGuard.programTwo item.ownerLocal firstLocal secondLocal releaseId

def finalHeap (heap : Heap) : List Item → Heap
  | [] => heap
  | item :: items => finalHeap (heap.release item.node) items

def finalStore (heap : Heap) (store : Store Unit) : List Item → Store Unit
  | [] => store
  | item :: items => finalStore (heap.release item.node) (heap.releaseStore store item.node) items

theorem finalStore_pages (heap : Heap) (store : Store Unit) (items : List Item) :
    (finalStore heap store items).mem.pages = store.mem.pages := by
  induction items generalizing heap store with
  | nil => rfl
  | cons item items ih => exact ih _ _

theorem finalStore_memoryCap (heap : Heap) (store : Store Unit) (items : List Item)
    (module_ : Wasm.Module) (index : Nat) :
    (finalStore heap store items).memoryCap module_ index = store.memoryCap module_ index := by
  induction items generalizing heap store with
  | nil => rfl
  | cons item items ih => exact ih _ _

theorem program_spec (env : HostEnv Unit) (module_ : Wasm.Module) (releaseId : Nat)
    (initial : Store Unit) (heap : Heap) (before : Heap) (original : Store Unit)
    (frame : Locals) (items : List Item) (first second : FreeNode)
    (firstBytes secondBytes : ByteArray) (firstLocal secondLocal : Nat)
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
    (hFirstBinding : frame.get firstLocal = some (.i64 first.root))
    (hSecondBinding : frame.get secondLocal = some (.i64 second.root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : (finalHeap heap items).At (finalStore heap initial items) →
      (finalHeap heap items).OwnsPacked (finalStore heap initial items) first firstBytes →
      (finalHeap heap items).OwnsPacked (finalStore heap initial items) second secondBytes →
      before.Frame original (finalHeap heap items) (finalStore heap initial items) →
      wp module_ rest Q (finalStore heap initial items) frame env) :
    wp module_ (program items firstLocal secondLocal releaseId ++ rest) Q initial frame env := by
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
    apply PackedReleaseGuard.programTwo_spec env module_ releaseId initial heap frame item.node item.bytes
      first.root second.root item.ownerLocal firstLocal secondLocal hFunction hImport hHeap hOwner
      hValues (hBindings item (by simp)) hFirstBinding hSecondBinding
      (hOwner.root_ne (hFirstSep item (by simp))) (hOwner.root_ne (hSecondSep item (by simp)))
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
    · exact hNext

#print axioms program_spec

end Project.ProofKit.PackedReleaseMany
