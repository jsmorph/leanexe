import Project.ProofKit.PackedReleaseManyAliases

namespace Project.Gpt2CachedStep.CachedBlock
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open PackedReleaseMany

def cleanupOwners : List Nat := [139, 122, 113, 96, 81, 69, 52, 38, 21]

def cleanupKept : Nat → List Nat
  | 139 => [161, 164, 125, 122, 119, 116, 113, 105, 99, 96, 90, 84, 81, 78, 72, 69, 61, 55, 52, 47, 41, 38, 30, 24, 21]
  | 122 => [161, 164, 116, 113, 105, 99, 96, 90, 84, 81, 78, 72, 69, 61, 55, 52, 47, 41, 38, 30, 24, 21]
  | 113 => [161, 164, 99, 96, 90, 84, 81, 78, 72, 69, 61, 55, 52, 47, 41, 38, 30, 24, 21]
  | 96 => [161, 164, 84, 81, 78, 72, 69, 61, 55, 52, 47, 41, 38, 30, 24, 21]
  | 81 => [161, 164, 72, 69, 61, 55, 52, 47, 41, 38, 30, 24, 21]
  | 69 => [161, 164, 55, 52, 47, 41, 38, 30, 24, 21]
  | 52 => [161, 164, 41, 38, 30, 24, 21]
  | 38 => [161, 164, 24, 21]
  | 21 => [161, 164]
  | _ => []

def ownerAliases : Nat → List Nat
  | 139 => [139]
  | 122 => [122, 125]
  | 113 => [113, 116, 119]
  | 96 => [96, 99, 105]
  | 81 => [81, 84, 90]
  | 69 => [69, 72, 78]
  | 52 => [52, 55, 61]
  | 38 => [38, 41, 47]
  | 21 => [21, 24, 30]
  | owner => [owner]

/-- Every guarded local holds a retained result or a different temporary owner. -/
theorem cleanupKept_coverage (owner slot : Nat) (hOwner : owner ∈ cleanupOwners)
    (hSlot : slot ∈ cleanupKept owner) :
    slot = 161 ∨ slot = 164 ∨ ∃ other ∈ cleanupOwners,
      owner ≠ other ∧ slot ∈ ownerAliases other := by
  have checked : cleanupOwners.all (fun owner => (cleanupKept owner).all fun slot =>
      slot == 161 || slot == 164 || cleanupOwners.any (fun other =>
        owner != other && (ownerAliases other).contains slot)) = true := by decide
  have h := List.all_eq_true.mp (List.all_eq_true.mp checked owner hOwner) slot hSlot
  simpa [List.any_eq_true, or_assoc] using h

theorem disjoint_of_owner_ne {items : List Item}
    (h : items.Pairwise fun a b => regionsDisjoint a.node.region b.node.region)
    {a b : Item} (ha : a ∈ items) (hb : b ∈ items) (hne : a.ownerLocal ≠ b.ownerLocal) :
    regionsDisjoint a.node.region b.node.region := by
  induction items with
  | nil => simp at ha
  | cons first rest ih =>
    obtain ⟨hFirst, hRest⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with rfl | haRest
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact False.elim (hne rfl)
      · exact hFirst b hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact regionsDisjoint_symm (hFirst a haRest)
      · exact ih hRest haRest hb

theorem cleanup_bindings (heap : Heap) (store : Store Unit) (frame : Locals) (items : List Item)
    (hidden cache : FreeNode)
    (hLocals : items.map (·.ownerLocal) = cleanupOwners)
    (hOwners : ∀ item ∈ items, heap.OwnsPacked store item.node item.bytes)
    (hDisjoint : items.Pairwise fun a b => regionsDisjoint a.node.region b.node.region)
    (hHiddenSep : ∀ item ∈ items, regionsDisjoint item.node.region hidden.region)
    (hCacheSep : ∀ item ∈ items, regionsDisjoint item.node.region cache.region)
    (hAliases : ∀ item ∈ items, ∀ slot ∈ ownerAliases item.ownerLocal,
      frame.get slot = some (.i64 item.node.root))
    (hHidden : frame.get 161 = some (.i64 hidden.root))
    (hCache : frame.get 164 = some (.i64 cache.root)) :
    ∀ item ∈ items, ∀ slot ∈ cleanupKept item.ownerLocal, ∃ other : UInt64,
      frame.get slot = some (.i64 other) ∧ item.node.root ≠ other := by
  intro item hItem slot hSlot
  have hOwner : item.ownerLocal ∈ cleanupOwners := by
    rw [← hLocals]
    exact List.mem_map.mpr ⟨item, hItem, rfl⟩
  rcases cleanupKept_coverage item.ownerLocal slot hOwner hSlot with rfl | rfl | ⟨other, hOther, hNe, hAlias⟩
  · exact ⟨hidden.root, hHidden, (hOwners item hItem).root_ne (hHiddenSep item hItem)⟩
  · exact ⟨cache.root, hCache, (hOwners item hItem).root_ne (hCacheSep item hItem)⟩
  · rw [← hLocals] at hOther
    obtain ⟨otherItem, hOtherItem, rfl⟩ := List.mem_map.mp hOther
    exact ⟨otherItem.node.root, hAliases otherItem hOtherItem slot hAlias,
      (hOwners item hItem).root_ne (disjoint_of_owner_ne hDisjoint hItem hOtherItem hNe)⟩

#print axioms cleanupKept_coverage
#print axioms cleanup_bindings
end Project.Gpt2CachedStep.CachedBlock
