import Verified.TreeCopyStep

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def copyBlocks (store : Store Unit) (current : CopyRecord) (parents : List CopyRecord) :
    List (Nat × Nat) := current.blocks store ++ parents.flatMap (fun record => record.blocks store)

def CopyFrames (shape : TreeShape) (heap : Heap) (store : Store Unit) (current : CopyRecord) :
    List CopyRecord → Prop
  | [] => current.Holds shape heap store 0
  | parent :: parents => current.Holds shape heap store parent.pointer ∧
      CopyFrames shape heap store parent parents

def CopyRecord.Kept (keep : Nat × Nat → Prop) (store : Store Unit) (record : CopyRecord) : Prop :=
  keep (block store record.pointer) ∧
    (∀ r ∈ (Node.record record.slots).slotRegions store record.source, keep r) ∧
    ∀ b ∈ slotsBlocks store record.pointer 0 (record.slots.take record.next), keep b

theorem CopyFrames.current {shape : TreeShape} {heap : Heap} {store : Store Unit}
    {current : CopyRecord} {parents : List CopyRecord}
    (h : CopyFrames shape heap store current parents) :
    current.Holds shape heap store ((parents.head?.map CopyRecord.pointer).getD 0) := by
  cases parents with
  | nil => exact h
  | cons parent parents => exact h.1

theorem CopyFrames.stepKeeping {shape : TreeShape} {heap heap' : Heap}
    {store store' : Store Unit} {current : CopyRecord} {parents : List CopyRecord}
    {keep : Nat × Nat → Prop} {fresh : List (Nat × Nat)}
    (h : CopyFrames shape heap store current parents)
    (hStep : Step heap store keep heap' store' fresh)
    (hKeep : ∀ record ∈ current :: parents, record.Kept keep store) :
    CopyFrames shape heap' store' current parents ∧
      copyBlocks store' current parents = copyBlocks store current parents ∧
      ∀ b ∈ copyBlocks store current parents, ∀ f ∈ fresh, regionsDisjoint b f := by
  induction parents generalizing current with
  | nil =>
    obtain ⟨hRaw, hSource, hChildren⟩ := hKeep current (by simp)
    obtain ⟨hCurrent, hBlocks, hApart⟩ :=
      CopyRecord.Holds.stepKeeping h hStep hRaw hSource hChildren
    simpa only [CopyFrames, copyBlocks, List.flatMap_nil, List.append_nil] using
      And.intro hCurrent (And.intro hBlocks hApart)
  | cons parent parents ih =>
    obtain ⟨hRaw, hSource, hChildren⟩ := hKeep current (by simp)
    obtain ⟨hCurrent, hCurrentBlocks, hCurrentApart⟩ :=
      CopyRecord.Holds.stepKeeping h.1 hStep hRaw hSource hChildren
    obtain ⟨hParents, hParentBlocks, hParentApart⟩ := ih h.2
      (fun record hr => hKeep record (List.mem_cons_of_mem current hr))
    refine ⟨⟨hCurrent, hParents⟩, ?_, ?_⟩
    · change current.blocks store' ++ copyBlocks store' parent parents =
        current.blocks store ++ copyBlocks store parent parents
      rw [hCurrentBlocks, hParentBlocks]
    · intro b hb
      change b ∈ current.blocks store ++ copyBlocks store parent parents at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hCurrentApart b hb
      · exact hParentApart b hb

theorem CopyFrames.step {shape : TreeShape} {heap heap' : Heap}
    {store store' : Store Unit} {current : CopyRecord} {parents : List CopyRecord}
    {fresh : List (Nat × Nat)} (h : CopyFrames shape heap store current parents)
    (hStep : Step heap store (fun _ => True) heap' store' fresh) :
    CopyFrames shape heap' store' current parents ∧
      copyBlocks store' current parents = copyBlocks store current parents ∧
      ∀ b ∈ copyBlocks store current parents, ∀ f ∈ fresh, regionsDisjoint b f :=
  h.stepKeeping hStep (fun _ _ => ⟨trivial, fun _ _ => trivial, fun _ _ => trivial⟩)

theorem CopyFrames.replaceCurrent {shape : TreeShape} {heap heap' : Heap}
    {store store' : Store Unit} {current current' : CopyRecord} {parents : List CopyRecord}
    {keep : Nat × Nat → Prop} {fresh : List (Nat × Nat)}
    (h : CopyFrames shape heap store current parents)
    (hStep : Step heap store keep heap' store' fresh)
    (hKeep : ∀ record ∈ parents, record.Kept keep store)
    (hCurrent : current'.Holds shape heap' store'
      ((parents.head?.map CopyRecord.pointer).getD 0)) :
    CopyFrames shape heap' store' current' parents := by
  cases parents with
  | nil => exact hCurrent
  | cons parent parents => exact ⟨hCurrent, (h.2.stepKeeping hStep hKeep).1⟩

#print axioms CopyFrames.stepKeeping
#print axioms CopyFrames.replaceCurrent

end Verified
