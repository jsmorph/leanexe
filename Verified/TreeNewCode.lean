import Verified.TreeAllocate
import Verified.TreeBeginCode
import Verified.TreeBeginState

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_treeCopyNew {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {shape : TreeShape} {heap : Heap} {store : Store Unit} {s : Locals} {dst input : Nat}
    {parent : Option Nat} {source parentValue : UInt64} {slots : List LeanExe.Pipeline.Slot}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * slots.length)))) Q)
    (hLayout : NodeLayout shape (.record slots)) (hSource : NodeBorrowed heap store source (.record slots))
    (hInput : s.get input = some (.i64 source))
    (hParent : parent.elim (parentValue = 0) (fun pos => s.get pos = some (.i64 parentValue)))
    (hInputNe : input ≠ dst) (hParentNe : ∀ pos, parent = some pos → pos ≠ dst)
    (hLow : s.params.length ≤ dst) (hHigh : dst < s.params.length + s.locals.length)
    (hNext : ∀ heap' store' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      CopyRecord.Holds shape heap' store' parentValue ⟨source, ptr, slots, 0⟩ →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * slots.length) →
      wp m rest Q store' (setLocal s dst (.i64 ptr)) host) :
    wp m (treeCopyAllocate shape input dst ++ treeCopyBegin shape input dst [.localGet input]
      (parent.elim [.constI64 0] (fun pos => [.localGet pos])) ++ rest)
      Q store s host := by
  obtain ⟨r, hLength, -, hPrefix, -⟩ := id hLayout
  have hSlotted : slots ≠ [] := (NodeLayout.slotted hLayout).1
  obtain ⟨-, hSourceRoom⟩ := NodeBorrowed.tagRoom hSource hAt hSlotted
  rw [List.append_assoc]
  refine wp_treeCopyAllocate hm r hAt hCap (PushesWord.tag hInput hSourceRoom)
    (fun ht => NodeBorrowed.tag hSource hPrefix ht) (by rw [← hLength]; exact hTrap) hLow hHigh ?_
  intro heap' store' ptr hStep hRaw _ hTop
  rw [← hLength] at hRaw hTop
  have hSource' := (hStep.nodeBorrowed hSource hLayout.slotted).1
  obtain ⟨-, hSourceRoom'⟩ := NodeBorrowed.tagRoom hSource' hStep.at_ hSlotted
  obtain ⟨hRecord, hAll⟩ := CopyRecord.Holds.beginRecord hLayout hSource hStep hRaw
    (parent := parentValue)
  have hPtr := Locals.get_setLocal_same (s := s) (v := .i64 ptr) hLow hHigh
  have hInput' : (setLocal s dst (.i64 ptr)).get input = some (.i64 source) := by
    rw [Locals.get_setLocal_ne hLow hInputNe]
    exact hInput
  have hParent' : parent.elim (parentValue = 0)
      (fun pos => (setLocal s dst (.i64 ptr)).get pos = some (.i64 parentValue)) := by
    cases parent with
    | none => exact hParent
    | some pos =>
      change (setLocal s dst (.i64 ptr)).get pos = some (.i64 parentValue)
      rw [Locals.get_setLocal_ne hLow (hParentNe pos rfl)]
      exact hParent
  exact wp_treeCopyBegin (parent := parent) r hRaw hStep.at_ hPtr hInput' hSourceRoom'
    (fun ht => NodeBorrowed.tag hSource' hPrefix ht) hLength.symm hParent'
    (hNext heap' _ ptr hAll hRecord hTop)

#print axioms wp_treeCopyNew

end Verified
