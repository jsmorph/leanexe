import Verified.TreeCopyStep
import Verified.TreeInitialize

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem CopyRecord.Holds.beginRecord {shape : TreeShape} {heap0 heap : Heap}
    {initial store : Store Unit} {p source parent : UInt64}
    {slots : List LeanExe.Pipeline.Slot}
    (hLayout : NodeLayout shape (.record slots))
    (hSource : NodeBorrowed heap0 initial source (.record slots))
    (hStep : Step heap0 initial (fun _ => True) heap store [block store p])
    (hRaw : RecordStorage shape heap store p) :
    let store' := beginRecordStore store p source parent
    CopyRecord.Holds shape heap store' parent ⟨source, p, slots, 0⟩ ∧
      Step heap0 initial (fun _ => True) heap store' [block store' p] := by
  obtain ⟨hWrites, hAt, hStorage, hCapacity, hParent, hInput, hIndex⟩ :=
    hRaw.beginRecord hStep.at_ (source := source) (parent := parent)
  have hBase := hRaw.base
  have hWrite : Step heap store (fun r => regionsDisjoint r (block store p)) heap
      (beginRecordStore store p source parent) [] :=
    Step.ofWritesRange hAt hWrites (by simp only [block]; omega)
      (by simp only [block]; omega)
  have hAll := hStep.writeFresh hWrite (by simp)
  have hBorrowed := (hAll.nodeBorrowed hSource hLayout.slotted).1
  refine ⟨⟨hLayout, by simp, hStorage, hBorrowed, hParent, hInput, hIndex,
    by simp [SlotsOwned]⟩, ?_⟩
  simpa only [block_eq hCapacity] using hAll

#print axioms CopyRecord.Holds.beginRecord

end Verified
