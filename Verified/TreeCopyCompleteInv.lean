import Verified.TreeCopyInvariant

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def CopyParentFrames (shape : TreeShape) (heap : Heap) (store : Store Unit) :
    List CopyRecord → Prop
  | [] => True
  | parent :: parents => CopyFrames shape heap store parent parents

structure CopyCompleted (shape : TreeShape) (heap0 : Heap) (initial : Store Unit)
    (root : List LeanExe.Pipeline.Slot) (result : UInt64) (limit : Nat)
    (heap : Heap) (store : Store Unit) (current : CopyRecord) (parents : List CopyRecord) : Prop
    extends CopyProgress shape heap0 initial root result limit heap store current parents where
  done : current.next = current.slots.length
  owned : NodeOwned heap store current.pointer (.record current.slots)
  parents : CopyParentFrames shape heap store parents

theorem CopyRecord.blocks_done (store : Store Unit) (current : CopyRecord)
    (h : current.next = current.slots.length) :
    current.blocks store = Node.blocks store current.pointer (.record current.slots) := by
  simp only [CopyRecord.blocks, h, List.take_length, Node.blocks]

end Verified
