import Verified.TreeAdvanceCode
import Verified.TreeCopyAdvanceInv
import Verified.TreeCopyLocals

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_treeCopyAdvanceInv {m : Module} {host : HostEnv Unit} {heap0 heap : Heap}
    {initial store : Store Unit} {shape : TreeShape} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit base : Nat} {current : CopyRecord} {parents : List CopyRecord}
    {s0 s : Locals} {word : UInt64} {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat current.next)))
    (hWord : s.get (base + 4) = some (.i64 word)) (hBound : current.next < current.slots.length)
    (hValue : (current.slots[current.next]).ValueOwned heap store word)
    (hNoBlocks : (current.slots[current.next]).valueBlocks store word = [])
    (hWork : CopyWork.Step (current.work parents)
      ({ current with next := current.next + 1 }.work parents))
    (hAllocates : (current.work parents).allocates = 0)
    (hNext : ∀ store', CopyInv shape heap0 initial root result limit heap store'
      { current with next := current.next + 1 } parents → wp m rest Q store' s host) :
    wp m (treeSlotAddress (base + 1) (base + 2) ++ [.localGet (base + 4), .store64 0] ++
      treeCopyAdvance (base + 1) (base + 2) ++ rest) Q store s host := by
  refine wp_copyRecordAdvance h.frames.current h.step.at_ hBound hValue h.sourceApart h.prefixApart
    (by rw [hNoBlocks]; exact nofun) hLocals.current hIndex hWord ?_
  intro store' hCurrent hWrite hBlocks
  rw [hNoBlocks, List.append_nil] at hBlocks
  exact hNext store' (h.advanceStep hCurrent hWrite hBlocks hWork hAllocates)

#print axioms wp_treeCopyAdvanceInv

end Verified
