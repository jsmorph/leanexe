import Project.Beck.ExecutionInputJobs

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem inputEligible_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (pointer : UInt64) (saved : InputSaved) (tail : InputTail) (words : Array UInt64) (out : ParseState)
    (remaining pageLimit : Nat) (valid : heap.At initial)
    (wordsAt : UInt64Array.At initial pointer words)
    (wordsProtected : heap.Protects pointer.toNat (pointer.toNat + 8 * (words.size + 1)))
    (nonzero : pointer ≠ 0) (lengthBound : 2 ≤ words.size)
    (countBound : words[0]!.toNat ≤ 6) (categoryBound : words[1]!.toNat ≤ 8)
    (accepted : readJobs words[0]!.toNat words words[1]!.toNat ⟨2, 0, #[]⟩ = some out)
    (terminal : out.position = words.size)
    (budget : OutputBudget initial heap (112 + 1520 * words[0]!.toNat + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap node owner,
      finalHeap.At final → finalHeap.OwnsWords final node out.incidence → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ frame, InputResult frame ⟨0, words[0]!.toNat, words[1]!.toNat, out.overlap, out.incidence⟩ owner node.root →
        Q (.Fallthrough final frame)) :
    wp Project.Beck.«module» inputEligible Q initial (inputFrame pointer saved tail) env := by
  rw [← List.take_append_drop 34 inputEligible]
  apply inputPrepare_exact env initial pointer saved tail words wordsAt lengthBound
  change wp Project.Beck.«module» ((inputEligible.drop 34).take 43 ++ inputEligible.drop 77) Q initial _ env
  rw [input_empty_shapes.1]
  apply inputEmpty_exact env initial heap pointer _ _ 25 (Or.inl rfl) (56 + 1520 * words[0]!.toNat + remaining) pageLimit valid
    (by simpa only [← Nat.add_assoc, Nat.reduceAdd] using budget)
  dsimp only
  intro firstValid firstOwned firstFrame firstBudget a b c d
  change wp Project.Beck.«module» ((inputEligible.drop 77).take 43 ++ inputEligible.drop 120) Q (emptyWords heap initial) _ env
  rw [input_empty_shapes.2]
  apply inputEmpty_exact env (emptyWords heap initial) (heap.allocate 8) pointer _ _ 26 (Or.inr rfl)
    (1520 * words[0]!.toNat + remaining) pageLimit firstValid
    (by simpa only [Nat.add_assoc] using firstBudget)
  dsimp only
  intro secondValid secondOwned secondFrame secondBudget e f g h
  have preserved := firstFrame.trans secondFrame
  have fresh := allocated_fresh heap (heap.allocate 8) initial (emptyWords heap initial) firstFrame 8
    (fun h => ((firstBudget.bump 8 (by change 56 ≤ 56 + 1520 * words[0]!.toNat + remaining; omega)) h).1.le)
  have different := fresh.pointer_ne pointer words.size wordsProtected (by have := secondOwned.buffer.capacity; omega)
    secondOwned.buffer.rootBound
  apply inputJobs_exact env _ ((heap.allocate 8).allocate 8) pointer (allocatedNode heap.top 8 heap.nodes).root
    (allocatedNode (heap.allocate 8).top 8 (heap.allocate 8).nodes) saved _ words[0]!.toNat words[1]!.toNat out words remaining pageLimit
    secondValid secondOwned (preserved.words wordsProtected wordsAt) (preserved.protects _ _ wordsProtected)
    different nonzero countBound categoryBound lengthBound accepted terminal secondBudget
  intro final finalHeap node finalValid finalOwned finalFrame finalBudget frame result
  exact next final finalHeap node _ finalValid finalOwned (preserved.trans finalFrame) finalBudget frame result

#print axioms inputEligible_exact

end Project.Beck.Execution
