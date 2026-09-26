import Project.Beck.ExecutionInputPrepare

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

structure InputResult (frame : Locals) (input : Input) (owner pointer : UInt64) : Prop where
  values : frame.values = []
  status : frame.get 46 = some (.i64 input.status)
  jobs : frame.get 47 = some (.i64 input.jobs.toUInt64)
  categories : frame.get 48 = some (.i64 input.categories.toUInt64)
  overlap : frame.get 49 = some (.i64 input.overlap.toUInt64)
  owner : frame.get 50 = some (.i64 owner)
  pointer : frame.get 51 = some (.i64 pointer)

def inputReadySaved (saved : InputSaved) (wordsPointer owner pointer : UInt64) (jobs categories : Nat) : InputSaved :=
  inputEmptySaved (inputEmptySaved (inputPreparedSaved saved wordsPointer jobs categories) 25 owner) 26 pointer

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem inputJobs_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (wordsPointer rowOwner : UInt64) (node : FreeNode) (saved : InputSaved) (tail : InputTail)
    (count categories : Nat) (out : ParseState) (words : Array UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (owned : heap.OwnsWords initial node #[])
    (wordsAt : UInt64Array.At initial wordsPointer words)
    (wordsProtected : heap.Protects wordsPointer.toNat (wordsPointer.toNat + 8 * (words.size + 1)))
    (different : node.root ≠ wordsPointer) (nonzero : wordsPointer ≠ 0)
    (countBound : count ≤ 6) (categoryBound : categories ≤ 8) (lengthBound : 2 ≤ words.size)
    (accepted : readJobs count words categories ⟨2, 0, #[]⟩ = some out) (terminal : out.position = words.size)
    (budget : OutputBudget initial heap (1520 * count + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap finalNode,
      finalHeap.At final → finalHeap.OwnsWords final finalNode out.incidence → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ frame, InputResult frame ⟨0, count, categories, out.overlap, out.incidence⟩
        (if count = 0 then rowOwner else finalNode.root) finalNode.root → Q (.Fallthrough final frame)) :
    wp Project.Beck.«module» (inputEligible.drop 120) Q initial
      (inputFrame wordsPointer (inputReadySaved saved wordsPointer rowOwner node.root count categories) tail) env := by
  have incidenceBound : 0 + count * categories ≤ 48 := by
    have := Nat.mul_le_mul countBound categoryBound
    simpa using this
  have call := readJobs_exact (rowOwner := rowOwner) env initial heap count categories wordsPointer node
    ⟨2, 0, #[]⟩ out words remaining pageLimit valid owned wordsAt wordsProtected different nonzero
    countBound categoryBound lengthBound (by decide) incidenceBound accepted budget
  simp only [inputEligible, inputInBounds, func6, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, inputFrame, inputPrefix, inputReadySaved, inputEmptySaved, inputPreparedSaved,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceAdd, or_false, false_or, reduceIte, List.cons_append, List.nil_append]
  wp_fixed_frame
  apply wp_call_tw call
  rintro final values ⟨finalHeap, finalNode, rfl, finalValid, finalOwned, preserved, finalBudget⟩
  have finalWords := preserved.words wordsProtected wordsAt
  have headerBound : wordsPointer.toUInt32.toNat + 8 ≤ final.mem.pages * 65536 := by
    rw [finalWords.pointerAddress_toNat]
    have := finalWords.2.1
    omega
  have positionEq : out.position.toUInt64 = UInt64.ofNat words.size := by rw [terminal]
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_fixed_frame
  rw [show 2 ^ 32 = 4294967296 by decide, ← Memory.toUInt32_eq_ofNat]
  simp only [UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero, Nat.not_lt.mpr headerBound, reduceIte, finalWords.lengthRead]
  repeat' ((try wp_fixed_frame [positionEq, List.take, List.drop, List.append_nil]) <;>
    (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  wp_fixed_frame [positionEq, List.take, List.drop, List.append_nil]
  apply next final finalHeap finalNode finalValid finalOwned preserved finalBudget
  constructor <;> rfl

#print axioms inputJobs_exact

end Project.Beck.Execution
