import Project.Beck.ExecutionCompute
import Project.Beck.Source
import Project.Beck.AnnotationMatches

namespace Project.Beck.Spec

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def CorrectOutput (categories : Nat) (jobs : List (List Nat)) (result : Array UInt64) : Prop :=
  result.size = jobs.length + 2 ∧ result[0]! = 0 ∧ result[1]! = (Source.overlap jobs).toUInt64 ∧
    (∀ job < jobs.length, result[job + 2]! = 0 ∨ result[job + 2]! = 1) ∧
    ∀ category : Fin categories,
      |(((Source.members jobs category.val).filter fun job => result[job.val + 2]! = 1).card : ℤ) -
        ((Source.members jobs category.val).filter fun job => result[job.val + 2]! = 0).card| ≤
        max 0 (2 * (Source.overlap jobs : ℤ) - 1)

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (pointer : UInt64) (words : Array UInt64)
    (remaining pageLimit : Nat), heap.At initial → UInt64Array.At initial pointer words →
    heap.Protects pointer.toNat (pointer.toNat + 8 * (words.size + 1)) →
    (readInput words).status = 0 →
    OutputBudget initial heap (Execution.computeMaxBytes + remaining) pageLimit m →
    TerminatesWith env m 35 initial [.i64 pointer]
      (fun final values => ∃ finalHeap node, finalHeap.At final ∧ finalHeap.OwnsWords final node (compute words) ∧
        heap.Frame initial finalHeap final ∧ Execution.FreshFor heap node ∧
        OutputBudget final finalHeap remaining pageLimit m ∧ values = [.i64 node.root])

def CorrectSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (pointer : UInt64) (words : Array UInt64)
    (categories : Nat) (jobs : List (List Nat)) (remaining pageLimit : Nat),
    Encoding.Input words categories jobs → heap.At initial → UInt64Array.At initial pointer words →
    heap.Protects pointer.toNat (pointer.toNat + 8 * (words.size + 1)) →
    OutputBudget initial heap (Execution.computeMaxBytes + remaining) pageLimit m →
    TerminatesWith env m 35 initial [.i64 pointer]
      (fun final values => ∃ result finalHeap node, result = compute words ∧ CorrectOutput categories jobs result ∧
        finalHeap.At final ∧ finalHeap.OwnsWords final node result ∧
        heap.Frame initial finalHeap final ∧ Execution.FreshFor heap node ∧
        OutputBudget final finalHeap remaining pageLimit m ∧ values = [.i64 node.root])

theorem compute_source_eq : ExactSpecFor Project.Beck.«module» := by
  intro env initial heap pointer words remaining pageLimit valid represented wordsProtected accepted budget
  exact Execution.compute_exact env initial heap pointer words remaining pageLimit valid represented wordsProtected accepted
    (budget.mono (Nat.add_le_add_right
      (Execution.computeBytes_bound _ (Parser.accepted_supported words accepted).capacity) remaining))

theorem compute_correct : CorrectSpecFor Project.Beck.«module» := by
  intro env initial heap pointer words categories jobs remaining pageLimit encoded valid represented wordsProtected budget
  apply (compute_source_eq env initial heap pointer words remaining pageLimit valid represented wordsProtected
    (Encoding.input_complete words categories jobs encoded).1 budget).mono
  rintro final values ⟨finalHeap, node, finalValid, owned, preserved, fresh, finalBudget, result⟩
  exact ⟨compute words, finalHeap, node, rfl, Source.compute_correct words categories jobs encoded,
    finalValid, owned, preserved, fresh, finalBudget, result⟩

#print axioms compute_source_eq
#print axioms compute_correct

end Project.Beck.Spec
