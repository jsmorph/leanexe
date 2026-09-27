import Project.Beck.ExecutionWordLocals
import Project.ProofKit.FixedArraySearchWindow

namespace Project.Beck.Execution

open Wasm Project.ProofKit

theorem WordLocals.searchFrame {saved tail : List Value} (savedWords : WordLocals saved) (tailWords : WordLocals tail)
    (params : List Value) (need previous current capacity afterNode result : UInt64) :
    WordLocals (FixedArraySearch.frame params saved tail need previous current capacity afterNode result).locals :=
  savedWords.append ((((((tailWords.cons result).cons afterNode).cons capacity).cons current).cons previous).cons need)

theorem WordLocals.allocationFrame {locals : List Value} (typed : WordLocals locals) (params : List Value)
    (offset : Nat) (bound : offset + 6 ≤ locals.length) :
    ∃ need previous current capacity afterNode result : UInt64,
      ({ params := params, locals := locals } : Locals) = FixedArraySearch.frame params (locals.take offset)
        (locals.drop (offset + 6)) need previous current capacity afterNode result := by
  obtain ⟨need, read0⟩ := typed.read offset (by omega)
  obtain ⟨previous, read1⟩ := typed.read (offset + 1) (by omega)
  obtain ⟨current, read2⟩ := typed.read (offset + 2) (by omega)
  obtain ⟨capacity, read3⟩ := typed.read (offset + 3) (by omega)
  obtain ⟨afterNode, read4⟩ := typed.read (offset + 4) (by omega)
  obtain ⟨result, read5⟩ := typed.read (offset + 5) (by omega)
  refine ⟨need, previous, current, capacity, afterNode, result,
    FixedArraySearch.frame_eq_of_gets { params := params, locals := locals } offset need previous current capacity afterNode result bound rfl ?_⟩
  intro i hi
  simp only [Locals.get, show ¬params.length + offset + i < params.length by omega,
    show params.length + offset + i < params.length + locals.length by omega, reduceIte,
    show params.length + offset + i - params.length = offset + i by omega]
  interval_cases i <;> simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ,
    read0, read1, read2, read3, read4, read5]

end Project.Beck.Execution
