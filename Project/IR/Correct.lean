import Project.IR.Function
import Project.Pipeline.Implements

namespace Project.IR

open Wasm Project.ProofKit.ScalarTransition Project.Pipeline

/-- A compiled function implements `f` when, for every `x` and every argument
list that represents it, its body runs from those arguments without changing the
store and ends in a state where the result expression evaluates to `f x`. -/
theorem Func.implements [Represent α] (func : Func) (name : String) (f : α → UInt64)
    (arity : ∀ heap store params (x : α), Represent.borrowed heap store params x →
      params.length = func.params)
    (correct : ∀ (x : α) (heap : Heap) (initial : Store Unit) (params : List Value),
      heap.At initial → Represent.borrowed heap initial params x →
      Triple func.body func.scratch
        (fun store state => store = initial ∧ state = func.state params)
        (fun store state => store = initial ∧
          ∃ next, func.result.eval func.scratch state = some (f x, next))) :
    Implements (compile func name) 0 f (fun _ => 0) := by
  intro env store heap params x hHeap hArgs _
  have hLength := arity heap store params x hArgs
  have hArgsBack : (params.reverse.take func.params).reverse = params := by
    rw [List.take_of_length_le (by simp [hLength])]
    simp
  apply TerminatesWith.of_wp_entry_for (f := func.function) rfl
  have hLocals :
      func.function.toLocals (params.reverse.take func.function.numParams).reverse =
        (func.state params).toLocals [] := by
    simp [Function.toLocals, Func.function, Func.type, Function.numParams, Func.state,
      hArgsBack, List.map_replicate, ValueType.zero]
  rw [hLocals, show func.function.body =
    func.body.program func.scratch ++ (func.result.program func.scratch ++ []) by
      simp [Func.function]]
  refine correct x heap store params hHeap hArgs _ env store _ [] _ _ ⟨rfl, rfl⟩ ?_
  rintro store' state ⟨rfl, next, hEval⟩
  refine Expr.program_spec func.result func.scratch _ next (f x) [] _ env store' [] _ hEval ?_
  rw [wp_nil]
  have hDrop : params.reverse.drop func.function.numParams = [] := by
    simp [Func.function, Func.type, Function.numParams, hLength]
  simp only [hDrop, List.append_nil]
  exact ⟨heap, hHeap, rfl, hArgs, by omega, le_max_left _ _⟩

end Project.IR
