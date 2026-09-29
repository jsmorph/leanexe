import Project.IR.Function
import Project.Pipeline.Implements

namespace Project.IR

open Wasm Project.ProofKit.ScalarTransition Project.Pipeline

/-- A compiled function implements `f` when, for every `x`, its body runs from
the arguments of `x` without changing the store and ends in a state where the
result expression evaluates to `f x`. -/
theorem Func.implements [Scalar α] (func : Func) (name : String) (f : α → UInt64)
    (arity : ∀ x : α, (Scalar.values x).length = func.params)
    (correct : ∀ (x : α) (initial : Store Unit), Triple func.body func.scratch
      (fun store state => store = initial ∧ state = func.state (Scalar.values x))
      (fun store state => store = initial ∧
        ∃ next, func.result.eval func.scratch state = some (f x, next))) :
    Implements (compile func name) 0 f (fun _ => 0) := by
  intro env store heap params x hHeap hArgs _
  change params = Scalar.values x at hArgs
  subst hArgs
  have hArgsBack :
      ((Scalar.values x).reverse.take func.params).reverse = Scalar.values x := by
    rw [List.take_of_length_le (by simp [arity])]
    simp
  apply TerminatesWith.of_wp_entry_for (f := func.function) rfl
  have hLocals :
      func.function.toLocals
          ((Scalar.values x).reverse.take func.function.numParams).reverse =
        (func.state (Scalar.values x)).toLocals [] := by
    simp [Function.toLocals, Func.function, Func.type, Function.numParams, Func.state,
      hArgsBack, List.map_replicate, ValueType.zero]
  rw [hLocals, show func.function.body =
    func.body.program func.scratch ++ (func.result.program func.scratch ++ []) by
      simp [Func.function]]
  refine correct x store _ env store _ [] _ _ ⟨rfl, rfl⟩ ?_
  rintro store' state ⟨rfl, next, hEval⟩
  refine Expr.program_spec func.result func.scratch _ next (f x) [] _ env store' [] _ hEval ?_
  rw [wp_nil]
  have hDrop : (Scalar.values x).reverse.drop func.function.numParams = [] := by
    simp [Func.function, Func.type, Function.numParams, arity]
  simp only [hDrop, List.append_nil]
  exact ⟨heap, hHeap, rfl, rfl, by omega, le_max_left _ _⟩

end Project.IR
