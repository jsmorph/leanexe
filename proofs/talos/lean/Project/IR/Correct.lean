import Project.IR.Function
import Project.Pipeline.Implements

namespace Project.IR

open Wasm Project.ProofKit.ScalarTransition Project.Pipeline

/-- A compiled function implements `f` when its expression evaluates to `f x`
from the arguments of every `x`.  The function writes only locals, so the store,
the heap, and the arguments are unchanged. -/
theorem Func.implements [Scalar α] (func : Func) (name : String) (f : α → UInt64)
    (arity : ∀ x : α, (Scalar.values x).length = func.params)
    (evaluates : ∀ x : α, ∃ next,
      func.result.eval func.params (func.state (Scalar.values x)) = some (f x, next)) :
    Implements (compile func name) 0 f (fun _ => 0) := by
  intro env store heap params x hHeap hArgs _
  change params = Scalar.values x at hArgs
  subst hArgs
  obtain ⟨next, hEval⟩ := evaluates x
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
  rw [hLocals, show func.function.body = func.result.program func.params ++ [] by
    simp [Func.function]]
  refine Expr.program_spec func.result func.params _ next (f x) [] _ env store [] _ hEval ?_
  rw [wp_nil]
  have hDrop : (Scalar.values x).reverse.drop func.function.numParams = [] := by
    simp [Func.function, Func.type, Function.numParams, arity]
  simp only [hDrop, List.append_nil]
  exact ⟨heap, hHeap, rfl, rfl, by omega, le_max_left _ _⟩

end Project.IR
