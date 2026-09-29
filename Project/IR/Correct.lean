import Project.IR.Function
import Project.Pipeline.Implements

namespace Project.IR

open Wasm Project.Pipeline

/-- A compiled function implements `f` with allocation bound `need` when, for
every `x`, every argument list that represents it, and every heap with room for
`need x` bytes, its body ends in a store where some heap satisfies the allocator
invariant, the arguments are still represented, `top` and the page count stay
within the bound, and the result expression evaluates to `f x`. -/
theorem Func.implements_heap [Represent α] (func : Func) (name : String) (f : α → UInt64)
    (need : α → Nat)
    (arity : ∀ heap store params (x : α), Represent.borrowed heap store params x →
      params.length = func.params)
    (correct : ∀ (x : α) (heap : Heap) (initial : Store Unit) (params : List Value),
      heap.At initial → Represent.borrowed heap initial params x →
      heap.Room initial (compile func name) (need x) →
      Triple (compile func name) func.body func.scratch
        (fun store state => store = initial ∧ state = func.state params)
        (fun store state => ∃ heap' : Heap, heap'.At store ∧
          Represent.borrowed heap' store params x ∧ heap'.top.toNat ≤ heap.top.toNat + need x ∧
          store.mem.pages ≤ max initial.mem.pages ((heap.top.toNat + need x + 65535) / 65536) ∧
          ∃ next, func.result.eval func.scratch state = some (f x, next))) :
    Implements (compile func name) 0 f need := by
  intro env store heap params x hHeap hArgs hRoom
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
  refine correct x heap store params hHeap hArgs hRoom env store _ [] _ _ ⟨rfl, rfl⟩ ?_
  rintro store' state ⟨heap', hHeap', hArgs', hTop, hPages, next, hEval⟩
  refine Expr.program_spec func.result func.scratch _ next (f x) [] _ env store' [] _ hEval ?_
  rw [wp_nil]
  have hDrop : params.reverse.drop func.function.numParams = [] := by
    simp [Func.function, Func.type, Function.numParams, hLength]
  simp only [hDrop, List.append_nil]
  exact ⟨heap', hHeap', rfl, hArgs', hTop, hPages⟩

/-- A compiled function whose body keeps the store implements `f` without
allocating. -/
theorem Func.implements [Represent α] (func : Func) (name : String) (f : α → UInt64)
    (arity : ∀ heap store params (x : α), Represent.borrowed heap store params x →
      params.length = func.params)
    (correct : ∀ (x : α) (heap : Heap) (initial : Store Unit) (params : List Value),
      heap.At initial → Represent.borrowed heap initial params x →
      Triple (compile func name) func.body func.scratch
        (fun store state => store = initial ∧ state = func.state params)
        (fun store state => store = initial ∧
          ∃ next, func.result.eval func.scratch state = some (f x, next))) :
    Implements (compile func name) 0 f (fun _ => 0) :=
  Func.implements_heap func name f (fun _ => 0) arity fun x heap initial params hHeap hArgs _ =>
    (correct x heap initial params hHeap hArgs).mono (fun _ _ h => h)
      fun _ _ ⟨hStore, hResult⟩ => by
        subst hStore
        exact ⟨heap, hHeap, hArgs, by omega, le_max_left _ _, hResult⟩

end Project.IR
