import Project.IR.Function
import Project.Pipeline.Implements

namespace Project.IR

open Wasm Project.Pipeline

/-- A compiled function implements `f` with allocation bound `need` when, for
every `x`, every argument list that represents it, and every heap with room for
`need x` bytes, its body ends in a store where some heap satisfies the allocator
invariant, the arguments are still represented, `top` and the page count stay
within the bound, every array borrowed or owned before is still borrowed or
owned, and the result expressions evaluate to values that represent `f x` as an
owned value. -/
theorem Func.implements_heap [Represent α] [Represent β] (funcs : List (Func × String))
    (i : Nat) (func : Func) (name : String) (hFunc : funcs[i]? = some (func, name))
    (f : α → β) (need : α → Nat)
    (arity : ∀ heap store params (x : α), Represent.borrowed heap store params x →
      params.length = func.params.length)
    (correct : ∀ (x : α) (heap : Heap) (initial : Store Unit) (params : List Value),
      heap.At initial → Represent.borrowed heap initial params x →
      heap.Room initial (compile funcs) (need x) →
      Triple (compile funcs) func.body func.scratch
        (fun store state => store = initial ∧ state = func.state params)
        (fun store state => ∃ heap' : Heap, heap'.At store ∧
          Represent.borrowed heap' store params x ∧ heap'.top.toNat ≤ heap.top.toNat + need x ∧
          store.mem.pages ≤ max initial.mem.pages ((heap.top.toNat + need x + 65535) / 65536) ∧
          (∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed store p ws) ∧
          (∀ p ws, heap.Owned initial p ws → heap'.Owned store p ws) ∧
          ∃ values next,
            Expr.evalResults store.mem func.scratch func.results state = some (values, next) ∧
            Represent.owned heap' store values (f x))) :
    Implements (compile funcs) (3 + i) f need := by
  intro env store heap params x hHeap hArgs hRoom
  have hLength := arity heap store params x hArgs
  have hArgsBack : (params.reverse.take func.params.length).reverse = params := by
    rw [List.take_of_length_le (by simp [hLength])]
    simp
  have hNoImports : (compile funcs).imports = [] := rfl
  apply TerminatesWith.of_wp_entry_for (f := func.function (2 + i))
    (by rw [hNoImports, List.length_nil, Nat.sub_zero]; exact compile_funcs hFunc)
  have hLocals :
      (func.function (2 + i)).toLocals (params.reverse.take (func.function (2 + i)).numParams).reverse =
        (func.state params).toLocals [] := by
    simp [Function.toLocals, Func.function, Func.type, Function.numParams, Func.state,
      hArgsBack]
  rw [hLocals, show (func.function (2 + i)).body =
    func.body.program func.scratch ++ (func.results.flatMap (·.2.program func.scratch) ++ []) by
      simp [Func.function]]
  refine correct x heap store params hHeap hArgs hRoom env store _ [] _ _ ⟨rfl, rfl⟩ ?_
  rintro store' state ⟨heap', hHeap', hArgs', hTop, hPages, hBorrowedKeep, hOwnedKeep, values,
    next, hEval, hResult⟩
  refine Expr.evalResults_program_spec (out := []) hEval ?_
  rw [wp_nil]
  have hDrop : params.reverse.drop (func.function (2 + i)).numParams = [] := by
    simp [Func.function, Func.type, Function.numParams, hLength]
  have hTake : (values.reverse ++ []).take (func.function (2 + i)).results.length =
      values.reverse := by
    simp [Func.function, Func.type, Expr.evalResults_length hEval]
  simp only [State.toLocals, hDrop, List.append_nil]
  rw [List.append_nil] at hTake
  rw [hTake, List.reverse_reverse]
  exact ⟨heap', hHeap', hResult, hArgs', hTop, hPages, hBorrowedKeep, hOwnedKeep⟩

/-- A compiled function whose body keeps the store implements `f` without
allocating. -/
theorem Func.implements [Represent α] [Scalar β] (funcs : List (Func × String)) (i : Nat)
    (func : Func) (name : String) (hFunc : funcs[i]? = some (func, name)) (f : α → β)
    (arity : ∀ heap store params (x : α), Represent.borrowed heap store params x →
      params.length = func.params.length)
    (correct : ∀ (x : α) (heap : Heap) (initial : Store Unit) (params : List Value),
      heap.At initial → Represent.borrowed heap initial params x →
      Triple (compile funcs) func.body func.scratch
        (fun store state => store = initial ∧ state = func.state params)
        (fun store state => store = initial ∧
          ∃ values next,
            Expr.evalResults store.mem func.scratch func.results state = some (values, next) ∧
            values = Scalar.values (f x))) :
    Implements (compile funcs) (3 + i) f (fun _ => 0) :=
  Func.implements_heap funcs i func name hFunc f (fun _ => 0) arity
    fun x heap initial params hHeap hArgs _ =>
    (correct x heap initial params hHeap hArgs).mono (fun _ _ h => h)
      fun _ _ ⟨hStore, hResult⟩ => by
        subst hStore
        exact ⟨heap, hHeap, hArgs, by omega, le_max_left _ _, fun _ _ h => h, fun _ _ h => h,
          hResult⟩

end Project.IR
