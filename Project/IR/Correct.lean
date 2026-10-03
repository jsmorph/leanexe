import Project.IR.Function
import Project.Pipeline.Implements

namespace Project.IR

open Wasm Project.Pipeline

/-- A body's triple gives `ReturnsOrAborts` with any postcondition on the final store and the
results. -/
theorem Func.returns (funcs : List (Func × String)) (i : Nat) (func : Func) (name : String)
    (hFunc : funcs[i]? = some (func, name)) {initial : Store Unit} {params : List Value}
    {P : Store Unit → List Value → Prop}
    (hLength : params.length = func.params.length)
    (correct : Triple (compile funcs) func.body func.scratch
        (fun store state => store = initial ∧ state = func.state params)
        (fun store state => ∃ out next,
          Expr.evalResults store.mem func.scratch func.results state = some (out, next) ∧
            P store out))
    (env : HostEnv Unit) :
    ReturnsOrAborts env (compile funcs) (2 + i) initial params.reverse
      (fun final values => P final values.reverse) := by
  have hArgsBack : (params.reverse.take func.params.length).reverse = params := by
    rw [List.take_of_length_le (by simp [hLength])]
    simp
  have hNoImports : (compile funcs).imports = [] := rfl
  apply ReturnsOrAborts.of_wp_entry_for (f := func.function (2 + i))
    (by rw [hNoImports, List.length_nil, Nat.sub_zero]; exact compile_funcs hFunc)
  have hLocals :
      (func.function (2 + i)).toLocals
          (params.reverse.take (func.function (2 + i)).numParams).reverse =
        (func.state params).toLocals [] := by
    simp [Function.toLocals, Func.function, Func.type, Function.numParams, Func.state,
      hArgsBack]
  rw [hLocals, show (func.function (2 + i)).body =
    func.body.program func.scratch ++ (func.results.flatMap (·.2.program func.scratch) ++ []) by
      simp [Func.function]]
  refine correct env initial _ [] _ _ ?_ ⟨rfl, rfl⟩ ?_
  · exact fun _ => rfl
  rintro store' state ⟨out, next, hEval, hP⟩
  refine Expr.evalResults_program_spec (out := []) hEval ?_
  rw [wp_nil]
  have hDrop : params.reverse.drop (func.function (2 + i)).numParams = [] := by
    simp [Func.function, Func.type, Function.numParams, hLength]
  have hTake : (out.reverse ++ []).take (func.function (2 + i)).results.length =
      out.reverse := by
    simp [Func.function, Func.type, Expr.evalResults_length hEval]
  simp only [State.toLocals, hDrop, List.append_nil]
  rw [List.append_nil] at hTake
  rw [hTake, List.reverse_reverse]
  exact hP

/-- A compiled function implements `f` when, for every `x`, every argument list that
represents it with separate consumed blocks, and every memory whose cap is at most 65,535
pages, its body aborts or ends in a store where some heap satisfies the allocator
invariant, the memory's maximum size is unchanged, the result expressions evaluate to values
that represent `f x` as an owned value, and every region of the heap apart from the consumed
blocks keeps its bytes, stays a region, and lies apart from the result. -/
theorem Func.implements_moves [Represent α] [Represent β] (funcs : List (Func × String))
    (i : Nat) (func : Func) (name : String) (hFunc : funcs[i]? = some (func, name))
    (f : α → β)
    (arity : ∀ heap store params (x : α), Represent.borrowed heap store params x →
      params.length = func.params.length)
    (correct : ∀ (x : α) (heap : Heap) (initial : Store Unit) (params : List Value),
      heap.At initial → Represent.borrowed heap initial params x →
      Separate initial (Represent.moves initial params x) (Represent.reads params x) →
      initial.memoryCap (compile funcs) 0 ≤ 65535 →
      Triple (compile funcs) func.body func.scratch
        (fun store state => store = initial ∧ state = func.state params)
        (fun store state => ∃ heap' : Heap, heap'.At store ∧
          store.memoryCaps = initial.memoryCaps ∧
          ∃ values next,
            Expr.evalResults store.mem func.scratch func.results state = some (values, next) ∧
            Represent.owned heap' store values (f x) ∧
            heap.Keeps initial ((Represent.moves initial params x).map (block initial)) heap'
              store (Represent.blocks store values (f x)))) :
    Implements (compile funcs) (2 + i) f := by
  intro env store heap params x hHeap hArgs hSeparate hCap
  let moves := Represent.moves store params x
  exact Func.returns funcs i func name hFunc (arity heap store params x hArgs)
    (P := fun final out => ∃ heap' : Heap, heap'.At final ∧ Represent.owned heap' final out (f x) ∧
      final.memoryCaps = store.memoryCaps ∧
      ∀ r, heap.Region r → 0 < r.2 → Apart store moves r →
        (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
          heap'.Region r ∧ Represent.outside final out (f x) r)
    ((correct x heap store params hHeap hArgs hSeparate hCap).mono (fun _ _ h => h)
      fun _ _ ⟨heap', hAt, hCaps, values, next, hEval, hResult, hKeeps⟩ =>
        ⟨values, next, hEval, heap', hAt, hResult, hCaps, Heap.Keeps.implements.mp hKeeps⟩) env

/-- `Func.implements_moves` for a function that consumes no argument. -/
theorem Func.implements_heap [Represent α] [Represent β] (funcs : List (Func × String))
    (i : Nat) (func : Func) (name : String) (hFunc : funcs[i]? = some (func, name))
    (f : α → β)
    (arity : ∀ heap store params (x : α), Represent.borrowed heap store params x →
      params.length = func.params.length)
    (correct : ∀ (x : α) (heap : Heap) (initial : Store Unit) (params : List Value),
      heap.At initial → Represent.borrowed heap initial params x →
      initial.memoryCap (compile funcs) 0 ≤ 65535 →
      Triple (compile funcs) func.body func.scratch
        (fun store state => store = initial ∧ state = func.state params)
        (fun store state => ∃ heap' : Heap, heap'.At store ∧ store.memoryCaps = initial.memoryCaps ∧
          ∃ values next,
            Expr.evalResults store.mem func.scratch func.results state = some (values, next) ∧
            Represent.owned heap' store values (f x) ∧
            heap.Keeps initial [] heap' store (Represent.blocks store values (f x)))) :
    Implements (compile funcs) (2 + i) f :=
  Func.implements_moves funcs i func name hFunc f arity
    fun x heap initial params hHeap hArgs _ hCap =>
    (correct x heap initial params hHeap hArgs hCap).mono (fun _ _ h => h)
      fun _ _ ⟨heap', hAt, hCaps, values, next, hEval, hOwned, hKeeps⟩ =>
        ⟨heap', hAt, hCaps, values, next, hEval, hOwned,
          hKeeps.mono (fun _ hb => nomatch hb) fun _ hb => hb⟩

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
    Implements (compile funcs) (2 + i) f :=
  Func.implements_moves funcs i func name hFunc f arity
    fun x heap initial params hHeap hArgs _ _ =>
    (correct x heap initial params hHeap hArgs).mono (fun _ _ h => h)
      fun _ _ ⟨hStore, hResult⟩ => by
        subst hStore
        obtain ⟨values, next, hEval, hValues⟩ := hResult
        exact ⟨heap, hHeap, rfl, values, next, hEval, hValues,
          fun _ hr _ _ => ⟨fun _ _ _ => rfl, hr, Represent.outside_scalar⟩⟩

/-- A compiled function of scalars whose body keeps the store, for every store,
computes `f` and keeps the store. -/
theorem Func.implementsPure [Scalar α] [Scalar β] (funcs : List (Func × String)) (i : Nat)
    (func : Func) (name : String) (hFunc : funcs[i]? = some (func, name)) (f : α → β)
    (arity : ∀ x : α, (Scalar.values x).length = func.params.length)
    (correct : ∀ (x : α) (initial : Store Unit),
      Triple (compile funcs) func.body func.scratch
        (fun store state => store = initial ∧ state = func.state (Scalar.values x))
        (fun store state => store = initial ∧ ∃ values next,
          Expr.evalResults store.mem func.scratch func.results state = some (values, next) ∧
          values = Scalar.values (f x))) :
    ImplementsPure (compile funcs) (2 + i) f := by
  intro env store x
  have hLength := arity x
  have hArgsBack : ((Scalar.values x).reverse.take func.params.length).reverse =
      Scalar.values x := by
    rw [List.take_of_length_le (by simp [hLength])]
    simp
  have hNoImports : (compile funcs).imports = [] := rfl
  apply ReturnsOrAborts.of_wp_entry_for (f := func.function (2 + i))
    (by rw [hNoImports, List.length_nil, Nat.sub_zero]; exact compile_funcs hFunc)
  have hLocals :
      (func.function (2 + i)).toLocals
          ((Scalar.values x).reverse.take (func.function (2 + i)).numParams).reverse =
        (func.state (Scalar.values x)).toLocals [] := by
    simp [Function.toLocals, Func.function, Func.type, Function.numParams, Func.state,
      hArgsBack]
  rw [hLocals, show (func.function (2 + i)).body =
    func.body.program func.scratch ++ (func.results.flatMap (·.2.program func.scratch) ++ []) by
      simp [Func.function]]
  refine correct x store env store _ [] _ _ ?_ ⟨rfl, rfl⟩ ?_
  · exact fun _ => rfl
  rintro store' state ⟨hStore, values, next, hEval, hResult⟩
  refine Expr.evalResults_program_spec (out := []) hEval ?_
  rw [wp_nil]
  have hDrop : (Scalar.values x).reverse.drop (func.function (2 + i)).numParams = [] := by
    simp [Func.function, Func.type, Function.numParams, hLength]
  have hTake : (values.reverse ++ []).take (func.function (2 + i)).results.length =
      values.reverse := by
    simp [Func.function, Func.type, Expr.evalResults_length hEval]
  simp only [State.toLocals, hDrop, List.append_nil]
  rw [List.append_nil] at hTake
  rw [hTake, List.reverse_reverse]
  exact ⟨hStore, hResult⟩

end Project.IR
