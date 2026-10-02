import Project.IR.Correct

/-!
The rules for a definition that calls itself other than in tail position.  The compiler emits
an internal function with a depth parameter, which traps at `unreachable` at the depth limit
and calls itself with the depth plus one, and an entry function, which calls the internal
function at depth 0.  `Func.recursion` proves the internal function by strong induction on a
measure of the argument, with `Stmt.selfCall_spec` for its calls of itself, and
`Func.entry_implements` gives the entry's `Implements`.  The depth needs no bound in the
proof, since `ReturnsOrAborts` allows a trap at `unreachable`.
-/

namespace Project.IR

open Wasm Project.Pipeline

/-- `Func.implementsPure` with any parameter values: a body that keeps the store and leaves
results `out` gives a store-keeping `ReturnsOrAborts`. -/
theorem Func.keeps (funcs : List (Func × String)) (i : Nat) (func : Func) (name : String)
    (hFunc : funcs[i]? = some (func, name)) {initial : Store Unit} {params out : List Value}
    (hLength : params.length = func.params.length)
    (correct : Triple (compile funcs) func.body func.scratch
        (fun store state => store = initial ∧ state = func.state params)
        (fun store state => store = initial ∧ ∃ next,
          Expr.evalResults store.mem func.scratch func.results state = some (out, next)))
    (env : HostEnv Unit) :
    ReturnsOrAborts env (compile funcs) (2 + i) initial params.reverse
      (fun final values => final = initial ∧ values.reverse = out) := by
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
  rintro store' state ⟨hStore, next, hEval⟩
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
  exact ⟨hStore, rfl⟩

/-- The specification of an internal recursive function at `idx`: for any depth word `d`, from a
store with the allocator invariant and arguments `vs` that represent `x` as borrowed, the call
aborts or keeps the store and returns `f x`. -/
def Keeps [Represent α] (m : Module) (idx : Nat) (f : α → UInt64) (x : α) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (vs : List Value) (d : UInt64),
    heap.At store → Represent.borrowed heap store vs x →
    ReturnsOrAborts env m idx store (.i64 d :: vs.reverse)
      (fun final values => final = store ∧ values = [.i64 (f x)])

/-- The recursion rule: a body that keeps the store, proved under the hypothesis that every call
on a smaller argument satisfies `Keeps`, satisfies `Keeps` for every argument. -/
theorem Func.recursion [Represent α] (funcs : List (Func × String)) (i : Nat) (func : Func)
    (name : String) (hFunc : funcs[i]? = some (func, name)) (f : α → UInt64)
    (measure : α → Nat)
    (arity : ∀ heap store vs (x : α), Represent.borrowed heap store vs x →
      vs.length + 1 = func.params.length)
    (hBody : ∀ x, (∀ y, measure y < measure x → Keeps (compile funcs) (2 + i) f y) →
      ∀ heap initial vs (d : UInt64), heap.At initial → Represent.borrowed heap initial vs x →
      Triple (compile funcs) func.body func.scratch
        (fun store state => store = initial ∧ state = func.state (vs ++ [.i64 d]))
        (fun store state => store = initial ∧ ∃ next,
          Expr.evalResults store.mem func.scratch func.results state =
            some ([.i64 (f x)], next))) :
    ∀ x, Keeps (compile funcs) (2 + i) f x := by
  intro x
  induction h : measure x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro env store heap vs d hHeap hArgs
    have hRun := Func.keeps funcs i func name hFunc (params := vs ++ [.i64 d])
      (out := [.i64 (f x)]) (by simp [arity _ _ _ _ hArgs])
      (hBody x (fun y hy => ih _ (h ▸ hy) y rfl) heap store vs d hHeap hArgs) env
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append] at hRun
    refine hRun.mono fun st vs' ⟨hSt, hVs⟩ => ⟨hSt, ?_⟩
    rw [← List.reverse_reverse vs', hVs]
    rfl

/-- A call of the internal function inside its own body: the specification of the callee,
the induction hypothesis for a smaller argument, discharges the precondition of
`Stmt.call_spec`, and the call keeps the store. -/
theorem Stmt.selfCall_spec [Represent α] {m : Module} {idx : Nat} {f : α → UInt64} {g : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some g)
    {scratch : Nat} {args : List ((type : ScalarType) × Expr type)} {result : Nat}
    (hParams : args.length = g.numParams) {initial : Store Unit} {before afterArgs next : State}
    {heap : Heap} {y : α} {vs : List Value} {d : UInt64}
    (hSpec : Keeps m idx f y) (hHeap : heap.At initial)
    (hB : Represent.borrowed heap initial vs y)
    (hArgs : Expr.evalResults initial.mem scratch args before = some (vs ++ [.i64 d], afterArgs))
    (hSet : afterArgs.setAll [result] [.i64 (f y)] = some next) :
    Triple m (.call idx args [result]) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => store = initial ∧ state = next) := by
  refine (Stmt.call_spec hImport hFunc hParams).mono ?_ fun _ _ h => h
  rintro store state ⟨rfl, rfl⟩
  refine ⟨vs ++ [.i64 d], afterArgs,
    fun final values => final = store ∧ values = [.i64 (f y)], hArgs, fun env => ?_, ?_⟩
  · simpa using hSpec env store heap vs d hHeap hB
  · rintro store' out ⟨rfl, rfl⟩
    exact ⟨next, by simpa using hSet, rfl, rfl⟩

/-- The entry of a recursive definition: one call of the internal function at `index`, with
the parameters and depth 0, whose result the entry returns. -/
theorem Func.entry_implements [Represent α] (funcs : List (Func × String)) (i : Nat)
    (func : Func) (name : String) (hFunc : funcs[i]? = some (func, name)) (f : α → UInt64)
    {index : Nat} {g : Wasm.Function} {args : List ((type : ScalarType) × Expr type)}
    (arity : ∀ heap store params (x : α), Represent.borrowed heap store params x →
      params.length = func.params.length)
    (hBody : func.body = .call index args [func.params.length])
    (hResults : func.results = [⟨.u64, .get func.params.length⟩])
    (hImport : (compile funcs).imports[index]? = none)
    (hCallee : (compile funcs).funcs[index - (compile funcs).imports.length]? = some g)
    (hParams : args.length = g.numParams)
    (hArgs : ∀ heap store params (x : α), Represent.borrowed heap store params x →
      Expr.evalResults store.mem func.scratch args (func.state params) =
        some (params ++ [.i64 0], func.state params))
    (hSet : ∀ (params : List Value) (v : UInt64), params.length = func.params.length →
      ∃ next, (func.state params).setAll [func.params.length] [.i64 v] = some next ∧
        next.get func.params.length = some (.i64 v))
    (hSpec : ∀ x, Keeps (compile funcs) index f x) :
    Implements (compile funcs) (2 + i) f := by
  refine Func.implements funcs i func name hFunc f arity fun x heap initial params hHeap hB => ?_
  rw [hBody, hResults]
  refine (Stmt.call_spec hImport hCallee hParams).mono ?_ fun _ _ h => h
  rintro store state ⟨rfl, rfl⟩
  refine ⟨params ++ [.i64 0], func.state params,
    fun final values => final = store ∧ values = [.i64 (f x)], hArgs heap store params x hB,
    fun env => by simpa using hSpec x env store heap params 0 hHeap hB, ?_⟩
  rintro store' out ⟨rfl, rfl⟩
  obtain ⟨next, hNext, hGet⟩ := hSet params (f x) (arity _ _ _ _ hB)
  exact ⟨next, by simpa using hNext, rfl, [.i64 (f x)], next,
    by simp [Expr.evalResults, Expr.eval, hGet], rfl⟩

end Project.IR
