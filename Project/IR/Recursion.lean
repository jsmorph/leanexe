import Project.IR.Correct
import Project.Pipeline.Rebuilt

/-!
The rules for a definition that calls itself other than in tail position.  The compiler emits
an internal function with a depth parameter, which traps at `unreachable` at the depth limit
and calls itself with the depth plus one, and an entry function, which calls the internal
function at depth 0.  `Func.recursion` proves the internal function by strong induction on a
measure of the argument, with `Stmt.selfCall_spec` for its calls of itself, and
`Func.entry_implements` gives the entry's `Implements`.  The depth needs no bound in the
proof, since `ReturnsOrAborts` allows a trap at `unreachable`.  A definition that consumes its
tree and returns a tree has the same rules with `Rebuilds` in place of `Keeps`.
-/

namespace Project.IR

open Wasm Project.Pipeline Project.Runtime

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
      (fun final values => final = initial ∧ values.reverse = out) :=
  Func.returns funcs i func name hFunc hLength
    (P := fun final values => final = initial ∧ values = out) (correct.mono (fun _ _ h => h) fun _ _ ⟨hStore, next, hEval⟩ => ⟨out, next, hEval, hStore, rfl⟩)
    env

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

/-- The specification of an internal function that consumes the moved part of its argument:
under the premises of `Implements` and for any depth word, a call aborts or returns one
pointer to the result's records, rebuilt from the consumed blocks. -/
def Rebuilds [Represent α] [Encode β] (m : Module) (idx : Nat) (f : α → β) (x : α) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (vs : List Value) (d : UInt64),
    heap.At store → Represent.borrowed heap store vs x →
    Separate store (Represent.moves store vs x) (Represent.reads vs x) →
    store.memoryCap m 0 ≤ 65535 →
    ReturnsOrAborts env m idx store (.i64 d :: vs.reverse)
      (fun final values => ∃ (heap' : Heap) (q : UInt64), values = [.i64 q] ∧
        heap.Rebuilt store ((Represent.moves store vs x).map (block store)) heap' final q
          (Encode.encode (f x)))

/-- The recursion rule for an internal function that consumes its argument. -/
theorem Func.rebuildRecursion [Represent α] [Encode β] (funcs : List (Func × String)) (i : Nat)
    (func : Func) (name : String) (hFunc : funcs[i]? = some (func, name)) (f : α → β)
    (measure : α → Nat)
    (arity : ∀ heap store vs (x : α), Represent.borrowed heap store vs x →
      vs.length + 1 = func.params.length)
    (hBody : ∀ x, (∀ y, measure y < measure x → Rebuilds (compile funcs) (2 + i) f y) →
      ∀ heap initial vs (d : UInt64), heap.At initial → Represent.borrowed heap initial vs x →
      Separate initial (Represent.moves initial vs x) (Represent.reads vs x) →
      initial.memoryCap (compile funcs) 0 ≤ 65535 →
      Triple (compile funcs) func.body func.scratch
        (fun store state => store = initial ∧ state = func.state (vs ++ [.i64 d]))
        (fun store state => ∃ (heap' : Heap) (q : UInt64) (next : State),
          Expr.evalResults store.mem func.scratch func.results state = some ([.i64 q], next) ∧
          heap.Rebuilt initial ((Represent.moves initial vs x).map (block initial)) heap' store q
            (Encode.encode (f x)))) :
    ∀ x, Rebuilds (compile funcs) (2 + i) f x := by
  intro x
  induction h : measure x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro env store heap vs d hHeap hArgs hSeparate hCap
    have hRun := Func.returns funcs i func name hFunc (params := vs ++ [.i64 d])
      (P := fun final values => ∃ (heap' : Heap) (q : UInt64), values = [.i64 q] ∧
        heap.Rebuilt store ((Represent.moves store vs x).map (block store)) heap' final q
          (Encode.encode (f x)))
      (by simp [arity _ _ _ _ hArgs])
      ((hBody x (fun y hy => ih _ (h ▸ hy) y rfl) heap store vs d hHeap hArgs hSeparate
        hCap).mono (fun _ _ h => h)
        fun _ _ ⟨heap', q, next, hEval, hR⟩ => ⟨[.i64 q], next, hEval, heap', q, rfl, hR⟩) env
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append] at hRun
    refine hRun.mono fun st vs' ⟨heap', q, hVs, hR⟩ => ⟨heap', q, ?_, hR⟩
    rw [← List.reverse_reverse vs', hVs]
    rfl

/-- A call of the internal function inside its own body, on a smaller argument. -/
theorem Stmt.selfCall_rebuilds [Represent α] [Encode β] {m : Module} {idx : Nat} {f : α → β}
    {g : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some g)
    {scratch : Nat} {args : List ((type : ScalarType) × Expr type)} {result : Nat}
    (hParams : args.length = g.numParams) {initial : Store Unit} {before afterArgs : State}
    {next : UInt64 → State} {heap : Heap} {y : α} {vs : List Value} {d : UInt64}
    (hSpec : Rebuilds m idx f y) (hHeap : heap.At initial)
    (hB : Represent.borrowed heap initial vs y)
    (hSeparate : Separate initial (Represent.moves initial vs y) (Represent.reads vs y))
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hArgs : Expr.evalResults initial.mem scratch args before = some (vs ++ [.i64 d], afterArgs))
    (hSet : ∀ q, afterArgs.setAll [result] [.i64 q] = some (next q)) :
    Triple m (.call idx args [result]) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ (heap' : Heap) (q : UInt64), state = next q ∧
        heap.Rebuilt initial ((Represent.moves initial vs y).map (block initial)) heap' store q
          (Encode.encode (f y))) := by
  refine (Stmt.call_spec hImport hFunc hParams).mono ?_ fun _ _ h => h
  rintro store state ⟨rfl, rfl⟩
  refine ⟨vs ++ [.i64 d], afterArgs, fun final values => ∃ (heap' : Heap) (q : UInt64),
    values = [.i64 q] ∧ heap.Rebuilt store ((Represent.moves store vs y).map (block store)) heap'
      final q (Encode.encode (f y)), hArgs, fun env => ?_, ?_⟩
  · simpa using hSpec env store heap vs d hHeap hB hSeparate hCap
  · rintro store' out ⟨heap', q, rfl, hR⟩
    exact ⟨next q, by simpa using hSet q, heap', q, rfl, hR⟩

/-- A function whose body leaves one pointer to a value rebuilt from the consumed blocks
implements `f`. -/
theorem Func.implements_rebuilt [Represent α] [Encode β] (funcs : List (Func × String)) (i : Nat)
    (func : Func) (name : String) (hFunc : funcs[i]? = some (func, name)) (f : α → β)
    (arity : ∀ heap store params (x : α), Represent.borrowed heap store params x →
      params.length = func.params.length)
    (correct : ∀ (x : α) (heap : Heap) (initial : Store Unit) (params : List Value),
      heap.At initial → Represent.borrowed heap initial params x →
      Separate initial (Represent.moves initial params x) (Represent.reads params x) →
      initial.memoryCap (compile funcs) 0 ≤ 65535 →
      Triple (compile funcs) func.body func.scratch
        (fun store state => store = initial ∧ state = func.state params)
        (fun store state => ∃ (heap' : Heap) (q : UInt64) (next : State),
          Expr.evalResults store.mem func.scratch func.results state = some ([.i64 q], next) ∧
          heap.Rebuilt initial ((Represent.moves initial params x).map (block initial)) heap'
            store q (Encode.encode (f x)))) :
    Implements (compile funcs) (2 + i) f :=
  Func.implements_moves funcs i func name hFunc f arity
    fun x heap initial params hHeap hB hSeparate hCap =>
      (correct x heap initial params hHeap hB hSeparate hCap).mono (fun _ _ h => h)
        fun _ _ ⟨heap', q, next, hEval, hR⟩ => by
          have hApart : ∀ r, Apart initial (Represent.moves initial params x) r →
              ∀ b ∈ (Represent.moves initial params x).map (block initial),
                regionsDisjoint r b := by
            intro r hr b hb
            obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hb
            exact hr q' hq'
          exact ⟨heap', hR.at_, hR.caps, fun p ws hp ha => (hR.keepBorrowed hp (hApart _ ha)).1,
            fun p ws hp ha => (hR.keepOwned hp (hApart _ ha)).1, [.i64 q], next, hEval,
            ⟨q, rfl, hR.owned, hR.disjoint⟩,
            fun p ws hp ha => (hR.keepBorrowed hp (hApart _ ha)).2,
            fun p ws hp ha => (hR.keepOwned hp (hApart _ ha)).2⟩

/-- The entry of a consumed recursion: one call of the internal function at depth 0. -/
theorem Func.entry_rebuilds [Represent α] [Encode β] (funcs : List (Func × String)) (i : Nat)
    (func : Func) (name : String) (hFunc : funcs[i]? = some (func, name)) (f : α → β)
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
    (hSpec : ∀ x, Rebuilds (compile funcs) index f x) :
    Implements (compile funcs) (2 + i) f := by
  refine Func.implements_rebuilt funcs i func name hFunc f arity
    fun x heap initial params hHeap hB hSeparate hCap => ?_
  rw [hBody, hResults]
  refine (Stmt.call_spec hImport hCallee hParams).mono ?_ fun _ _ h => h
  rintro store state ⟨rfl, rfl⟩
  refine ⟨params ++ [.i64 0], func.state params, fun final values =>
    ∃ (heap' : Heap) (q : UInt64), values = [.i64 q] ∧
      heap.Rebuilt store ((Represent.moves store params x).map (block store)) heap' final q
        (Encode.encode (f x)),
    hArgs heap store params x hB,
    fun env => by simpa using hSpec x env store heap params 0 hHeap hB hSeparate hCap, ?_⟩
  rintro store' out ⟨heap', q, rfl, hR⟩
  obtain ⟨next, hNext, hGet⟩ := hSet params q (arity _ _ _ _ hB)
  exact ⟨next, by simpa using hNext, heap', q, next, by simp [Expr.evalResults, Expr.eval, hGet],
    hR⟩

end Project.IR
