import LeanExe.IR.Stmt
import LeanExe.Pipeline.Implements

/-!
The rule for calls between compiled functions.  A call reuses the callee's
`Implements` theorem: the caller supplies arguments that represent the callee's
input, and receives results that represent the callee's value, with every array
it held kept, or the call aborts.
-/

namespace LeanExe.IR

open Wasm LeanExe.Pipeline

variable {m : Module} {a : Bool}

/-- A call of entry `idx`, which implements `g`, from arguments that evaluate to
words representing `x`, leaves in the locals `results` values that represent
`g x` as owned, and the heap condition `Post` holds.  The heap facts are those of `Implements`, with its region clause as
`Heap.Keeps`, and `hSet` says the result locals can hold any represented result. -/
theorem Stmt.callImplementsA_spec [Represent α] [Represent β] {idx : Nat} {g : α → β}
    {Pre : α → Heap → Store Unit → Prop} {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (hImpl : ImplementsA a m idx g Pre Post) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch : Nat} {args : List ((type : ScalarType) × Expr type)} {results : List Nat}
    (hParams : args.length = f.numParams) {initial : Store Unit} {before afterArgs : State}
    {heap : Heap} {x : α} {vals : List Value}
    (hArgs : Expr.evalResults initial.mem scratch args before = some (vals, afterArgs))
    (hHeap : heap.At initial) (hPre : Pre x heap initial)
    (hBorrowed : Represent.borrowed heap initial vals x)
    (hSeparate : Separate initial (Represent.moves initial vals x) (Represent.reads initial vals x))
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hSet : ∀ heap' store values, Represent.owned heap' store values (g x) →
      ∃ next, afterArgs.setAll results.reverse values.reverse = some next) :
    TripleA a m (.call idx args results) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ (heap' : Heap) (values : List Value), heap'.At store ∧
        Represent.owned heap' store values (g x) ∧
        store.memoryCaps = initial.memoryCaps ∧
        heap.Keeps initial ((Represent.moves initial vals x).map (block initial)) heap' store
          (Represent.blocks store values (g x)) ∧
        afterArgs.setAll results.reverse values.reverse = some state ∧
        Post x heap initial heap' store) := by
  refine (Stmt.call_spec hImport hFunc hParams).mono ?_ fun _ _ h => h
  rintro store state ⟨hStore, hState⟩
  subst store state
  refine ⟨vals, afterArgs, fun final values => ∃ heap' : Heap, heap'.At final ∧
      Represent.owned heap' final values.reverse (g x) ∧
      final.memoryCaps = initial.memoryCaps ∧
      (∀ r, heap.Region r → 0 < r.2 → Apart initial (Represent.moves initial vals x) r →
        (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = initial.mem.bytes a) ∧
          heap'.Region r ∧ Represent.outside final values.reverse (g x) r) ∧
      Post x heap initial heap' final,
    hArgs, fun env => ?_, ?_⟩
  · exact hImpl env initial heap vals x hHeap hPre hBorrowed hSeparate hCap
  · rintro store' out ⟨heap', hAt', hOwned', hCaps, hRegion, hPost⟩
    obtain ⟨next, hNext⟩ := hSet heap' store' out.reverse hOwned'
    rw [List.reverse_reverse] at hNext
    exact ⟨next, hNext, heap', out.reverse, hAt', hOwned', hCaps,
      Heap.Keeps.implements.mpr hRegion, by rw [List.reverse_reverse]; exact hNext, hPost⟩


/-- A call of entry `idx`, which implements `g`, from arguments that evaluate to
words representing `x`, leaves in the locals `results` values that represent
`g x` as owned.  The heap facts are those of `Implements`, with its region clause as
`Heap.Keeps`, and `hSet` says the result locals can hold any represented result. -/
theorem Stmt.callImplements_spec [Represent α] [Represent β] {idx : Nat} {g : α → β}
    (hImpl : Implements m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch : Nat} {args : List ((type : ScalarType) × Expr type)} {results : List Nat}
    (hParams : args.length = f.numParams) {initial : Store Unit} {before afterArgs : State}
    {heap : Heap} {x : α} {vals : List Value}
    (hArgs : Expr.evalResults initial.mem scratch args before = some (vals, afterArgs))
    (hHeap : heap.At initial) (hBorrowed : Represent.borrowed heap initial vals x)
    (hSeparate : Separate initial (Represent.moves initial vals x) (Represent.reads initial vals x))
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hSet : ∀ heap' store values, Represent.owned heap' store values (g x) →
      ∃ next, afterArgs.setAll results.reverse values.reverse = some next) :
    Triple m (.call idx args results) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ (heap' : Heap) (values : List Value), heap'.At store ∧
        Represent.owned heap' store values (g x) ∧
        store.memoryCaps = initial.memoryCaps ∧
        heap.Keeps initial ((Represent.moves initial vals x).map (block initial)) heap' store
          (Represent.blocks store values (g x)) ∧
        afterArgs.setAll results.reverse values.reverse = some state) := by
  refine (Stmt.callImplementsA_spec (a := true) hImpl.toA hImport hFunc hParams hArgs hHeap trivial
    hBorrowed hSeparate hCap hSet).mono (fun _ _ h => h) ?_
  rintro store state ⟨heap', values, hAt, hOwned, hCaps, hKeeps, hState, -⟩
  exact ⟨heap', values, hAt, hOwned, hCaps, hKeeps, hState⟩

/-- A call of entry `idx`, which computes `g` on scalars and keeps the store, from
arguments that evaluate to the values of `x`, keeps the store and leaves the values
of `g x` in the locals `results`. -/
theorem Stmt.callPure_spec [Scalar α] [Scalar β] {idx : Nat} {g : α → β}
    (hImpl : ImplementsPureA a m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch : Nat} {args : List ((type : ScalarType) × Expr type)} {results : List Nat}
    (hParams : args.length = f.numParams) {initial : Store Unit}
    {before afterArgs next : State} {x : α}
    (hArgs : Expr.evalResults initial.mem scratch args before = some (Scalar.values x, afterArgs))
    (hSet : afterArgs.setAll results.reverse (Scalar.values (g x)).reverse = some next) :
    TripleA a m (.call idx args results) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => store = initial ∧ state = next) := by
  refine (Stmt.call_spec hImport hFunc hParams).mono ?_ fun _ _ h => h
  rintro store state ⟨hStore, hState⟩
  subst store state
  refine ⟨Scalar.values x, afterArgs,
    fun final values => final = initial ∧ values.reverse = Scalar.values (g x), hArgs,
    fun env => hImpl env initial x, ?_⟩
  rintro store' out ⟨rfl, hOut⟩
  refine ⟨next, ?_, rfl, rfl⟩
  rw [show out = (Scalar.values (g x)).reverse by rw [← hOut, List.reverse_reverse]]
  exact hSet

/-- `Stmt.callPure_spec` followed by `rest` from the state the call leaves. -/
theorem Stmt.seq_callPure [Scalar α] [Scalar β] {idx : Nat} {g : α → β}
    (hImpl : ImplementsPureA a m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch : Nat} {args : List ((type : ScalarType) × Expr type)} {results : List Nat}
    (hParams : args.length = f.numParams) {initial : Store Unit} {before : State}
    {x : α} {rest : Stmt} {Q : Store Unit → State → Prop}
    (h : ∃ afterArgs,
      Expr.evalResults initial.mem scratch args before = some (Scalar.values x, afterArgs) ∧
      ∃ next, afterArgs.setAll results.reverse (Scalar.values (g x)).reverse = some next ∧
        TripleA a m rest scratch (fun store state => store = initial ∧ state = next) Q) :
    TripleA a m (.seq (.call idx args results) rest) scratch
      (fun store state => store = initial ∧ state = before) Q :=
  let ⟨_, hArgs, _, hSet, hNext⟩ := h
  Stmt.seq_spec (Stmt.callPure_spec hImpl hImport hFunc hParams hArgs hSet) hNext

/-- `Stmt.callPure_spec` as the last statement: the postcondition holds of the state the call
leaves. -/
theorem Stmt.callPure_last [Scalar α] [Scalar β] {idx : Nat} {g : α → β}
    (hImpl : ImplementsPureA a m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch : Nat} {args : List ((type : ScalarType) × Expr type)} {results : List Nat}
    (hParams : args.length = f.numParams) {initial : Store Unit} {before : State}
    {x : α} {Q : Store Unit → State → Prop}
    (h : ∃ afterArgs,
      Expr.evalResults initial.mem scratch args before = some (Scalar.values x, afterArgs) ∧
      ∃ next, afterArgs.setAll results.reverse (Scalar.values (g x)).reverse = some next ∧
        Q initial next) :
    TripleA a m (.call idx args results) scratch
      (fun store state => store = initial ∧ state = before) Q :=
  let ⟨_, hArgs, _, hSet, hQ⟩ := h
  (Stmt.callPure_spec hImpl hImport hFunc hParams hArgs hSet).mono (fun _ _ h => h)
    fun _ _ ⟨hs, hst⟩ => hs ▸ hst ▸ hQ

end LeanExe.IR
