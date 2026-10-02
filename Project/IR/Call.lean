import Project.IR.Stmt
import Project.Pipeline.Implements

/-!
The rule for calls between compiled functions.  A call reuses the callee's
`Implements` theorem: the caller supplies arguments that represent the callee's
input, and receives results that represent the callee's value, with every array
it held kept, or the call aborts.
-/

namespace Project.IR

open Wasm Project.Pipeline

variable {m : Module}

/-- A call of entry `idx`, which implements `g`, from arguments that evaluate to
words representing `x`, leaves in the locals `results` values that represent
`g x` as owned.  The heap facts are those of `Implements`, and `hSet` says the
result locals can hold any represented result. -/
theorem Stmt.callImplements_spec [Represent α] [Represent β] {idx : Nat} {g : α → β}
    (hImpl : Implements m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch : Nat} {args : List ((type : ScalarType) × Expr type)} {results : List Nat}
    (hParams : args.length = f.numParams) {initial : Store Unit} {before afterArgs : State}
    {heap : Heap} {x : α} {vals : List Value}
    (hArgs : Expr.evalResults initial.mem scratch args before = some (vals, afterArgs))
    (hHeap : heap.At initial) (hBorrowed : Represent.borrowed heap initial vals x)
    (hSeparate : Separate initial (Represent.moves vals x) (Represent.reads vals x))
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hSet : ∀ heap' store values, Represent.owned heap' store values (g x) →
      ∃ next, afterArgs.setAll results.reverse values.reverse = some next) :
    Triple m (.call idx args results) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ (heap' : Heap) (values : List Value), heap'.At store ∧
        Represent.owned heap' store values (g x) ∧
        store.memoryCaps = initial.memoryCaps ∧
        (∀ p ws, heap.Borrowed initial p ws →
          Apart initial (Represent.moves vals x) (p.toNat, 8 * (ws.size + 1)) →
          heap'.Borrowed store p ws) ∧
        (∀ p ws, heap.Owned initial p ws → Apart initial (Represent.moves vals x) (block initial p) →
          heap'.Owned store p ws ∧ capacityAt store p = capacityAt initial p) ∧
        (∀ p ws, heap.Borrowed initial p ws →
          Apart initial (Represent.moves vals x) (p.toNat, 8 * (ws.size + 1)) →
          Represent.outside store values (g x) (p.toNat, 8 * (ws.size + 1))) ∧
        (∀ p ws, heap.Owned initial p ws → Apart initial (Represent.moves vals x) (block initial p) →
          Represent.outside store values (g x) (block initial p)) ∧
        afterArgs.setAll results.reverse values.reverse = some state) := by
  refine (Stmt.call_spec hImport hFunc hParams).mono ?_ fun _ _ h => h
  rintro store state ⟨hStore, hState⟩
  subst store state
  refine ⟨vals, afterArgs, fun final values => ∃ heap' : Heap, heap'.At final ∧
      Represent.owned heap' final values.reverse (g x) ∧
      final.memoryCaps = initial.memoryCaps ∧
      (∀ p ws, heap.Borrowed initial p ws →
        Apart initial (Represent.moves vals x) (p.toNat, 8 * (ws.size + 1)) →
        heap'.Borrowed final p ws) ∧
      (∀ p ws, heap.Owned initial p ws → Apart initial (Represent.moves vals x) (block initial p) →
        heap'.Owned final p ws ∧ capacityAt final p = capacityAt initial p) ∧
      (∀ p ws, heap.Borrowed initial p ws →
        Apart initial (Represent.moves vals x) (p.toNat, 8 * (ws.size + 1)) →
        Represent.outside final values.reverse (g x) (p.toNat, 8 * (ws.size + 1))) ∧
      (∀ p ws, heap.Owned initial p ws → Apart initial (Represent.moves vals x) (block initial p) →
        Represent.outside final values.reverse (g x) (block initial p)),
    hArgs, fun env => ?_, ?_⟩
  · exact hImpl env initial heap vals x hHeap hBorrowed hSeparate hCap
  · rintro store' out ⟨heap', hAt', hOwned', hCaps, hKeepBorrowed, hKeepOwned, hOutsideB,
      hOutsideO⟩
    obtain ⟨next, hNext⟩ := hSet heap' store' out.reverse hOwned'
    rw [List.reverse_reverse] at hNext
    exact ⟨next, hNext, heap', out.reverse, hAt', hOwned', hCaps, hKeepBorrowed, hKeepOwned,
      hOutsideB, hOutsideO, by rw [List.reverse_reverse]; exact hNext⟩

/-- A call of entry `idx`, which computes `g` on scalars and keeps the store, from
arguments that evaluate to the values of `x`, keeps the store and leaves the values
of `g x` in the locals `results`. -/
theorem Stmt.callPure_spec [Scalar α] [Scalar β] {idx : Nat} {g : α → β}
    (hImpl : ImplementsPure m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch : Nat} {args : List ((type : ScalarType) × Expr type)} {results : List Nat}
    (hParams : args.length = f.numParams) {initial : Store Unit}
    {before afterArgs next : State} {x : α}
    (hArgs : Expr.evalResults initial.mem scratch args before = some (Scalar.values x, afterArgs))
    (hSet : afterArgs.setAll results.reverse (Scalar.values (g x)).reverse = some next) :
    Triple m (.call idx args results) scratch
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

end Project.IR
