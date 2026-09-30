import Project.IR.Stmt
import Project.Pipeline.Implements

/-!
The rule for calls between compiled functions.  A call reuses the callee's
`Implements` theorem: the caller supplies arguments that represent the callee's
input in a heap with room for its allocation, and receives results that
represent the callee's value, with every array it held kept.
-/

namespace Project.IR

open Wasm Project.Pipeline

variable {m : Module}

/-- A call of entry `idx`, which implements `g`, from arguments that evaluate to
words representing `x`, leaves in the locals `results` values that represent
`g x` as owned.  The heap facts are those of `Implements`, and `hSet` says the
result locals can hold any represented result. -/
theorem Stmt.callImplements_spec [Represent α] [Represent β] {idx : Nat} {g : α → β}
    {need : α → Nat} (hImpl : Implements m idx g need) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch : Nat} {args : List (Expr .u64)} {results : List Nat}
    (hParams : args.length = f.numParams) {initial : Store Unit} {before afterArgs : State}
    {heap : Heap} {x : α} {words : List UInt64}
    (hArgs : Expr.evalAll initial.mem scratch args before = some (words, afterArgs))
    (hHeap : heap.At initial) (hBorrowed : Represent.borrowed heap initial (words.map .i64) x)
    (hRoom : heap.Room initial m (need x))
    (hSet : ∀ heap' store values, Represent.owned heap' store values (g x) →
      ∃ next, afterArgs.setAll results.reverse values.reverse = some next) :
    Triple m (.call idx args results) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ (heap' : Heap) (values : List Value), heap'.At store ∧
        Represent.owned heap' store values (g x) ∧
        Represent.borrowed heap' store (words.map .i64) x ∧
        heap'.top.toNat ≤ heap.top.toNat + need x ∧
        store.mem.pages ≤ max initial.mem.pages ((heap.top.toNat + need x + 65535) / 65536) ∧
        store.memoryCaps = initial.memoryCaps ∧
        (∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed store p ws) ∧
        (∀ p ws, heap.Owned initial p ws → heap'.Owned store p ws) ∧
        afterArgs.setAll results.reverse values.reverse = some state) := by
  refine (Stmt.call_spec hImport hFunc hParams).mono ?_ fun _ _ h => h
  rintro store state ⟨hStore, hState⟩
  subst store state
  refine ⟨words, afterArgs, fun final values => ∃ heap' : Heap, heap'.At final ∧
      Represent.owned heap' final values.reverse (g x) ∧
      Represent.borrowed heap' final (words.map .i64) x ∧ heap'.top.toNat ≤ heap.top.toNat + need x ∧
      final.mem.pages ≤ max initial.mem.pages ((heap.top.toNat + need x + 65535) / 65536) ∧
      final.memoryCaps = initial.memoryCaps ∧
      (∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed final p ws) ∧
      (∀ p ws, heap.Owned initial p ws → heap'.Owned final p ws), hArgs, fun env => ?_, ?_⟩
  · have hRun := hImpl env initial heap (words.map .i64) x hHeap hBorrowed hRoom
    rw [List.map_reverse]
    exact hRun
  · rintro store' out ⟨heap', hAt', hOwned', hBorrowed', hTop, hPages, hCaps, hKeepBorrowed,
      hKeepOwned⟩
    obtain ⟨next, hNext⟩ := hSet heap' store' out.reverse hOwned'
    rw [List.reverse_reverse] at hNext
    exact ⟨next, hNext, heap', out.reverse, hAt', hOwned', hBorrowed', hTop, hPages, hCaps,
      hKeepBorrowed, hKeepOwned, by rw [List.reverse_reverse]; exact hNext⟩

end Project.IR
