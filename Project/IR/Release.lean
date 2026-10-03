import Project.IR.Stmt
import Project.Pipeline.ReleaseTree
import Project.Pipeline.Rebuilt

/-!
The rule lemmas for releasing a temporary: `release` called on the owned array, or on the
owned value of a recursive type, whose pointer is in local `src`.
-/

namespace Project.IR

open Wasm Project.Pipeline Project.Runtime

variable {m : Module}

/-- Calls `release` on the array in local `src`. -/
def Stmt.release (src : Nat) : Stmt := .call 1 [⟨.u64, .get src⟩] []

/-- Releasing an owned array keeps the state and ends in `heap.releaseStore`;
`Heap.At.release` gives the allocator invariant there. -/
theorem Stmt.release_spec {typeIdx scratch src : Nat} {initial : Store Unit} {before : State}
    {heap : Heap} {ptr : UInt64} {words : Array UInt64} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (releaseFunction typeIdx))
    (hPtr : before.get src = some (.i64 ptr)) (hHeap : heap.At initial)
    (hOwned : heap.Owned initial ptr words) :
    Triple m (.release src) scratch (fun store state => store = initial ∧ state = before)
      (fun store state => store = heap.releaseStore initial ptr ∧ state = before) := by
  refine (Stmt.call_spec (f := releaseFunction typeIdx) (by simp [hImports])
    (by simpa [hImports] using hFunc) rfl).mono ?_ fun _ _ h => h
  rintro store state ⟨hStore, hState⟩
  subst store state
  exact ⟨[.i64 ptr], before, _, by simp [Expr.evalResults, Expr.eval, hPtr],
    fun env => (release_run hImports hFunc env heap initial ptr words hHeap hOwned).returnsOrAborts,
    fun store' out ⟨hOut, hStore'⟩ => ⟨before, by simp [hOut, State.setAll], hStore', rfl⟩⟩

/-- Releasing an owned value of a recursive type keeps the state, and frees its records: the
allocator invariant holds for some heap, the memory caps are unchanged, and every
region of positive size of the old heap apart from the value's blocks keeps its bytes and
stays a region. -/
theorem Stmt.releaseNode_spec {typeIdx scratch src : Nat} {initial : Store Unit}
    {before : State} {heap : Heap} {ptr : UInt64} {n : Node} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (releaseFunction typeIdx))
    (hPtr : before.get src = some (.i64 ptr)) (hHeap : heap.At initial)
    (hOwned : NodeOwned heap initial ptr n)
    (hDisjoint : (n.blocks initial ptr).Pairwise regionsDisjoint) :
    Triple m (.release src) scratch (fun store state => store = initial ∧ state = before)
      (fun store state => state = before ∧ ∃ heap' : Heap, heap'.At store ∧
        store.memoryCaps = initial.memoryCaps ∧
        ∀ r, heap.Region r → 0 < r.2 → (∀ b ∈ n.blocks initial ptr, regionsDisjoint r b) →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → store.mem.bytes a = initial.mem.bytes a) ∧
            heap'.Region r) := by
  refine (Stmt.call_spec (f := releaseFunction typeIdx) (by simp [hImports])
    (by simpa [hImports] using hFunc) rfl).mono ?_ fun _ _ h => h
  rintro store state ⟨hStore, hState⟩
  subst store state
  exact ⟨[.i64 ptr], before, _, by simp [Expr.evalResults, Expr.eval, hPtr],
    fun env => (release_tree_run hImports hFunc env heap initial ptr n hHeap hOwned
      hDisjoint).returnsOrAborts,
    fun store' out ⟨hOut, hRest⟩ => ⟨before, by simp [hOut, State.setAll], rfl, hRest⟩⟩

/-- The release rule for a value of a recursive type, with its postcondition as a rebuild to
the null pointer. -/
theorem Stmt.releaseNode_rebuilt {typeIdx scratch src : Nat} {initial : Store Unit}
    {before : State} {heap : Heap} {ptr : UInt64} {n : Node} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (releaseFunction typeIdx))
    (hPtr : before.get src = some (.i64 ptr)) (hHeap : heap.At initial)
    (hOwned : NodeOwned heap initial ptr n)
    (hDisjoint : (n.blocks initial ptr).Pairwise regionsDisjoint) :
    Triple m (.release src) scratch (fun store state => store = initial ∧ state = before)
      (fun store state => state = before ∧ ∃ heap' : Heap,
        heap.Rebuilt initial (n.blocks initial ptr) heap' store 0 .null) :=
  (Stmt.releaseNode_spec hImports hFunc hPtr hHeap hOwned hDisjoint).mono (fun _ _ h => h)
    fun _ _ ⟨hState, heap', hAt, hCaps, hRegion⟩ =>
      ⟨hState, heap', Heap.Rebuilt.released hAt hCaps hRegion⟩

/-- `Stmt.releaseNode_spec` with its frame as `Heap.Keeps`: the release keeps every region apart
from the released blocks. -/
theorem Stmt.releaseNode_keeps {typeIdx scratch src : Nat} {initial : Store Unit}
    {before : State} {heap : Heap} {ptr : UInt64} {n : Node} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (releaseFunction typeIdx))
    (hPtr : before.get src = some (.i64 ptr)) (hHeap : heap.At initial)
    (hOwned : NodeOwned heap initial ptr n)
    (hDisjoint : (n.blocks initial ptr).Pairwise regionsDisjoint) :
    Triple m (.release src) scratch (fun store state => store = initial ∧ state = before)
      (fun store state => state = before ∧ ∃ heap' : Heap, heap'.At store ∧
        store.memoryCaps = initial.memoryCaps ∧
        heap.Keeps initial (n.blocks initial ptr) heap' store []) :=
  (Stmt.releaseNode_spec hImports hFunc hPtr hHeap hOwned hDisjoint).mono (fun _ _ h => h)
    fun _ _ ⟨hState, heap', hAt, hCaps, hRegion⟩ => ⟨hState, heap', hAt, hCaps,
      fun r hr hpos hApart => ⟨(hRegion r hr hpos hApart).1, (hRegion r hr hpos hApart).2,
        fun _ hb => nomatch hb⟩⟩

end Project.IR
