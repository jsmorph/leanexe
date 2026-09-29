import Project.IR.Stmt
import Project.Pipeline.RuntimeSpec

/-!
The rule lemma for releasing a temporary: `release` called on the owned array
whose pointer is in local `src`.
-/

namespace Project.IR

open Wasm Project.Pipeline Project.Runtime

variable {m : Module}

/-- Calls `release` on the array in local `src`. -/
def Stmt.release (src : Nat) : Stmt := .call 2 [.get src] none

/-- Releasing an owned array keeps the state and ends in `heap.releaseStore`;
`Heap.At.release` gives the allocator invariant there. -/
theorem Stmt.release_spec {typeIdx scratch src : Nat} {initial : Store Unit} {before : State}
    {heap : Heap} {ptr : UInt64} {words : Array UInt64} (hImports : m.imports = [])
    (hFunc : m.funcs[2]? = some (releaseFunction typeIdx))
    (hPtr : before.get src = some (.i64 ptr)) (hHeap : heap.At initial)
    (hOwned : heap.Owned initial ptr words) :
    Triple m (.release src) scratch (fun store state => store = initial ∧ state = before)
      (fun store state => store = heap.releaseStore initial ptr ∧ state = before) := by
  refine (Stmt.call_spec (f := releaseFunction typeIdx) (by simp [hImports])
    (by simpa [hImports] using hFunc) rfl).mono ?_ fun _ _ h => h
  rintro store state ⟨hStore, hState⟩
  subst store state
  exact ⟨[ptr], before, _, by simp [Expr.evalAll, Expr.eval, hPtr],
    fun env => release_run hImports hFunc env heap initial ptr words hHeap hOwned,
    fun store' out ⟨hOut, hStore'⟩ => ⟨hOut, hStore', rfl⟩⟩

end Project.IR
