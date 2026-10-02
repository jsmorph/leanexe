import Project.Lists.Module
import Project.IR.Correct
import Project.IR.ListFold
import Project.Encoding.RoundTrip

/-! The list module's compiled functions compute their Lean definitions exactly. -/

namespace Project.Lists

open Project.Pipeline Project.IR

theorem listSum_implements :
    Implements lists.module 2 LeanExe.Examples.Lists.listSum := by
  refine Func.implements lists.funcs 0 lists.listSum.ir "listSum" rfl _
    (by rintro _ _ _ _ ⟨ptr, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ hHeap ⟨ptr, rfl, hBorrowed⟩
  let start : State := { params := [.i64 ptr], locals := List.replicate 3 (.i64 0) }
  show Triple _ (.seq (.assign 1 (.const 0)) (.listFold 0 1 2 3 (.bin .add (.get 1) (.get 3)))) 4
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = start) ?_
    ((Stmt.listFold_spec (initial := initial) (before := start) (ptr := ptr) (start := 0) (· + ·)
      (by decide) (by decide) (by simp [start]) (NodeBorrowed.listAt hHeap hBorrowed) rfl rfl
      fun state a e _ hA hE => ⟨state, by simp [Expr.eval, hA, hE, U64Op.apply]⟩).mono
        (fun _ _ h => h) ?_)
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨0, start, start, rfl, rfl, rfl, rfl⟩
  · rintro store state ⟨hStore, -, hAcc⟩
    exact ⟨hStore, [.i64 (xs.foldl (· + ·) 0)], state, by
      simp [lists.listSum.ir, Func.scratch, Expr.evalResults, Expr.eval, hAcc], rfl⟩

/-- `encode` succeeds on `lists.module`, and its bytes decode to a module that computes
`listSum` exactly. -/
theorem lists_bytes : ∃ bytes, Wasm.Encoding.encode lists.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      Implements m 2 LeanExe.Examples.Lists.listSum := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip lists.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, lists.module, decoded, listSum_implements⟩

#print axioms lists_bytes

end Project.Lists
