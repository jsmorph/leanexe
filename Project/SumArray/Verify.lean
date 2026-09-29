import Project.SumArray.Module
import Project.IR.Correct
import Project.Encoding.RoundTrip

namespace Project.SumArray

open Project.Pipeline Project.IR

theorem sumArray_implements :
    Implements sumArray.module 0 LeanExe.Examples.SumArray.sumArray (fun _ => 0) := by
  refine Func.implements sumArray.ir "sumArray" _ (by rintro _ _ _ _ ⟨ptr, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ - ⟨ptr, rfl, hBorrowed⟩
  let start : State := { params := [.i64 ptr], locals := List.replicate 4 (.i64 0) }
  show Triple _ (.seq (.assign 1 (.const 0)) (.fold 0 1 2 3 4 (.bin .add (.get 1) (.get 4)))) 5
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = start) ?_
    ((Stmt.fold_spec (initial := initial) (before := start) (ptr := ptr) (start := 0) (· + ·)
      (by decide) (by decide) (by simp [start]) hBorrowed.values rfl rfl
      fun state a e _ hA hE => ⟨state, by simp [Expr.eval, hA, hE, U64Op.apply]⟩).mono
        (fun _ _ h => h) ?_)
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨0, start, start, rfl, rfl, rfl, rfl⟩
  · rintro store state ⟨hStore, -, hAcc⟩
    exact ⟨hStore, (xs.foldl (· + ·) 0 : UInt64), state, by
      simp [sumArray.ir, Func.scratch, Expr.eval, hAcc], rfl⟩

/-- The bytes `encode` produces for `sumArray.module` decode to a module that
computes `sumArray` exactly. -/
theorem sumArray_bytes (bytes : ByteArray)
    (success : Wasm.Encoding.encode sumArray.module = .ok bytes) :
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      Implements m 0 LeanExe.Examples.SumArray.sumArray (fun _ => 0) :=
  ⟨sumArray.module, Wasm.Encoding.decode_encode sumArray.module bytes (by decide) success,
    sumArray_implements⟩

end Project.SumArray
